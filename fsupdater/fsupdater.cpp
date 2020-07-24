/*
 * Copyright (C) 2009 The Android Open Source Project
 * Copyright (C) 2020 The Android Open Kang Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "fsupdater/fsupdater.h"

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <ftw.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/capability.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <time.h>
#include <unistd.h>
#include <utime.h>
#include <dirent.h>
#include <libgen.h>

#include <memory>
#include <string>
#include <vector>

#include <android-base/file.h>
#include <android-base/logging.h>
#include <android-base/parsedouble.h>
#include <android-base/parseint.h>
#include <android-base/properties.h>
#include <android-base/stringprintf.h>
#include <android-base/strings.h>
#include <android-base/unique_fd.h>
#include <applypatch/applypatch.h>
#include <openssl/sha.h>
#include <selinux/label.h>
#include <selinux/selinux.h>
#include <ziparchive/zip_archive.h>

#include "edify/expr.h"
#include "otautil/dirutil.h"
#include "otautil/error_code.h"
#include "otautil/print_sha1.h"

// Send over the buffer to recovery though the command pipe.
static void uiPrint(State* state, const std::string& buffer) {
  FsUpdaterInfo* ui = static_cast<FsUpdaterInfo*>(state->cookie);

  // "line1\nline2\n" will be split into 3 tokens: "line1", "line2" and "".
  // So skip sending empty strings to UI.
  std::vector<std::string> lines = android::base::Split(buffer, "\n");
  for (auto& line : lines) {
    if (!line.empty()) {
      if (ui->cmd_pipe) {
        fprintf(ui->cmd_pipe, "ui_print %s\n", line.c_str());
      }
      else {
        LOG(INFO) << "fsupdater: " << line;
      }
    }
  }

  // On the updater side, we need to dump the contents to stderr (which has
  // been redirected to the log file). Because the recovery will only print
  // the contents to screen when processing pipe command ui_print.
  LOG(INFO) << buffer;
}

static void uiPrintf(State* _Nonnull state, const char* _Nonnull format, ...) {
  std::string error_msg;

  va_list ap;
  va_start(ap, format);
  android::base::StringAppendV(&error_msg, format, ap);
  va_end(ap);

  uiPrint(state, error_msg);
}

struct perm_parsed_args {
  uid_t uid;
  gid_t gid;
  mode_t mode;
  bool has_selabel;
  const char* selabel;
  bool has_capabilities;
  uint64_t capabilities;
};

static bool ParsePermArgs(const std::vector<std::string>& args, size_t argidx,
                          struct perm_parsed_args* parsed) {
  memset(parsed, 0, sizeof(*parsed));

  if ((args.size() - argidx) % 2 != 1) {
    return false;
  }
  int64_t i64;
  int32_t i32;
  if (sscanf(args[argidx + 0].c_str(), "%" SCNd64, &i64) != 1) {
    return false;
  }
  parsed->uid = i64;
  if (sscanf(args[argidx + 1].c_str(), "%" SCNd64, &i64) != 1) {
    return false;
  }
  parsed->gid = i64;
  if (sscanf(args[argidx + 2].c_str(), "%" SCNi32, &i32) != 1) {
    return false;
  }
  parsed->mode = i32;
  for (size_t i = argidx + 3; i < args.size(); ++i) {
    if (args[i] == "capabilities") {
      if (sscanf(args[i + 1].c_str(), "%" SCNi64, &parsed->capabilities) != 1) {
        return false;
      }
      parsed->has_capabilities = true;
      continue;
    }
    if (args[i] == "selabel") {
      if (args[i + 1].empty()) {
        return false;
      }
      parsed->selabel = args[i + 1].c_str();
      parsed->has_selabel = true;
      continue;
    }
  }
  return true;
}

static int ApplyParsedPerms(State* state, const char* filename, const struct stat* statptr,
                            struct perm_parsed_args parsed) {
  int bad = 0;

  if (parsed.has_selabel) {
    if (lsetfilecon(filename, parsed.selabel) != 0) {
      uiPrintf(state, "ApplyParsedPerms: lsetfilecon of %s to %s failed: %s\n", filename,
               parsed.selabel, strerror(errno));
      bad++;
    }
  }

  /* ignore symlinks */
  if (S_ISLNK(statptr->st_mode)) {
    return bad;
  }

  if (lchown(filename, parsed.uid, parsed.gid) < 0) {
    uiPrintf(state, "ApplyParsedPerms: chown of %s to %d.%d failed: %s\n", filename,
             parsed.uid, parsed.gid, strerror(errno));
    bad++;
  }

  if (chmod(filename, parsed.mode) < 0) {
    uiPrintf(state, "ApplyParsedPerms: chmod of %s to %d failed: %s\n", filename, parsed.mode,
             strerror(errno));
    bad++;
  }

  if (parsed.has_capabilities && S_ISREG(statptr->st_mode)) {
    if (parsed.capabilities == 0) {
      if ((removexattr(filename, XATTR_NAME_CAPS) != 0) && (errno != ENODATA)) {
        // Report failure unless it's ENODATA (attribute not set)
        uiPrintf(state, "ApplyParsedPerms: removexattr of %s to %" PRIx64 " failed: %s\n", filename,
                 parsed.capabilities, strerror(errno));
        bad++;
      }
    } else {
      struct vfs_cap_data cap_data;
      memset(&cap_data, 0, sizeof(cap_data));
      cap_data.magic_etc = VFS_CAP_REVISION_2 | VFS_CAP_FLAGS_EFFECTIVE;
      cap_data.data[0].permitted = (uint32_t)(parsed.capabilities & 0xffffffff);
      cap_data.data[0].inheritable = 0;
      cap_data.data[1].permitted = (uint32_t)(parsed.capabilities >> 32);
      cap_data.data[1].inheritable = 0;
      if (setxattr(filename, XATTR_NAME_CAPS, &cap_data, sizeof(cap_data), 0) < 0) {
        uiPrintf(state, "ApplyParsedPerms: setcap of %s to %" PRIx64 " failed: %s\n", filename,
                 parsed.capabilities, strerror(errno));
        bad++;
      }
    }
  }

  return bad;
}

// mkdir(path, uid, gid, mode, ...)
//   Create a directory.
//   Returns nothing.
static Value* MkdirFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() < 4) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects at least 4 arguments, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];

  struct perm_parsed_args parsed;
  if (!ParsePermArgs(args, 1, &parsed)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  int bad = 0;

  if (mkdir(path.c_str(), parsed.mode) != 0) {
    if (errno != EEXIST) {
      return ErrorAbort(state, kFileOpenFailure, "%s: Error on mkdir of \"%s\": %s", name,
                        path.c_str(), strerror(errno));
    }
  }

  struct stat st;
  if (stat(path.c_str(), &st) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s: Error on stat of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }

  bad += ApplyParsedPerms(state, path.c_str(), &st, parsed);

  if (bad > 0) {
    return ErrorAbort(state, kSetMetadataFailure, "%s: some changes failed", name);
  }

  return StringValue("");
}

// rmdir(path)
//   Delete a directory.
//   Returns nothing.
static Value* RmdirFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() != 1) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects 1 argument, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];

  if (rmdir(path.c_str()) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s: Error on rmdir of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }

  return StringValue("");
}

// create(path, zipfile, uid, gid, mode, ...)
//   Create a file.
//   Returns nothing.
static Value* CreateFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() < 5) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects at least 5 arguments, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];
  const auto& zipfile = args[1];

  struct perm_parsed_args parsed;
  if (!ParsePermArgs(args, 2, &parsed)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  int bad = 0;

  ZipArchiveHandle za = static_cast<FsUpdaterInfo*>(state->cookie)->package_zip;
  ZipString zip_string_path(zipfile.c_str());
  ZipEntry entry;
  if (FindEntry(za, zip_string_path, &entry) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() No %s in package", name, zipfile.c_str());
  }

  struct stat st;
  if (lstat(path.c_str(), F_OK) == 0) {
    return StringValue("");
  }

  android::base::unique_fd fd(TEMP_FAILURE_RETRY(
      open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR)));
  if (fd < 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() No %s in package", name, path.c_str());
  }

  ExtractEntryToFile(za, &entry, fd);

  if (stat(path.c_str(), &st) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() Failed to create %s", name, path.c_str());
  }

  bad += ApplyParsedPerms(state, path.c_str(), &st, parsed);

  if (bad > 0) {
    return ErrorAbort(state, kSetMetadataFailure, "%s: some changes failed", name);
  }

  if (fsync(fd) != 0) {
    return ErrorAbort(state, kFsyncFailure, "%s() No %s in package", name, path.c_str());
  }
  close(fd.release());

  return StringValue("");
}

// symlink_chown(target, path, uid, gid)
//   Create symbolic link and set owner.
//   Returns nothing.
static Value* SymlinkChownFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() != 4) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects 4 arguments, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto& target = args[0];
  const auto path = args[1];

  int64_t uid, gid;
  if (sscanf(args[2].c_str(), "%" SCNd64, &uid) != 1 ||
      sscanf(args[3].c_str(), "%" SCNd64, &gid) != 1) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  struct stat st;
  if (lstat(path.c_str(), &st) == 0) {
    return StringValue("");
  }

  if (symlink(target.c_str(), path.c_str()) != 0) {
    return ErrorAbort(state, kSymlinkFailure, "%s: Error on symlink of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }
  if (lchown(path.c_str(), uid, gid) != 0) {
    return ErrorAbort(state, kSymlinkFailure, "%s: Error on lchown of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }

  return StringValue("");
}

// patch(path, zipfile, old_digest)
//   Patch a file.
//   Returns nothing.
Value* PatchFn(const char* name, State* state,
                    const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() != 3) {
    return ErrorAbort(state, kArgsParsingFailure,
                      "%s(): expected 4 args, got %zu", name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }
  const std::string  filename = args[0];
  const std::string& zipfile = args[1];
  const std::string& old_digest = args[2];
  if (old_digest.size() != 2 * SHA_DIGEST_LENGTH) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Bad digest length", name);
  }

  int ret;
  int fd;

  ZipArchiveHandle za = static_cast<FsUpdaterInfo*>(state->cookie)->package_zip;
  ZipString zip_string_path(zipfile.c_str());
  ZipEntry entry;
  if (FindEntry(za, zip_string_path, &entry) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() No %s in package", name, zipfile.c_str());
  }

  std::vector<uint8_t> patch_data;
  patch_data.resize(entry.uncompressed_length);
  ret = ExtractToMemory(za, &entry, patch_data.data(), patch_data.size());
  if (ret != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() Failed to read patch %s: %d", name, zipfile.c_str(), ret);
  }
  Value patch(Value::Type::BLOB, std::string(patch_data.cbegin(), patch_data.cend()));

  struct stat st;
  if (stat(filename.c_str(), &st) != 0) {
    return ErrorAbort(state, kFileOpenFailure, "%s() Failed to stat %s", name, filename.c_str());
  }

  std::vector<unsigned char> old_data(st.st_size);
  fd = open(filename.c_str(), O_RDONLY);
  if (fd == -1) {
    return ErrorAbort(state, kFileOpenFailure, "%s() Failed to open %s", name, filename.c_str());
  }
  ssize_t nread = read(fd, old_data.data(), old_data.size());
  close(fd);
  if (nread != (ssize_t)st.st_size) {
    return ErrorAbort(state, kFreadFailure, "%s() Failed to read %s", name, filename.c_str());
  }

  SHA_CTX sha_ctx;
  SHA1_Init(&sha_ctx);
  SHA1_Update(&sha_ctx, old_data.data(), old_data.size());
  uint8_t digest[SHA_DIGEST_LENGTH];
  SHA1_Final(digest, &sha_ctx);
  char hexdigest[2 * SHA_DIGEST_LENGTH + 1];
  for (size_t n = 0; n < SHA_DIGEST_LENGTH; ++n) {
      sprintf(&hexdigest[2 * n], "%02x", digest[n]);
  }

  uiPrintf(state, "File %s size %u digest %s", filename.c_str(), old_data.size(), hexdigest);

  if (memcmp(old_digest.c_str(), hexdigest, 2 * SHA_DIGEST_LENGTH) != 0) {
    uiPrintf(state, "digest mismatch, not patching %s: expected %s, got %s",
             filename.c_str(), old_digest.c_str(), hexdigest);
    return StringValue("");
  }

  std::string new_data;
  SinkFn sink = [&new_data](const unsigned char* data, size_t len) {
    new_data.append(reinterpret_cast<const char*>(data), len);
    return len;
  };

  ret = ApplyBSDiffPatch(old_data.data(), old_data.size(), patch, 0, sink);
  if (ret != 0) {
    //XXX: ErrorAbort
    uiPrintf(state, "Failed to patch %s: ApplyBSDiffPatch returned %d\n", filename.c_str(), ret);
  }

  fd = open(filename.c_str(), O_WRONLY);
  if (fd == -1) {
    return ErrorAbort(state, kFileOpenFailure, "%s() Failed to open %s: %s", name, filename.c_str(), strerror(errno));
  }
  size_t nwritten = write(fd, new_data.c_str(), new_data.size());
  close(fd);
  if (nwritten != new_data.size()) {
    return ErrorAbort(state, kFwriteFailure, "%s() Failed to write %s", name, filename.c_str());
  }

  return StringValue("");
}

// unlink(path)
//   Deletes path.
//   Returns nothing.
static Value* UnlinkFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() != 1) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects 1 argument, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];

  struct stat sb;
  if (lstat(path.c_str(), &sb) != 0) {
    return StringValue("");
  }

  if (unlink(path.c_str()) != 0) {
    return ErrorAbort(state, kFwriteFailure, "%s: Error on unlink of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }

  return StringValue("");
}

// chown(path, uid, gid)
//   Change ownership of existing path.
//   Returns nothing.
static Value* ChownFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() != 3) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects 3 arguments, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];

  int64_t uid, gid;
  if (sscanf(args[2].c_str(), "%" SCNd64, &uid) != 1 ||
      sscanf(args[3].c_str(), "%" SCNd64, &gid) != 1) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  if (lchown(path.c_str(), uid, gid) != 0) {
    return ErrorAbort(state, kSymlinkFailure, "%s: Error on lchown of \"%s\": %s", name,
                      path.c_str(), strerror(errno));
  }

  return StringValue("");
}

// chmeta(path, uid, gid, mode, ...)
//   Change metadata of existing path.
//   Returns nothing.
static Value* ChmetaFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
  if (argv.size() < 4) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() expects at least 4 arguments, got %zu",
                      name, argv.size());
  }

  std::vector<std::string> args;
  if (!ReadArgs(state, argv, &args)) {
    return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
  }

  const auto path = args[0];

  struct stat sb;
  if (lstat(path.c_str(), &sb) != 0) {
    return StringValue("");
  }

  struct perm_parsed_args parsed;
  ParsePermArgs(args, 0, &parsed);
  int bad = 0;

  bad += ApplyParsedPerms(state, path.c_str(), &sb, parsed);

  if (bad > 0) {
    return ErrorAbort(state, kSetMetadataFailure, "%s: some changes failed", name);
  }

  return StringValue("");
}

/*
 * These are the edify functions for file based incremental updates.
 *
 */
void RegisterFsUpdaterFunctions() {
  RegisterFunction("mkdir", MkdirFn);
  RegisterFunction("rmdir", RmdirFn);
  RegisterFunction("create", CreateFn);
  RegisterFunction("symlink_chown", SymlinkChownFn);
  RegisterFunction("patch", PatchFn);
  RegisterFunction("unlink", UnlinkFn);
  RegisterFunction("chown", ChownFn);
  RegisterFunction("chmeta", ChmetaFn);
}
