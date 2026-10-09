#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Some hosted runtimes permit /proc/self/exe but hide numeric process paths.
   Redirect only THIS process's executable lookup; all other calls pass through.
   This does not change Lean's kernel, elaboration, imported files or axioms. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char own[64];
  snprintf(own, sizeof own, "/proc/%d/exe", (int)getpid());
  return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buffer, size);
}
