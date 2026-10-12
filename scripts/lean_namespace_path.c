/* PID-namespace compatibility for Lean's executable-location lookup only.
   Some containers expose host /proc entries but return namespace-local getpid.
   Resolve this process's executable through /proc/self/exe instead. This does
   not modify Lean, its kernel, arithmetic, proof terms, or other file access. */
#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
  ssize_t (*original)(const char*,char*,size_t)=dlsym(RTLD_NEXT,"readlink");
  char self[64];snprintf(self,sizeof(self),"/proc/%d/exe",getpid());
  return original(strcmp(path,self)==0?"/proc/self/exe":path,buf,size);
}
