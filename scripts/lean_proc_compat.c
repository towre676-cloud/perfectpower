#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char*,char*,size_t);
  if(!original) original=dlsym(RTLD_NEXT,"readlink");
  ssize_t n=original(path,buf,size);
  char expected[96]; snprintf(expected,sizeof(expected),"/proc/%d/exe",getpid());
  if(strcmp(path,expected)==0)
    return original("/proc/self/exe",buf,size);
  return n;
}
