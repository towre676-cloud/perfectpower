#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <string.h>
ssize_t readlink(const char *p,char *b,size_t n) { ssize_t (*f)(const char*,char*,size_t)=dlsym(RTLD_NEXT,"readlink"); if(strncmp(p,"/proc/",6)==0 && strlen(p)>4 && strcmp(p+strlen(p)-4,"/exe")==0) p="/proc/self/exe"; return f(p,b,n); }
