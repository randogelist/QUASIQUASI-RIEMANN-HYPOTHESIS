/* Lean 4.33 Linux self-location compatibility for this execution namespace.
 * Official runtime/io.cpp asks readlink("/proc/<getpid()>/exe", ...).
 * This namespace permits /proc/self/exe, while numeric /proc paths are denied.
 * Redirect exactly the calling process's own exe link to its standard self
 * alias. All other paths and all return/error semantics pass through libc.
 * No Lean binary, elaborator, kernel, or trust option is changed.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    typedef ssize_t (*readlink_fn)(const char *, char *, size_t);
    static readlink_fn real_readlink;
    if (!real_readlink)
        real_readlink = (readlink_fn)dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, own_exe) == 0)
        path = "/proc/self/exe";
    return real_readlink(path, buf, size);
}
