/* IO, environment, and process: console read/print, the random generator, program
 * arguments and environment, the file operations, shell-out, and the fault traps
 * (division by zero, wrong-arity apply, non-exhaustive case, error/fatal) that
 * print a diagnostic to stderr and exit. main() lives here too. */
#ifndef PRISM_IO_H
#define PRISM_IO_H

#include "prism_internal.h"

/* The fault traps do not return (each prints to stderr and exits); the _Noreturn
 * marker lets a caller in another module see that the code after a guarded trap
 * is unreachable, which the single-file build got from the visible exit(). */
_Noreturn void prism_div_zero(void);
_Noreturn void prism_apply_error(void);
_Noreturn void prism_match_error(void);
_Noreturn void prism_fatal(long s);
_Noreturn void prism_error_int(long n);
long prism_prim_read_int(void);
long prism_prim_read_line(void);
void prism_print_int(long w);
void prism_print_nl(void);
void prism_srand(long seed);
long prism_prim_rand(void);
long prism_prim_wall_now(void);
long prism_prim_mono_now(void);
long prism_prim_args_count(void);
long prism_prim_arg(long i);
long prism_prim_getenv(long name);
long prism_probe_enabled(long name);
long prism_prim_read_file(long path);
long prism_prim_read_bytes(long path);
long prism_prim_write_bytes(long path, long buf);
long prism_write_file(long path, long contents);
long prism_append_file(long path, long contents);
long prism_prim_file_exists(long path);
long prism_remove_file(long path);
long prism_system(long cmd);
long prism_eprint(long s);
long prism_exit(long code);

#endif /* PRISM_IO_H */
