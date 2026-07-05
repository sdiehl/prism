/* Floats: the owned shortest-round-trip formatter (a Dragon-style dtoa over an
 * in-runtime bignum) and the float builtins that print, parse, and pow. Floats
 * are boxed i64 cells at the value boundary; see prism_mem's box/unbox. */
#ifndef PRISM_FLOAT_H
#define PRISM_FLOAT_H

#include "prism_internal.h"

long prism_show_float(long f);
void prism_print_float(long f);
long prism_show_float_prec(long f, long digits);
long prism_parse_float(long s);
long prism_pow_float(long a, long b);
long prism_atan2(long a, long b);
long prism_hypot(long a, long b);
long prism_fmod(long a, long b);

#endif /* PRISM_FLOAT_H */
