/* Integers: the sign-magnitude bignum cell, the canonical tagged-immediate/bignum
 * Int arithmetic (the slow path of the fixed-width operators), and the machine
 * i64/u64 conversions and operators. */
#ifndef PRISM_INT_H
#define PRISM_INT_H

#include "prism_internal.h"

long prism_big_from_int(long v);
long prism_big_of_str(long s, int *ok);
long prism_big_add(long a, long b);
long prism_big_sub(long a, long b);
long prism_big_mul(long a, long b);
long prism_big_div(long a, long b);
long prism_big_rem(long a, long b);
long prism_big_cmp(long a, long b);
long prism_big_show(long a);
long prism_big_lit(long s);
long prism_parse_int(long s);

long prism_rt_int_add(long a, long b);
long prism_rt_int_sub(long a, long b);
long prism_rt_int_mul(long a, long b);
long prism_rt_int_div(long a, long b);
long prism_rt_int_rem(long a, long b);
long prism_rt_int_cmp(long a, long b);
long prism_show_int(long w);

long prism_to_i64(long w);
long prism_to_u64(long w);
long prism_int_of_long(long v);
long prism_int_of_i64(long p);
long prism_int_of_u64(long p);
long prism_i64_add(long a, long b);
long prism_i64_sub(long a, long b);
long prism_i64_mul(long a, long b);
long prism_i64_div(long a, long b);
long prism_i64_rem(long a, long b);
long prism_u64_div(long a, long b);
long prism_u64_rem(long a, long b);
long prism_i64_cmp(long a, long b);
long prism_u64_cmp(long a, long b);
long prism_u64_add(long a, long b);
long prism_u64_sub(long a, long b);
long prism_u64_mul(long a, long b);
long prism_i64_and(long a, long b);
long prism_i64_or(long a, long b);
long prism_i64_xor(long a, long b);
long prism_u64_and(long a, long b);
long prism_u64_or(long a, long b);
long prism_u64_xor(long a, long b);
long prism_i64_shl(long a, long b);
long prism_i64_shr(long a, long b);
long prism_u64_shl(long a, long b);
long prism_u64_shr(long a, long b);
long prism_show_i64(long p);
long prism_show_u64(long p);

#endif /* PRISM_INT_H */
