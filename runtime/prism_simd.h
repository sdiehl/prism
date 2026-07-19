/* Public interface of the baseline 128-bit SIMD runtime in prism_simd.c.
 *
 * Each entry mirrors one wired `simd_*` builtin. A vector is a two-word cell
 * (arity 0, so the reference-count collector never recurses into the raw
 * lanes); the codegen passes and receives it as an ordinary `long` cell
 * pointer. The scalar interpreter (`src/eval/builtin.rs`) is the parity oracle,
 * and every function here reproduces its exact per-lane formula, including NaN,
 * signed zero, and subnormals. */
#ifndef PRISM_SIMD_H
#define PRISM_SIMD_H

long prism_simd_fsplat(long bits);
long prism_simd_isplat(long x);
long prism_simd_fadd(long a, long b);
long prism_simd_fsub(long a, long b);
long prism_simd_fmul(long a, long b);
long prism_simd_fmin(long a, long b);
long prism_simd_fmax(long a, long b);
long prism_simd_iadd(long a, long b);
long prism_simd_isub(long a, long b);
long prism_simd_iand(long a, long b);
long prism_simd_ior(long a, long b);
long prism_simd_ixor(long a, long b);
long prism_simd_fextract(long v, long i);
long prism_simd_iextract(long v, long i);

#endif /* PRISM_SIMD_H */
