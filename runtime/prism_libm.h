/* Owned numerics: the single deterministic math surface.
 *
 * Every transcendental a Prism program can produce routes through one of these
 * `prism_m_*` wrappers, which forward to the vendored double-precision musl libm
 * in `libm/` (see `libm/README.md`). Native codegen calls these (through the
 * boxed-float shims in prism_float.c for the binary ops), and the interpreter
 * FFIs the very same symbols, so interpreter and native are bit-identical by
 * construction. The contract is determinism, not correct rounding. */
#ifndef PRISM_LIBM_H
#define PRISM_LIBM_H

/* Unary. */
double prism_m_sin(double x);
double prism_m_cos(double x);
double prism_m_tan(double x);
double prism_m_asin(double x);
double prism_m_acos(double x);
double prism_m_atan(double x);
double prism_m_sinh(double x);
double prism_m_cosh(double x);
double prism_m_tanh(double x);
double prism_m_exp(double x);
double prism_m_exp2(double x);
double prism_m_expm1(double x);
double prism_m_log(double x);
double prism_m_log2(double x);
double prism_m_log10(double x);
double prism_m_log1p(double x);
double prism_m_cbrt(double x);

/* Binary. */
double prism_m_pow(double x, double y);
double prism_m_atan2(double y, double x);
double prism_m_hypot(double x, double y);
double prism_m_fmod(double x, double y);

#endif /* PRISM_LIBM_H */
