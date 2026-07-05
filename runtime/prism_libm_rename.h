/* Namespace the vendored double-precision libm's public functions to `prism_v_*`.
 *
 * The vendored functions carry their standard C names (`sin`, `cos`, `atan`, ...),
 * which collide with the platform libm. Because the transcendentals are not
 * IEEE-correctly-rounded, the platform's copy differs from ours by a ULP, and the
 * linker's choice between the two is not reliable across binaries (the interpreter
 * links the vendored archive as one static lib among the Rust runtime's own libm;
 * a native program links it too) -- so a plain `cos` can silently resolve to the
 * system copy in one binary and the vendored copy in another, breaking parity.
 *
 * Renaming every entry point the `prism_m_*` wrappers call gives each a unique
 * symbol that only the vendored translation units define and only prism references,
 * so no system math symbol is ever named. Included AFTER any <math.h> so the
 * platform's real-named declarations are processed first and left inert; the
 * vendored TUs (via libm.h) and the wrappers (prism_libm.c) both include this, so
 * definitions, internal cross-calls, and the wrapper calls all use the renamed name.
 */
#ifndef PRISM_LIBM_RENAME_H
#define PRISM_LIBM_RENAME_H

#define sin prism_v_sin
#define cos prism_v_cos
#define tan prism_v_tan
#define asin prism_v_asin
#define acos prism_v_acos
#define atan prism_v_atan
#define sinh prism_v_sinh
#define cosh prism_v_cosh
#define tanh prism_v_tanh
#define exp prism_v_exp
#define exp2 prism_v_exp2
#define expm1 prism_v_expm1
#define log prism_v_log
#define log2 prism_v_log2
#define log10 prism_v_log10
#define log1p prism_v_log1p
#define cbrt prism_v_cbrt
#define pow prism_v_pow
#define atan2 prism_v_atan2
#define hypot prism_v_hypot
#define fmod prism_v_fmod

#endif /* PRISM_LIBM_RENAME_H */
