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
 * We rename the LINK-TIME symbol with `#pragma redefine_extname`, not a `#define`.
 * A macro `#define cos prism_v_cos` would corrupt glibc's <math.h>, which builds
 * its SIMD declaration macros by token-pasting the function name (`__DECL_SIMD_##cos`
 * becomes `__DECL_SIMD_prism_v_cos`, an undefined identifier). redefine_extname
 * leaves the header's tokens alone and only renames the emitted/resolved symbol, so
 * every definition, internal cross-call, and wrapper call binds to prism_v_* while
 * <math.h> compiles unchanged. Force-included at the top of every libm unit and
 * pulled in by prism_libm.c, ahead of the declarations it applies to.
 */
#ifndef PRISM_LIBM_RENAME_H
#define PRISM_LIBM_RENAME_H

#pragma redefine_extname sin prism_v_sin
#pragma redefine_extname cos prism_v_cos
#pragma redefine_extname tan prism_v_tan
#pragma redefine_extname asin prism_v_asin
#pragma redefine_extname acos prism_v_acos
#pragma redefine_extname atan prism_v_atan
#pragma redefine_extname sinh prism_v_sinh
#pragma redefine_extname cosh prism_v_cosh
#pragma redefine_extname tanh prism_v_tanh
#pragma redefine_extname exp prism_v_exp
#pragma redefine_extname exp2 prism_v_exp2
#pragma redefine_extname expm1 prism_v_expm1
#pragma redefine_extname log prism_v_log
#pragma redefine_extname log2 prism_v_log2
#pragma redefine_extname log10 prism_v_log10
#pragma redefine_extname log1p prism_v_log1p
#pragma redefine_extname cbrt prism_v_cbrt
#pragma redefine_extname pow prism_v_pow
#pragma redefine_extname atan2 prism_v_atan2
#pragma redefine_extname hypot prism_v_hypot
#pragma redefine_extname fmod prism_v_fmod

#endif /* PRISM_LIBM_RENAME_H */
