/* The prism_m_* wrappers over the vendored double-precision musl libm (libm/).
 *
 * Each wrapper is a one-line forward to the standard-named vendored function, so
 * codegen and the interpreter address a single, prism-namespaced surface and the
 * standard names stay an internal detail of the vendored translation units. */
#include "prism_libm.h"
/* Namespace the vendored functions to prism_v_* (same header the vendored TUs use)
 * so these wrappers call the uniquely-named vendored copies, never the platform
 * libm. This makes the declarations and calls below expand to prism_v_*. */
#include "prism_libm_rename.h"

/* The vendored functions carry their standard C names; declare the ones we call
 * here rather than pulling <math.h> (whose prototypes clang could route to its
 * own builtins). These resolve to the definitions in libm/ at link time. */
double sin(double);
double cos(double);
double tan(double);
double asin(double);
double acos(double);
double atan(double);
double sinh(double);
double cosh(double);
double tanh(double);
double exp(double);
double exp2(double);
double expm1(double);
double log(double);
double log2(double);
double log10(double);
double log1p(double);
double cbrt(double);
double pow(double, double);
double atan2(double, double);
double hypot(double, double);
double fmod(double, double);

double prism_m_sin(double x) {
    return sin(x);
}
double prism_m_cos(double x) {
    return cos(x);
}
double prism_m_tan(double x) {
    return tan(x);
}
double prism_m_asin(double x) {
    return asin(x);
}
double prism_m_acos(double x) {
    return acos(x);
}
double prism_m_atan(double x) {
    return atan(x);
}
double prism_m_sinh(double x) {
    return sinh(x);
}
double prism_m_cosh(double x) {
    return cosh(x);
}
double prism_m_tanh(double x) {
    return tanh(x);
}
double prism_m_exp(double x) {
    return exp(x);
}
double prism_m_exp2(double x) {
    return exp2(x);
}
double prism_m_expm1(double x) {
    return expm1(x);
}
double prism_m_log(double x) {
    return log(x);
}
double prism_m_log2(double x) {
    return log2(x);
}
double prism_m_log10(double x) {
    return log10(x);
}
double prism_m_log1p(double x) {
    return log1p(x);
}
double prism_m_cbrt(double x) {
    return cbrt(x);
}

double prism_m_pow(double x, double y) {
    return pow(x, y);
}
double prism_m_atan2(double y, double x) {
    return atan2(y, x);
}
double prism_m_hypot(double x, double y) {
    return hypot(x, y);
}
double prism_m_fmod(double x, double y) {
    return fmod(x, y);
}

/* The vendored hypot calls `sqrt`; provide it as the hardware IEEE square root
 * (correctly rounded on every target, so identical everywhere and matching the
 * `Sqrt` FloatOp's intrinsic lowering). Defining it here means the vendored set
 * needs no system libm even at -O0, where clang would otherwise emit a libcall. */
double sqrt(double x) {
    /* Emit the hardware IEEE square-root instruction directly on the real
     * targets. `__builtin_sqrt` is permitted to lower to a call to this very
     * function (GCC's -Winfinite-recursion flags exactly that), so name the
     * instruction ourselves; the fallback keeps other archs building. */
    double r;
#if defined(__x86_64__)
    __asm__("sqrtsd %1, %0" : "=x"(r) : "x"(x));
#elif defined(__aarch64__)
    __asm__("fsqrt %d0, %d1" : "=w"(r) : "w"(x));
#else
    r = __builtin_sqrt(x);
#endif
    return r;
}
