/* prism_simd.c: the baseline 128-bit SIMD runtime.
 *
 * The scalar interpreter defines the semantics (`simd_builtin` in
 * src/eval/builtin.rs); this file must reproduce it bit for bit. A vector is a
 * two-word cell whose arity word is 0, so `prism_rc_dec` frees it without
 * treating the raw lanes as child pointers (the `prism_box` discipline, two
 * words wide). Float lanes are the doubles' bit patterns; integer lanes are the
 * two's-complement values. `min`/`max` use a plain `a < b ? a : b`, the same
 * formula the interpreter uses, so NaN and signed-zero behavior agrees by
 * construction rather than by matching a platform intrinsic's choice. The
 * per-op work is scalar and branch-free enough that the C compiler is free to
 * vectorize it under SSE2; correctness never depends on whether it does. */
#include "prism_simd.h"

#include "prism_internal.h"
#include "prism_mem.h"

#include <string.h>

/* A fresh two-lane vector cell holding the two raw words. Arity 0 keeps the
 * lanes out of the child scan; the cell is otherwise an ordinary counted cell
 * that dup/drop and the leak balance treat like any other. */
static long prism_simd_vec(long w0, long w1) {
    long *p = prism_alloc(2);
    p[PRISM_ARITY_W] = 0;
    p[PRISM_HDR_WORDS + 0] = w0;
    p[PRISM_HDR_WORDS + 1] = w1;
    return (long)p;
}

static double as_f64(long word) {
    double d;
    memcpy(&d, &word, sizeof d);
    return d;
}

static long f64_bits(double d) {
    long word;
    memcpy(&word, &d, sizeof word);
    return word;
}

/* Read lane `i` (0 or 1) of a vector cell. An out-of-range index is a codegen
 * or type error, not a recoverable condition: trap rather than read past the
 * cell, matching the interpreter's deterministic fault. */
static long prism_simd_word(long v, long i) {
    if (i != 0 && i != 1) {
        fprintf(stderr, "fatal: simd lane index %ld out of bounds\n", i);
        abort();
    }
    return ((long *)v)[PRISM_HDR_WORDS + i];
}

/* The float splat receives its scalar as the raw f64 bit pattern in an integer
 * register, exactly as the `F0` builtin codec unboxes it (`prism_show_float`
 * takes the same `long` bits). Declaring a `double` parameter would place it in
 * a floating-point register the caller never wrote, so the lanes matched the
 * interpreter only when the link-time inliner happened to reconcile the integer
 * call with the float definition; taking the bits as a `long` makes the splat
 * bit-exact at every optimization level and on both register conventions. The
 * pattern is duplicated into both lanes with no reinterpretation. */
long prism_simd_fsplat(long bits) {
    return prism_simd_vec(bits, bits);
}

long prism_simd_isplat(long x) {
    long v = prism_unbox(x);
    return prism_simd_vec(v, v);
}

long prism_simd_fadd(long a, long b) {
    return prism_simd_vec(f64_bits(as_f64(prism_simd_word(a, 0)) + as_f64(prism_simd_word(b, 0))),
                          f64_bits(as_f64(prism_simd_word(a, 1)) + as_f64(prism_simd_word(b, 1))));
}

long prism_simd_fsub(long a, long b) {
    return prism_simd_vec(f64_bits(as_f64(prism_simd_word(a, 0)) - as_f64(prism_simd_word(b, 0))),
                          f64_bits(as_f64(prism_simd_word(a, 1)) - as_f64(prism_simd_word(b, 1))));
}

long prism_simd_fmul(long a, long b) {
    return prism_simd_vec(f64_bits(as_f64(prism_simd_word(a, 0)) * as_f64(prism_simd_word(b, 0))),
                          f64_bits(as_f64(prism_simd_word(a, 1)) * as_f64(prism_simd_word(b, 1))));
}

static double lane_min(double x, double y) {
    return x < y ? x : y;
}

static double lane_max(double x, double y) {
    return x > y ? x : y;
}

long prism_simd_fmin(long a, long b) {
    return prism_simd_vec(
        f64_bits(lane_min(as_f64(prism_simd_word(a, 0)), as_f64(prism_simd_word(b, 0)))),
        f64_bits(lane_min(as_f64(prism_simd_word(a, 1)), as_f64(prism_simd_word(b, 1)))));
}

long prism_simd_fmax(long a, long b) {
    return prism_simd_vec(
        f64_bits(lane_max(as_f64(prism_simd_word(a, 0)), as_f64(prism_simd_word(b, 0)))),
        f64_bits(lane_max(as_f64(prism_simd_word(a, 1)), as_f64(prism_simd_word(b, 1)))));
}

/* Integer lanes are unsigned for wrapping arithmetic and bitwise ops; the bit
 * pattern is what the extract reinterprets as a signed I64. */
static long iw(long v, long i) {
    return prism_simd_word(v, i);
}

long prism_simd_iadd(long a, long b) {
    return prism_simd_vec((long)((unsigned long)iw(a, 0) + (unsigned long)iw(b, 0)),
                          (long)((unsigned long)iw(a, 1) + (unsigned long)iw(b, 1)));
}

long prism_simd_isub(long a, long b) {
    return prism_simd_vec((long)((unsigned long)iw(a, 0) - (unsigned long)iw(b, 0)),
                          (long)((unsigned long)iw(a, 1) - (unsigned long)iw(b, 1)));
}

long prism_simd_iand(long a, long b) {
    return prism_simd_vec(iw(a, 0) & iw(b, 0), iw(a, 1) & iw(b, 1));
}

long prism_simd_ior(long a, long b) {
    return prism_simd_vec(iw(a, 0) | iw(b, 0), iw(a, 1) | iw(b, 1));
}

long prism_simd_ixor(long a, long b) {
    return prism_simd_vec(iw(a, 0) ^ iw(b, 0), iw(a, 1) ^ iw(b, 1));
}

/* Extract reboxes the lane: a float lane becomes a boxed `Float`, an integer
 * lane a boxed `I64`. Both are one payload word (`prism_box`), so the same call
 * serves each; only the surface type the caller expects differs. */
long prism_simd_fextract(long v, long i) {
    return prism_box(prism_simd_word(v, i));
}

long prism_simd_iextract(long v, long i) {
    return prism_box(prism_simd_word(v, i));
}
