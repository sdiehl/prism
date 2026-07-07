/* Integers: the sign-magnitude bignum cell, the canonical tagged-immediate/bignum
 * Int arithmetic, and the machine i64/u64 conversions and operators. */
#include "prism_int.h"
#include "prism_io.h"
#include "prism_mem.h"
#include "prism_string.h"

static long *prism_big_alloc(long nlimbs) {
    /* Same overflow-checked sizing as ordinary cells: a hostile or computed
     * limb count must never under-allocate and let the limb stores below write
     * out of bounds. */
    long *p = malloc(prism_cell_bytes(nlimbs));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = PRISM_BIG_TAG;
    p[PRISM_ARITY_W] = 0;
    prism_live_cells++;
    return p;
}

static unsigned long *big_limbs(long v) {
    return (unsigned long *)((long *)v + PRISM_HDR_WORDS);
}

static long big_count(long v) {
    return ((long *)v)[PRISM_ARITY_W];
}

static long big_mag(long v) {
    long n = big_count(v);
    return n < 0 ? -n : n;
}

static long mag_trim(const unsigned long *m, long n) {
    while (n > 0 && m[n - 1] == 0) n--;
    return n;
}

static long big_make(const unsigned long *m, long n, int neg) {
    n = mag_trim(m, n);
    long *p = prism_big_alloc(n);
    // n > 0 implies m is non-null (mag_trim already read it); the explicit `&& m`
    // says so to the analyzer, which otherwise loses the constraint through the
    // zero-bignum call big_make(0, 0, 0) and flags memcpy's nonnull `src`.
    if (n && m) memcpy(p + PRISM_HDR_WORDS, m, (size_t)n * 8);
    p[PRISM_ARITY_W] = neg ? -n : n;
    return (long)p;
}

static int mag_cmp(const unsigned long *a, long na, const unsigned long *b, long nb) {
    if (na != nb) return na < nb ? -1 : 1;
    for (long i = na - 1; i >= 0; i--)
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}

static long mag_add(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    __uint128_t c = 0;
    long n = na > nb ? na : nb;
    for (long i = 0; i < n; i++) {
        c += (__uint128_t)(i < na ? a[i] : 0) + (i < nb ? b[i] : 0);
        o[i] = (unsigned long)c;
        c >>= 64;
    }
    o[n] = (unsigned long)c;
    return n + 1;
}

/* Requires a >= b; in place (o == a) is safe. */
static long mag_sub(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    long borrow = 0;
    for (long i = 0; i < na; i++) {
        __int128 t = (__int128)a[i] - (i < nb ? b[i] : 0) - borrow;
        o[i] = (unsigned long)t;
        borrow = t < 0;
    }
    return na;
}

static void mag_mul(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    memset(o, 0, (size_t)(na + nb) * 8);
    for (long i = 0; i < na; i++) {
        unsigned long carry = 0;
        for (long j = 0; j < nb; j++) {
            __uint128_t t = (__uint128_t)a[i] * b[j] + o[i + j] + carry;
            o[i + j] = (unsigned long)t;
            carry = (unsigned long)(t >> 64);
        }
        o[i + nb] += carry;
    }
}

/* Shift-subtract long division: q gets na limbs, r gets nb + 1. */
static void mag_divrem(const unsigned long *a, long na, const unsigned long *b, long nb,
                       unsigned long *q, unsigned long *r) {
    memset(q, 0, (size_t)na * 8);
    memset(r, 0, (size_t)(nb + 1) * 8);
    for (long i = na * 64 - 1; i >= 0; i--) {
        unsigned long bit = (a[i / 64] >> (i % 64)) & 1;
        for (long k = 0; k <= nb; k++) {
            unsigned long top = r[k] >> 63;
            r[k] = (r[k] << 1) | bit;
            bit = top;
        }
        if (mag_cmp(r, mag_trim(r, nb + 1), b, nb) >= 0) {
            mag_sub(r, nb + 1, b, nb, r);
            q[i / 64] |= 1UL << (i % 64);
        }
    }
}

static long mag_muladd_small(unsigned long *m, long n, unsigned long mul, unsigned long add) {
    __uint128_t c = add;
    for (long i = 0; i < n; i++) {
        c += (__uint128_t)m[i] * mul;
        m[i] = (unsigned long)c;
        c >>= 64;
    }
    if (c) m[n++] = (unsigned long)c;
    return n;
}

static unsigned long mag_divmod_small(unsigned long *m, long n, unsigned long d) {
    __uint128_t rem = 0;
    for (long i = n - 1; i >= 0; i--) {
        __uint128_t t = (rem << 64) | m[i];
        m[i] = (unsigned long)(t / d);
        rem = t % d;
    }
    return (unsigned long)rem;
}

long prism_big_from_int(long v) {
    unsigned long m = v < 0 ? 0UL - (unsigned long)v : (unsigned long)v;
    return big_make(&m, 1, v < 0);
}

long prism_big_of_str(long s, int *ok) {
    const char *p = prism_str_data(s);
    const char *q = p + prism_str_len_bytes(s);
    while (p < q && prism_ws(*p)) p++;
    while (q > p && prism_ws(q[-1])) q--;
    int neg = 0;
    if (p < q && (*p == '-' || *p == '+')) neg = *p++ == '-';
    if (p == q) {
        *ok = 0;
        return 0;
    }
    for (const char *t = p; t < q; t++)
        if (*t < '0' || *t > '9') {
            *ok = 0;
            return 0;
        }
    unsigned long *m = malloc((size_t)((q - p) / 19 + 2) * 8);
    if (!m) abort();
    long n = 0;
    for (; p < q; p++) n = mag_muladd_small(m, n, 10, (unsigned long)(*p - '0'));
    long r = big_make(m, n, neg);
    free(m);
    *ok = 1;
    return r;
}

static long big_addsub(long a, long b, int flip) {
    long ma = big_mag(a), mb = big_mag(b);
    int sa = big_count(a) < 0, sb = (big_count(b) < 0) ^ flip;
    const unsigned long *la = big_limbs(a), *lb = big_limbs(b);
    unsigned long *o = malloc((size_t)((ma > mb ? ma : mb) + 1) * 8);
    if (!o) abort();
    long n;
    int neg;
    if (sa == sb) {
        n = mag_add(la, ma, lb, mb, o);
        neg = sa;
    } else if (mag_cmp(la, ma, lb, mb) >= 0) {
        n = mag_sub(la, ma, lb, mb, o);
        neg = sa;
    } else {
        n = mag_sub(lb, mb, la, ma, o);
        neg = sb;
    }
    long r = big_make(o, n, neg);
    free(o);
    return r;
}

long prism_big_add(long a, long b) {
    return big_addsub(a, b, 0);
}

long prism_big_sub(long a, long b) {
    return big_addsub(a, b, 1);
}

long prism_big_mul(long a, long b) {
    long ma = big_mag(a), mb = big_mag(b);
    if (ma == 0 || mb == 0) return big_make(0, 0, 0);
    unsigned long *o = malloc((size_t)(ma + mb) * 8);
    if (!o) abort();
    mag_mul(big_limbs(a), ma, big_limbs(b), mb, o);
    long r = big_make(o, ma + mb, (big_count(a) < 0) != (big_count(b) < 0));
    free(o);
    return r;
}

/* Truncated division: quotient rounds toward zero, remainder keeps the
 * dividend's sign, matching C, Rust, and num-bigint. */
static long big_divrem(long a, long b, int want_rem) {
    long ma = big_mag(a), mb = big_mag(b);
    if (mb == 0) prism_div_zero();
    if (ma == 0) return big_make(0, 0, 0);
    unsigned long *q = malloc((size_t)ma * 8);
    unsigned long *r = malloc((size_t)(mb + 1) * 8);
    if (!q || !r) abort();
    mag_divrem(big_limbs(a), ma, big_limbs(b), mb, q, r);
    long res = want_rem ? big_make(r, mb + 1, big_count(a) < 0)
                        : big_make(q, ma, (big_count(a) < 0) != (big_count(b) < 0));
    free(q);
    free(r);
    return res;
}

long prism_big_div(long a, long b) {
    return big_divrem(a, b, 0);
}

long prism_big_rem(long a, long b) {
    return big_divrem(a, b, 1);
}

long prism_big_cmp(long a, long b) {
    long na = big_count(a), nb = big_count(b);
    if (na != nb) return na < nb ? -1 : 1;
    int c = mag_cmp(big_limbs(a), big_mag(a), big_limbs(b), big_mag(b));
    return na < 0 ? -c : c;
}

long prism_big_show(long a) {
    long n = big_mag(a);
    if (n == 0) return prism_str_lit("0", 1);
    unsigned long *t = malloc((size_t)n * 8);
    unsigned long *chunk = malloc((size_t)(n + 2) * 8);
    if (!t || !chunk) abort();
    memcpy(t, big_limbs(a), (size_t)n * 8);
    long k = 0;
    while (n > 0) {
        chunk[k++] = mag_divmod_small(t, n, 10000000000000000000UL);
        n = mag_trim(t, n);
    }
    long cap = k * 19 + 2;
    char *buf = malloc((size_t)cap);
    if (!buf) abort();
    char *o = buf;
    if (big_count(a) < 0) *o++ = '-';
    char tmp[32];
    int written = snprintf(tmp, sizeof tmp, "%lu", chunk[k - 1]);
    if (written < 0 || (size_t)written >= sizeof tmp) abort();
    size_t len = (size_t)written;
    if (len > (size_t)(buf + cap - o)) abort();
    memcpy(o, tmp, len);
    o += len;
    for (long i = k - 2; i >= 0; i--) {
        written = snprintf(tmp, sizeof tmp, "%019lu", chunk[i]);
        if (written < 0 || (size_t)written >= sizeof tmp) abort();
        len = (size_t)written;
        if (len > (size_t)(buf + cap - o)) abort();
        memcpy(o, tmp, len);
        o += len;
    }
    long cell = prism_str_lit(buf, o - buf);
    free(t);
    free(chunk);
    free(buf);
    return cell;
}

/* Lean-model Int: a tagged immediate (v<<1|1) when the value fits 63 bits, a
 * PRISM_BIG_TAG cell otherwise. Canonical form is the invariant: every entry
 * point that produces an Int returns an immediate whenever the mathematical
 * value fits, so equal values never split across representations. None of
 * these functions consume their arguments; callers rc_dec after the call. */
#define PRISM_IMM_MAX ((1L << 62) - 1)
#define PRISM_IMM_MIN (-(1L << 62))

static long int_imm(long v) {
    /* Shift in unsigned: a signed left-shift of a negative value is UB in C
     * (works at -O2, but UBSan flags it). This wraps mod 2^64, matching the
     * codegen side's wrapping_shl(1) | 1 (src/codegen/emit.rs). */
    return (long)(((unsigned long)v << 1) | 1UL);
}

static long big_norm(long b) {
    long n = big_count(b);
    unsigned long lo = big_mag(b) ? big_limbs(b)[0] : 0;
    if (big_mag(b) <= 1 && lo <= (n < 0 ? 1UL << 62 : (unsigned long)PRISM_IMM_MAX)) {
        prism_rc_dec(b);
        return int_imm(n < 0 ? -(long)lo : (long)lo);
    }
    return b;
}

static long int_as_big(long w, int *fresh) {
    *fresh = (int)(w & 1);
    return *fresh ? prism_big_from_int(w >> 1) : w;
}

static long int_slow(long a, long b, long (*f)(long, long)) {
    int fa, fb;
    long ba = int_as_big(a, &fa), bb = int_as_big(b, &fb);
    long r = f(ba, bb);
    if (fa) prism_rc_dec(ba);
    if (fb) prism_rc_dec(bb);
    return big_norm(r);
}

long prism_rt_int_add(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_add_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_add);
}

long prism_rt_int_sub(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_sub_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_sub);
}

long prism_rt_int_mul(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_mul_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_mul);
}

long prism_rt_int_div(long a, long b) {
    if (a & b & 1) {
        long y = b >> 1;
        if (y == 0) prism_div_zero();
        long q = (a >> 1) / y;
        if (q >= PRISM_IMM_MIN && q <= PRISM_IMM_MAX) return int_imm(q);
    }
    return int_slow(a, b, prism_big_div);
}

long prism_rt_int_rem(long a, long b) {
    if (a & b & 1) {
        long y = b >> 1;
        if (y == 0) prism_div_zero();
        return int_imm((a >> 1) % y);
    }
    return int_slow(a, b, prism_big_rem);
}

long prism_rt_int_cmp(long a, long b) {
    if (a & b & 1) return a < b ? -1 : a > b ? 1 : 0;
    int fa, fb;
    long ba = int_as_big(a, &fa), bb = int_as_big(b, &fb);
    long c = prism_big_cmp(ba, bb);
    if (fa) prism_rc_dec(ba);
    if (fb) prism_rc_dec(bb);
    return c;
}

long prism_show_int(long w) {
    if (w & 1) {
        char buf[32];
        int k = snprintf(buf, sizeof buf, "%ld", w >> 1);
        return prism_str_lit(buf, k);
    }
    return prism_big_show(w);
}

/* Trim ASCII whitespace, optional sign, then strict base-10 digits of any
 * length: Some(n) on success, None on empty/non-numeric input. */
long prism_parse_int(long s) {
    int ok = 0;
    long b = prism_big_of_str(s, &ok);
    if (!ok) return prism_ctor(0, 0, 0); /* None */
    long n = big_norm(b);
    return prism_ctor(1, 1, &n); /* Some(n) */
}

/* Elaborator-only: a big literal whose text is known-valid digits, so it skips
 * the Option wrapper and returns the raw Integer cell. */
long prism_big_lit(long s) {
    int ok = 0;
    return big_norm(prism_big_of_str(s, &ok));
}

/* I64 and U64 are boxed 64-bit payload cells like Float. Arithmetic wraps mod
 * 2^64 and is sign-agnostic, so add/sub/mul are shared by both types. */
static unsigned long int_low64(long w) {
    if (w & 1) return (unsigned long)(w >> 1);
    unsigned long lo = big_mag(w) ? big_limbs(w)[0] : 0;
    return big_count(w) < 0 ? (unsigned long)(~lo) + 1UL : lo;
}

long prism_to_i64(long w) {
    return prism_box((long)int_low64(w));
}

long prism_to_u64(long w) {
    return prism_box((long)int_low64(w));
}

/* Encode a raw machine integer as a Prism Int: a tagged immediate when it fits
 * the 63-bit immediate range, a bignum cell otherwise. The single encoding
 * chokepoint for values entering from the machine-word world (boxed i64/u64
 * conversions, read_int). */
long prism_int_of_long(long v) {
    if (v >= PRISM_IMM_MIN && v <= PRISM_IMM_MAX) return int_imm(v);
    return prism_big_from_int(v);
}

long prism_int_of_i64(long p) {
    return prism_int_of_long(prism_unbox(p));
}

long prism_int_of_u64(long p) {
    unsigned long v = (unsigned long)prism_unbox(p);
    if (v <= (unsigned long)PRISM_IMM_MAX) return int_imm((long)v);
    return big_make(&v, 1, 0);
}

long prism_i64_add(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) + (unsigned long)prism_unbox(b)));
}

long prism_i64_sub(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) - (unsigned long)prism_unbox(b)));
}

long prism_i64_mul(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) * (unsigned long)prism_unbox(b)));
}

long prism_i64_div(long a, long b) {
    long x = prism_unbox(a), y = prism_unbox(b);
    if (y == 0) prism_div_zero();
    if (y == -1) return prism_box((long)(0UL - (unsigned long)x)); /* MIN/-1 wraps */
    return prism_box(x / y);
}

long prism_i64_rem(long a, long b) {
    long y = prism_unbox(b);
    if (y == 0) prism_div_zero();
    if (y == -1) return prism_box(0);
    return prism_box(prism_unbox(a) % y);
}

long prism_u64_div(long a, long b) {
    unsigned long y = (unsigned long)prism_unbox(b);
    if (y == 0) prism_div_zero();
    return prism_box((long)((unsigned long)prism_unbox(a) / y));
}

long prism_u64_rem(long a, long b) {
    unsigned long y = (unsigned long)prism_unbox(b);
    if (y == 0) prism_div_zero();
    return prism_box((long)((unsigned long)prism_unbox(a) % y));
}

long prism_i64_cmp(long a, long b) {
    long x = prism_unbox(a), y = prism_unbox(b);
    return x < y ? -1 : x > y ? 1 : 0;
}

long prism_u64_cmp(long a, long b) {
    unsigned long x = (unsigned long)prism_unbox(a), y = (unsigned long)prism_unbox(b);
    return x < y ? -1 : x > y ? 1 : 0;
}

/* Wrapping add/sub/mul share a bit pattern across signedness, so the u64 lane
   reuses the i64 wraparound. */
long prism_u64_add(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) + (unsigned long)prism_unbox(b)));
}
long prism_u64_sub(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) - (unsigned long)prism_unbox(b)));
}
long prism_u64_mul(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) * (unsigned long)prism_unbox(b)));
}

/* Fixed-width bitwise/shift. and/or/xor are bit-pattern identical across lanes;
   shifts mask the count to 0..64. i64_shr is arithmetic (signed >>), u64_shr
   logical (unsigned >>). */
long prism_i64_and(long a, long b) {
    return prism_box(prism_unbox(a) & prism_unbox(b));
}
long prism_i64_or(long a, long b) {
    return prism_box(prism_unbox(a) | prism_unbox(b));
}
long prism_i64_xor(long a, long b) {
    return prism_box(prism_unbox(a) ^ prism_unbox(b));
}
long prism_u64_and(long a, long b) {
    return prism_box(prism_unbox(a) & prism_unbox(b));
}
long prism_u64_or(long a, long b) {
    return prism_box(prism_unbox(a) | prism_unbox(b));
}
long prism_u64_xor(long a, long b) {
    return prism_box(prism_unbox(a) ^ prism_unbox(b));
}

long prism_i64_shl(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) << (prism_unbox(b) & 63)));
}
long prism_i64_shr(long a, long b) {
    return prism_box(prism_unbox(a) >> (prism_unbox(b) & 63)); /* arithmetic */
}
long prism_u64_shl(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) << (prism_unbox(b) & 63)));
}
long prism_u64_shr(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) >> (prism_unbox(b) & 63))); /* logical */
}

long prism_show_i64(long p) {
    char buf[32];
    int k = snprintf(buf, sizeof buf, "%ld", prism_unbox(p));
    return prism_str_lit(buf, k);
}

long prism_show_u64(long p) {
    char buf[32];
    int k = snprintf(buf, sizeof buf, "%lu", (unsigned long)prism_unbox(p));
    return prism_str_lit(buf, k);
}
