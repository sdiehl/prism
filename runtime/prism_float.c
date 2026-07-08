/* Floats: the owned shortest-round-trip dtoa and the float builtins. */
#include "prism_float.h"
#include "prism_libm.h"
#include "prism_mem.h"
#include "prism_string.h"

/* --- Shortest-round-trip decimal digit generation (Dragon4) ---------------
 *
 * The significant digits of a shortest-round-trip float print are produced here
 * with exact integer arithmetic, owning the digit selection in-repo rather than
 * deferring to libc's snprintf/strtod round-trip. The output is byte-identical
 * to the interpreter's shortest form by construction: same algorithm class
 * (correctly-rounded shortest decimal, round-half-to-even at boundaries), so the
 * digit string and exponent match Rust's float Display digit for digit.
 *
 * A fixed-capacity base-2^32 bignum backs the exact scaling. The widest
 * intermediate is a subnormal scaled toward its leading digit (~2^1130) or
 * DBL_MAX's denominator (~2^1027), both well under the capacity; every mutator
 * aborts rather than silently truncate if that bound is ever exceeded. */
#define PRISM_DTOA_LIMBS 128 /* margin for fixed precision up to f64's 2^-1074 tail */

typedef struct {
    uint32_t w[PRISM_DTOA_LIMBS]; /* little-endian base-2^32 limbs */
    int n;                        /* used limbs; n == 0 is the value zero */
} DtoaBig;

static void dtoa_big_norm(DtoaBig *b) {
    while (b->n > 0 && b->w[b->n - 1] == 0) b->n--;
}

static void dtoa_big_set_u64(DtoaBig *b, uint64_t x) {
    b->n = 0;
    while (x) {
        b->w[b->n++] = (uint32_t)x;
        x >>= 32;
    }
}

static int dtoa_big_cmp(const DtoaBig *a, const DtoaBig *b) {
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (int i = a->n - 1; i >= 0; i--)
        if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    return 0;
}

/* a += b */
static void dtoa_big_add(DtoaBig *a, const DtoaBig *b) {
    int n = a->n > b->n ? a->n : b->n;
    uint64_t carry = 0;
    for (int i = 0; i < n; i++) {
        uint64_t s = carry + (i < a->n ? a->w[i] : 0) + (i < b->n ? b->w[i] : 0);
        a->w[i] = (uint32_t)s;
        carry = s >> 32;
    }
    if (carry) {
        if (n >= PRISM_DTOA_LIMBS) abort();
        a->w[n++] = (uint32_t)carry;
    }
    a->n = n;
    dtoa_big_norm(a);
}

/* a -= b, requires a >= b */
static void dtoa_big_sub(DtoaBig *a, const DtoaBig *b) {
    int64_t borrow = 0;
    for (int i = 0; i < a->n; i++) {
        int64_t s = (int64_t)a->w[i] - (int64_t)(i < b->n ? b->w[i] : 0) - borrow;
        if (s < 0) {
            s += (int64_t)1 << 32;
            borrow = 1;
        } else {
            borrow = 0;
        }
        a->w[i] = (uint32_t)s;
    }
    dtoa_big_norm(a);
}

/* a *= m */
static void dtoa_big_mul_small(DtoaBig *a, uint32_t m) {
    uint64_t carry = 0;
    for (int i = 0; i < a->n; i++) {
        uint64_t p = (uint64_t)a->w[i] * m + carry;
        a->w[i] = (uint32_t)p;
        carry = p >> 32;
    }
    while (carry) {
        if (a->n >= PRISM_DTOA_LIMBS) abort();
        a->w[a->n++] = (uint32_t)carry;
        carry >>= 32;
    }
    dtoa_big_norm(a);
}

/* a *= b (schoolbook) */
static void dtoa_big_mul(DtoaBig *a, const DtoaBig *b) {
    uint32_t out[PRISM_DTOA_LIMBS] = {0};
    for (int i = 0; i < a->n; i++) {
        uint64_t carry = 0;
        for (int j = 0; j < b->n; j++) {
            if (i + j >= PRISM_DTOA_LIMBS) abort();
            uint64_t cur = (uint64_t)out[i + j] + (uint64_t)a->w[i] * b->w[j] + carry;
            out[i + j] = (uint32_t)cur;
            carry = cur >> 32;
        }
        for (int k = i + b->n; carry; k++) {
            if (k >= PRISM_DTOA_LIMBS) abort();
            uint64_t cur = (uint64_t)out[k] + carry;
            out[k] = (uint32_t)cur;
            carry = cur >> 32;
        }
    }
    int outn = a->n + b->n;
    if (outn > PRISM_DTOA_LIMBS) outn = PRISM_DTOA_LIMBS;
    for (int i = 0; i < outn; i++) a->w[i] = out[i];
    a->n = outn;
    dtoa_big_norm(a);
}

/* a *= 2^bits */
static void dtoa_big_shl(DtoaBig *a, int bits) {
    if (a->n == 0 || bits == 0) return;
    int words = bits / 32, rem = bits % 32;
    if (words) {
        if (a->n + words > PRISM_DTOA_LIMBS) abort();
        for (int i = a->n - 1; i >= 0; i--) a->w[i + words] = a->w[i];
        for (int i = 0; i < words; i++) a->w[i] = 0;
        a->n += words;
    }
    if (rem) {
        uint32_t carry = 0;
        for (int i = 0; i < a->n; i++) {
            uint64_t s = ((uint64_t)a->w[i] << rem) | carry;
            a->w[i] = (uint32_t)s;
            carry = (uint32_t)(s >> 32);
        }
        if (carry) {
            if (a->n >= PRISM_DTOA_LIMBS) abort();
            a->w[a->n++] = carry;
        }
    }
    dtoa_big_norm(a);
}

/* Powers of ten that fit a single limb; PRISM_POW10_CHUNK is the largest, used
 * to multiply by 10^k in one-limb strides. */
static const uint32_t PRISM_POW10_SMALL[10] = {1,      10,      100,      1000,      10000,
                                               100000, 1000000, 10000000, 100000000, 1000000000};
#define PRISM_POW10_CHUNK_EXP 9
#define PRISM_POW10_CHUNK 1000000000u

/* a *= 10^k */
static void dtoa_big_mul_pow10(DtoaBig *a, int k) {
    while (k >= PRISM_POW10_CHUNK_EXP) {
        dtoa_big_mul_small(a, PRISM_POW10_CHUNK);
        k -= PRISM_POW10_CHUNK_EXP;
    }
    if (k > 0) dtoa_big_mul_small(a, PRISM_POW10_SMALL[k]);
}

static void dtoa_big_add_small(DtoaBig *a, uint32_t x) {
    uint64_t carry = x;
    int i = 0;
    while (carry) {
        if (i >= a->n) {
            if (i >= PRISM_DTOA_LIMBS) abort();
            a->w[i] = 0;
            a->n = i + 1;
        }
        uint64_t s = (uint64_t)a->w[i] + carry;
        a->w[i] = (uint32_t)s;
        carry = s >> 32;
        i++;
    }
}

static uint32_t dtoa_big_div_small(DtoaBig *a, uint32_t d) {
    uint64_t rem = 0;
    for (int i = a->n - 1; i >= 0; i--) {
        uint64_t cur = (rem << 32) | a->w[i];
        a->w[i] = (uint32_t)(cur / d);
        rem = cur % d;
    }
    dtoa_big_norm(a);
    return (uint32_t)rem;
}

static int dtoa_big_test_bit(const DtoaBig *a, int bit) {
    int word = bit / 32, off = bit % 32;
    return word < a->n && ((a->w[word] >> off) & 1u);
}

static int dtoa_big_any_bit_below(const DtoaBig *a, int bit) {
    int full = bit / 32, off = bit % 32;
    for (int i = 0; i < full && i < a->n; i++)
        if (a->w[i] != 0) return 1;
    if (full < a->n && off > 0) {
        uint32_t mask = (1u << off) - 1u;
        if ((a->w[full] & mask) != 0) return 1;
    }
    return 0;
}

static DtoaBig dtoa_big_shr(const DtoaBig *a, int bits) {
    DtoaBig out = {{0}, 0};
    int words = bits / 32, rem = bits % 32;
    if (words >= a->n) return out;
    out.n = a->n - words;
    for (int i = 0; i < out.n; i++) {
        uint32_t lo = a->w[i + words] >> rem;
        uint32_t hi = 0;
        if (rem && i + words + 1 < a->n) hi = a->w[i + words + 1] << (32 - rem);
        out.w[i] = lo | hi;
    }
    dtoa_big_norm(&out);
    return out;
}

static DtoaBig dtoa_big_div_pow2_round(const DtoaBig *num, int bits) {
    DtoaBig q = dtoa_big_shr(num, bits);
    if (bits <= 0) return q;
    int half = dtoa_big_test_bit(num, bits - 1);
    int sticky = dtoa_big_any_bit_below(num, bits - 1);
    int odd = q.n > 0 && (q.w[0] & 1u);
    if (half && (sticky || odd)) dtoa_big_add_small(&q, 1);
    return q;
}

static int append_u32_dec(char *out, int o, uint32_t x, int width) {
    char tmp[10];
    int n = 0;
    do {
        tmp[n++] = (char)('0' + (x % 10));
        x /= 10;
    } while (x);
    while (n < width) tmp[n++] = '0';
    while (n > 0) out[o++] = tmp[--n];
    return o;
}

static int dtoa_big_to_dec(const DtoaBig *a, char *out) {
    if (a->n == 0) {
        out[0] = '0';
        return 1;
    }
    DtoaBig tmp = *a;
    uint32_t chunks[180];
    int nc = 0;
    while (tmp.n > 0) {
        if (nc >= (int)(sizeof chunks / sizeof chunks[0])) abort();
        chunks[nc++] = dtoa_big_div_small(&tmp, PRISM_POW10_CHUNK);
    }
    int o = append_u32_dec(out, 0, chunks[nc - 1], 0);
    for (int i = nc - 2; i >= 0; i--) o = append_u32_dec(out, o, chunks[i], 9);
    return o;
}

/* Bit layout of an IEEE-754 double. */
#define PRISM_F64_MANT_BITS 52
#define PRISM_F64_EXP_BIAS 1075 /* 1023 + 52: unbiased exponent of the integer significand */
#define PRISM_F64_MIN_EXP (-1074)
#define PRISM_F64_HIDDEN (1ULL << PRISM_F64_MANT_BITS)
/* log10(2), for the initial decimal-exponent estimate (corrected exactly below). */
#define PRISM_LOG10_2 0.30102999566398119521

/* Largest significand a shortest-round-trip double print ever needs; 17 decimal
 * digits fit a u64, so the p-digit integer is exact in a machine word. */
#define PRISM_FLOAT_MAX_DIGITS 17

/* Sign of the decimal `F * 10^g` minus the rational `X / S` (S > 0). Both sides
 * are scaled to integers before comparing: multiply through by S, and by
 * 10^(-g) when g is negative, so the comparison is exact. */
static int dtoa_cmp_decimal(uint64_t F, int g, const DtoaBig *X, const DtoaBig *S) {
    DtoaBig lhs, rhs = *X;
    dtoa_big_set_u64(&lhs, F);
    if (g >= 0) {
        dtoa_big_mul_pow10(&lhs, g);
        dtoa_big_mul(&lhs, S); /* (F * 10^g) * S  vs  X */
    } else {
        dtoa_big_mul(&lhs, S); /* F * S           vs  X * 10^(-g) */
        dtoa_big_mul_pow10(&rhs, -g);
    }
    return dtoa_big_cmp(&lhs, &rhs);
}

/* Decimal significand of `d` (finite, > 0) matching the interpreter's `fmt_g`:
 * the FEWEST significant digits p in 1..17 whose correctly-rounded (round half
 * to even) p-digit decimal rounds back to exactly `d`. This is the trial loop
 * `fmt_g` runs over Rust's `{:.*e}` and `parse::<f64>()`, reproduced with exact
 * integer arithmetic so the digit string is owned in-repo rather than resting on
 * libc agreeing with Rust. The correctly-rounded p-digit value is not always the
 * shortest that round-trips (a power of two is the classic case), so this must
 * be the trial loop, not a one-pass shortest formatter, to stay byte-identical.
 *
 * Writes the digit chars into `digits` (no sign, no point), the count into `*nd`
 * (1..17), and the base-10 exponent of the leading digit into `*e10` (value ==
 * 0.d1..dn * 10^(*e10 + 1)). `digits` must hold at least 18 bytes. */
static void prism_shortest_digits(double d, char *digits, int *nd, int *e10) {
    uint64_t bits;
    memcpy(&bits, &d, sizeof bits);
    int be = (int)((bits >> PRISM_F64_MANT_BITS) & 0x7ff);
    uint64_t frac = bits & (PRISM_F64_HIDDEN - 1);
    uint64_t f;
    int e;
    if (be == 0) {
        f = frac; /* subnormal; d > 0 so frac != 0 */
        e = PRISM_F64_MIN_EXP;
    } else {
        f = frac | PRISM_F64_HIDDEN; /* normal: restore the hidden leading bit */
        e = be - PRISM_F64_EXP_BIAS;
    }
    /* Round-to-nearest-EVEN makes the rounding boundaries inclusive exactly when
     * the significand is even, so a decimal landing on a boundary round-trips. */
    int even = (f & 1) == 0;

    /* Scaled exact rationals: value == R/S, and the half-gaps to the neighboring
     * doubles are Mp/S (upper) and Mm/S (lower). Everything is scaled by 2 so a
     * half-ulp is an integer; a decimal round-trips to `d` iff it lies in
     * (value - Mm/S, value + Mp/S), boundaries included when `even`. */
    DtoaBig R, S, Mp, Mm;
    if (e >= 0) {
        dtoa_big_set_u64(&R, f);
        dtoa_big_shl(&R, e + 1); /* R = f * 2^(e+1) */
        dtoa_big_set_u64(&S, 2);
        dtoa_big_set_u64(&Mp, 1);
        dtoa_big_shl(&Mp, e); /* Mp = 2^e */
        Mm = Mp;
    } else {
        dtoa_big_set_u64(&R, f);
        dtoa_big_shl(&R, 1); /* R = f * 2 */
        dtoa_big_set_u64(&S, 1);
        dtoa_big_shl(&S, 1 - e); /* S = 2^(1-e) */
        dtoa_big_set_u64(&Mp, 1);
        dtoa_big_set_u64(&Mm, 1);
    }
    /* A power-of-two significand (and not the smallest normal, whose predecessor
     * shares its exponent) sits at a binary-exponent boundary: the gap below is
     * half the gap above. Scale R, S, Mp by 2 and leave Mm, so Mm == Mp/2. */
    if (f == PRISM_F64_HIDDEN && be > 1) {
        dtoa_big_mul_small(&R, 2);
        dtoa_big_mul_small(&S, 2);
        dtoa_big_mul_small(&Mp, 2);
    }
    /* The round-trip boundaries as integer numerators over S. */
    DtoaBig hi_num = R, lo_num = R;
    dtoa_big_add(&hi_num, &Mp);
    dtoa_big_sub(&lo_num, &Mm);

    /* Position the leading digit: A/B == value, scaled into [1/10, 1). The
     * estimate is corrected off-by-one exactly against the bignums. Positioning
     * depends only on the value, so it is done once for every precision. */
    DtoaBig A = R, B = S;
    double lv = prism_m_log10((double)f) + (double)e * PRISM_LOG10_2;
    int k = (int)ceil(lv - 1e-10);
    if (k >= 0) {
        dtoa_big_mul_pow10(&B, k);
    } else {
        dtoa_big_mul_pow10(&A, -k);
    }
    for (;;) { /* pull below 1 */
        if (dtoa_big_cmp(&A, &B) >= 0) {
            dtoa_big_mul_small(&B, 10);
            k++;
        } else {
            break;
        }
    }
    for (;;) { /* push to at least 1/10 so the leading digit is nonzero */
        DtoaBig a10 = A;
        dtoa_big_mul_small(&a10, 10);
        if (dtoa_big_cmp(&a10, &B) < 0) {
            dtoa_big_mul_small(&A, 10);
            k--;
        } else {
            break;
        }
    }
    int base_e10 = k - 1;

    for (int p = 1; p <= PRISM_FLOAT_MAX_DIGITS; p++) {
        /* Emit p digits of A/B, correctly rounded half-to-even, into `digits`. */
        DtoaBig cur = A, den = B;
        for (int i = 0; i < p; i++) {
            dtoa_big_mul_small(&cur, 10);
            int dig = 0;
            while (dtoa_big_cmp(&cur, &den) >= 0) {
                dtoa_big_sub(&cur, &den);
                dig++;
            }
            digits[i] = (char)('0' + dig);
        }
        /* Round the p-th digit on the remainder `cur`: 2*cur vs den, ties even. */
        DtoaBig twice = cur;
        dtoa_big_mul_small(&twice, 2);
        int c = dtoa_big_cmp(&twice, &den);
        int e10_p = base_e10;
        if (c > 0 || (c == 0 && ((digits[p - 1] - '0') & 1))) {
            int i = p - 1;
            while (i >= 0 && digits[i] == '9') {
                digits[i] = '0';
                i--;
            }
            if (i < 0) {
                /* 999..9 carried to 1000..0: the p-digit significand is "1"
                 * followed by p-1 zeros, one decimal place higher. */
                digits[0] = '1';
                for (int j = 1; j < p; j++) digits[j] = '0';
                e10_p++;
            } else {
                digits[i]++;
            }
        }
        /* Reconstruct the exact p-digit integer (17 digits fit a u64). */
        uint64_t F = 0;
        for (int i = 0; i < p; i++) F = F * 10 + (uint64_t)(digits[i] - '0');

        /* Round-trip: does F * 10^(e10_p - (p-1)) round back to exactly d? It does
         * iff it lands strictly inside the rounding interval, or on a boundary
         * that ties to the even significand. p == 17 always round-trips. */
        int g = e10_p - (p - 1);
        int ch = dtoa_cmp_decimal(F, g, &hi_num, &S);
        int cl = dtoa_cmp_decimal(F, g, &lo_num, &S);
        int round_trips =
            (cl > 0 && ch < 0) || (even && (ch == 0 || cl == 0)) || p == PRISM_FLOAT_MAX_DIGITS;
        if (round_trips) {
            /* At the minimal p a trailing zero cannot occur (it would mean p-1
             * already round-tripped); drop one defensively to match `fmt_g`. */
            int cnt = p;
            while (cnt > 1 && digits[cnt - 1] == '0') cnt--;
            *nd = cnt;
            *e10 = e10_p;
            return;
        }
    }
}

/* Shortest decimal that round-trips back to `d`, laid out like a Python `repr`:
 * full precision with no truncation, scientific notation only when the decimal
 * exponent falls outside [-4, 16). This must stay byte-identical to the
 * interpreter's `fmt_g` (src/eval) and the Lean oracle's `fmtG` (models), which
 * are differentially tested against this runtime. Because the digits are the
 * FEWEST that round-trip, the last digit is never 0, so no trailing zeros ever
 * need stripping. */
/* Buffer size every caller of prism_fmt_float must provide; 17 significant
 * digits plus sign, point, and `e+XXX` never exceed this. */
#define PRISM_FLOAT_BUF 64

static int prism_fmt_float(double d, char *out) {
    int o = 0;
    if (isnan(d)) {
        memcpy(out, "nan", sizeof "nan");
        return 3;
    }
    if (isinf(d)) {
        if (d < 0) {
            memcpy(out, "-inf", sizeof "-inf");
            return 4;
        }
        memcpy(out, "inf", sizeof "inf");
        return 3;
    }
    if (d == 0.0) {
        if (signbit(d)) {
            memcpy(out, "-0", sizeof "-0");
            return 2;
        }
        out[0] = '0';
        return 1;
    }

    int neg = signbit(d);
    char digits[20] = {0};
    int nd = 0, e10 = 0;
    prism_shortest_digits(neg ? -d : d, digits, &nd, &e10);

    if (neg) out[o++] = '-';
    if (e10 >= -4 && e10 < 16) {
        if (e10 >= 0) {
            int k = e10 + 1;
            for (int i = 0; i < k; i++) out[o++] = i < nd ? digits[i] : '0';
            if (nd > k) {
                out[o++] = '.';
                for (int i = k; i < nd; i++) out[o++] = digits[i];
            }
        } else {
            out[o++] = '0';
            out[o++] = '.';
            for (int i = 0; i < -e10 - 1; i++) out[o++] = '0';
            for (int i = 0; i < nd; i++) out[o++] = digits[i];
        }
    } else {
        out[o++] = digits[0];
        if (nd > 1) {
            out[o++] = '.';
            for (int i = 1; i < nd; i++) out[o++] = digits[i];
        }
        o += snprintf(out + o, PRISM_FLOAT_BUF - (size_t)o, "e%c%02d", e10 < 0 ? '-' : '+',
                      e10 < 0 ? -e10 : e10);
    }
    return o;
}

long prism_show_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    char out[PRISM_FLOAT_BUF];
    int o = prism_fmt_float(d, out);
    return prism_str_lit(out, o);
}

/* `print` of a float goes through the same shortest-round-trip formatter as
 * `show_float`, so native `print(x)` agrees with the interpreter and with
 * native `print(show_float(x))` instead of C `printf("%g")`'s 6-digit form. */
void prism_print_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    char out[PRISM_FLOAT_BUF];
    int o = prism_fmt_float(d, out);
    fwrite(out, 1, (size_t)o, stdout);
}

long prism_parse_float(long s) {
    // Mirror the interpreter's `s.trim().parse::<f64>()`: the whole trimmed
    // string must be a valid decimal float, else 0.0. strtod alone diverges by
    // accepting trailing garbage (`3.14x` -> 3.14) and hex (`0x10` -> 16), which
    // the Rust parser rejects.
    const char *data = prism_str_data(s);
    while (isspace((unsigned char)*data)) data++;
    const char *digits = data + (*data == '+' || *data == '-' ? 1 : 0);
    int hex = digits[0] == '0' && (digits[1] == 'x' || digits[1] == 'X');
    char *end;
    double d = strtod(data, &end);
    if (hex || end == data) {
        d = 0.0;
    } else {
        while (isspace((unsigned char)*end)) end++;
        if (*end != '\0') d = 0.0;
    }
    long bits;
    memcpy(&bits, &d, 8);
    return prism_box(bits);
}

/* The boxed-float binary transcendentals. Each unpacks two boxed doubles, calls
 * the owned `prism_m_*` implementation, and reboxes; native codegen lowers the
 * corresponding builtins to these. Determinism rides on the vendored libm, not
 * the system one. */
static long prism_float_binop(long a, long b, double (*f)(double, double)) {
    double x, y;
    memcpy(&x, &a, 8);
    memcpy(&y, &b, 8);
    double r = f(x, y);
    long bits;
    memcpy(&bits, &r, 8);
    return prism_box(bits);
}

long prism_pow_float(long a, long b) { return prism_float_binop(a, b, prism_m_pow); }
long prism_atan2(long a, long b) { return prism_float_binop(a, b, prism_m_atan2); }
long prism_hypot(long a, long b) { return prism_float_binop(a, b, prism_m_hypot); }
long prism_fmod(long a, long b) { return prism_float_binop(a, b, prism_m_fmod); }

long prism_show_float_prec(long f, long digits) {
    double d;
    memcpy(&d, &f, 8);
    char out[PRISM_FLOAT_BUF];
    if (isnan(d) || isinf(d)) {
        int o = prism_fmt_float(d, out);
        return prism_str_lit(out, o);
    }

    long requested = digits < 0 ? 0 : digits;
    int neg = signbit(d);
    double x = neg ? -d : d;

    uint64_t bits;
    memcpy(&bits, &x, sizeof bits);
    int be = (int)((bits >> PRISM_F64_MANT_BITS) & 0x7ff);
    uint64_t frac = bits & (PRISM_F64_HIDDEN - 1);
    uint64_t sig;
    int e;
    if (be == 0) {
        sig = frac;
        e = PRISM_F64_MIN_EXP;
    } else {
        sig = frac | PRISM_F64_HIDDEN;
        e = be - PRISM_F64_EXP_BIAS;
    }

    DtoaBig q;
    int scale = 0;
    if (sig == 0) {
        dtoa_big_set_u64(&q, 0);
    } else if (e >= 0) {
        dtoa_big_set_u64(&q, sig);
        dtoa_big_shl(&q, e);
    } else {
        scale = requested < (long)(-e) ? (int)requested : -e;
        DtoaBig num;
        dtoa_big_set_u64(&num, sig);
        dtoa_big_mul_pow10(&num, scale);
        q = dtoa_big_div_pow2_round(&num, -e);
    }

    char dec[1600];
    int nd = dtoa_big_to_dec(&q, dec);
    int int_len = nd - scale;
    int o = 0;
    if (neg) out[o++] = '-';
    if (int_len > 0) {
        for (int i = 0; i < int_len && o < PRISM_FLOAT_BUF - 1; i++) {
            out[o++] = i < nd ? dec[i] : '0';
        }
    } else if (o < PRISM_FLOAT_BUF - 1) {
        out[o++] = '0';
    }
    if (requested > 0 && o < PRISM_FLOAT_BUF - 1) out[o++] = '.';
    for (long i = 0; i < requested && o < PRISM_FLOAT_BUF - 1; i++) {
        int pos = int_len + (int)i;
        char c = (pos >= 0 && pos < nd) ? dec[pos] : '0';
        out[o++] = c;
    }
    return prism_str_lit(out, o);
}
