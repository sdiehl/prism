/* Growable arrays and the array-to-string conversions. */
#include "prism_array.h"
#include "prism_mem.h"
#include "prism_string.h"

_Noreturn void prism_array_oob(void) {
    fprintf(stderr, "fatal: array index out of bounds\n");
    exit(1);
}

/* Growable polymorphic array as an ordinary cell
   { rc, tag=0, arity=cap+1, len, elem0..elem_{cap-1} }, so prism_rc_dec already
   recurses into it: the length word is stored odd-tagged (skipped as an
   immediate), live slots hold elements, spare slots hold 0 (also skipped). All
   ops BORROW their cell args (the call site drops them afterward), so each
   retains a ref by inc-ing what it stores or returns. Indices arrive raw. */
#define PRISM_ARR_ELEM0 (PRISM_HDR_WORDS + 1)
static long arr_len(long *p) {
    return p[PRISM_HDR_WORDS] >> 1;
}
static void arr_setlen(long *p, long l) {
    p[PRISM_HDR_WORDS] = (l << 1) | 1;
}
static long arr_cap(long *p) {
    return p[PRISM_ARITY_W] - 1;
}

long prism_array_empty(void) {
    long *p = prism_alloc(1); /* cap 0: just the length word */
    arr_setlen(p, 0);
    return (long)p;
}

long prism_array_new(long n, long init) {
    long *p = prism_alloc(n + 1); /* cap = len = n */
    arr_setlen(p, n);
    for (long i = 0; i < n; i++) {
        prism_rc_inc(init);
        p[PRISM_ARR_ELEM0 + i] = init;
    }
    return (long)p;
}

long prism_array_len(long a) {
    return arr_len((long *)a); /* raw count; the call site retags it */
}

long prism_array_get(long a, long i) {
    long *p = (long *)a;
    if (i < 0 || i >= arr_len(p)) prism_array_oob();
    long e = p[PRISM_ARR_ELEM0 + i];
    prism_rc_inc(e); /* returned ref; the borrowed array is dropped by the caller */
    return e;
}

long prism_array_set(long a, long i, long x) {
    long *p = (long *)a;
    long len = arr_len(p);
    if (i < 0 || i >= len) prism_array_oob();
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: write in place (FBIP) */
        prism_rc_dec(p[PRISM_ARR_ELEM0 + i]);
        prism_rc_inc(x);
        p[PRISM_ARR_ELEM0 + i] = x;
        prism_rc_inc(a); /* survive the caller's drop of the borrowed arg */
        return a;
    }
    long *q = prism_alloc(len + 1); /* shared: copy compactly then set */
    arr_setlen(q, len);
    for (long j = 0; j < len; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    prism_rc_dec(q[PRISM_ARR_ELEM0 + i]);
    prism_rc_inc(x);
    q[PRISM_ARR_ELEM0 + i] = x;
    return (long)q;
}

long prism_array_push(long a, long x) {
    long *p = (long *)a;
    long len = arr_len(p), cap = arr_cap(p);
    if (p[PRISM_RC_W] == 1 && len < cap) { /* room and unique: append in place */
        prism_rc_inc(x);
        p[PRISM_ARR_ELEM0 + len] = x;
        arr_setlen(p, len + 1);
        prism_rc_inc(a); /* survive the caller's drop */
        return a;
    }
    /* full (grow, doubling) or shared (copy): one fresh array of the new size */
    long ncap = len < cap ? cap : (cap < 1 ? 1 : cap * 2);
    long *q = prism_alloc(ncap + 1);
    arr_setlen(q, len + 1);
    for (long j = 0; j < len; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    prism_rc_inc(x);
    q[PRISM_ARR_ELEM0 + len] = x;
    for (long j = len + 1; j < ncap; j++) q[PRISM_ARR_ELEM0 + j] = 0; /* skip-safe spare */
    return (long)q;
}

long prism_array_pop(long a) {
    long *p = (long *)a;
    long len = arr_len(p);
    if (len <= 0) prism_array_oob();
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: drop the last in place */
        prism_rc_dec(p[PRISM_ARR_ELEM0 + len - 1]);
        p[PRISM_ARR_ELEM0 + len - 1] = 0; /* skip-safe spare */
        arr_setlen(p, len - 1);
        prism_rc_inc(a);
        return a;
    }
    long *q = prism_alloc(len); /* shared: copy len-1 elements */
    arr_setlen(q, len - 1);
    for (long j = 0; j < len - 1; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    return (long)q;
}

/* Concatenate every string in an array into one fresh string with a single
   allocation. Borrows the array (the caller drops it and its elements). */
long prism_string_of_array(long arr) {
    long *p = (long *)arr;
    long n = arr_len(p);
    long total = 0;
    for (long i = 0; i < n; i++) total += prism_str_len_bytes(p[PRISM_ARR_ELEM0 + i]);
    long *out = prism_str_alloc(total);
    char *o = (char *)(out + PRISM_HDR_WORDS);
    long off = 0;
    for (long i = 0; i < n; i++) {
        long s = p[PRISM_ARR_ELEM0 + i];
        long len = prism_str_len_bytes(s);
        memcpy(o + off, prism_str_data(s), (size_t)len);
        off += len;
    }
    o[total] = 0;
    return (long)out;
}

/* Classify the UTF-8 sequence at raw[i..n). On a well-formed sequence set *adv
 * to its length and return 1. On an ill-formed one set *adv to the length of the
 * maximal valid subpart (>=1, clamped to the bytes remaining when the sequence
 * runs off the end) and return 0; the caller emits a single U+FFFD and skips
 * *adv bytes. This is Rust's `from_utf8_lossy` decoder (Unicode Table 3-7 with
 * substitution of maximal subparts), which the interpreter uses via
 * `String::from_utf8_lossy`; the two must stay byte-identical. */
static int prism_utf8_seq(const unsigned char *raw, long i, long n, long *adv) {
    unsigned char b0 = raw[i];
    if (b0 < 0x80) {
        *adv = 1;
        return 1;
    }
    if (b0 < 0xC2 || b0 > 0xF4) { /* 0x80..0xC1 and 0xF5..0xFF are invalid leads */
        *adv = 1;
        return 0;
    }
    /* Continuation-byte ranges depend on the lead: E0/ED and F0/F4 narrow the
     * second byte to exclude overlong encodings and surrogates (Table 3-7). */
    long lo1 = 0x80, hi1 = 0xBF;
    long width;
    if (b0 < 0xE0) {
        width = 2;
    } else if (b0 < 0xF0) {
        width = 3;
        if (b0 == 0xE0)
            lo1 = 0xA0;
        else if (b0 == 0xED)
            hi1 = 0x9F;
    } else {
        width = 4;
        if (b0 == 0xF0)
            lo1 = 0x90;
        else if (b0 == 0xF4)
            hi1 = 0x8F;
    }
    for (long k = 1; k < width; k++) {
        if (i + k >= n) { /* incomplete trailing sequence: one U+FFFD for the rest */
            *adv = n - i;
            return 0;
        }
        unsigned char b = raw[i + k];
        long lo = k == 1 ? lo1 : 0x80;
        long hi = k == 1 ? hi1 : 0xBF;
        if (b < lo || b > hi) {
            *adv = k; /* the k valid bytes are the maximal subpart */
            return 0;
        }
    }
    *adv = width;
    return 1;
}

/* True when a raw byte span is well-formed UTF-8 (Table 3-7): every sequence
   decodes with no maximal-subpart substitution, so the span is exactly what
   Rust's `str::from_utf8` accepts. The String/Bytes boundary gates on this before
   admitting bytes as a String, and the interpreter checks the identical property. */
int prism_utf8_valid(const unsigned char *raw, long n) {
    for (long i = 0; i < n;) {
        long adv;
        if (!prism_utf8_seq(raw, i, n, &adv)) return 0;
        i += adv;
    }
    return 1;
}

/* Build a string from a raw byte span, replacing any ill-formed UTF-8 with U+FFFD
   so the result is byte-identical to the interpreter's lossy decode. Shared by the
   Int-array path below and the buffer module's prism_string_of_buf, so the single
   lossy decoder has one home. Does not take ownership of `raw`. */
long prism_string_of_raw(const unsigned char *raw, long n) {
    /* Two passes over the same deterministic decode: size, then fill. A U+FFFD
     * (0xEF 0xBF 0xBD) is three bytes, so the output can outgrow the input. */
    long out_len = 0;
    for (long i = 0; i < n;) {
        long adv;
        out_len += prism_utf8_seq(raw, i, n, &adv) ? adv : 3;
        i += adv;
    }
    long *out = prism_str_alloc(out_len);
    char *o = (char *)(out + PRISM_HDR_WORDS);
    long off = 0;
    for (long i = 0; i < n;) {
        long adv;
        if (prism_utf8_seq(raw, i, n, &adv)) {
            memcpy(o + off, raw + i, (size_t)adv);
            off += adv;
        } else {
            o[off] = (char)0xEF;
            o[off + 1] = (char)0xBF;
            o[off + 2] = (char)0xBD;
            off += 3;
        }
        i += adv;
    }
    o[out_len] = 0;
    return (long)out;
}

/* Build a string from an array of byte values (each a small Int 0..255, stored
   tagged so `>> 1` recovers it). Borrows the array. */
long prism_string_of_bytes(long arr) {
    long *p = (long *)arr;
    long n = arr_len(p);
    unsigned char *raw = malloc((size_t)(n > 0 ? n : 1));
    if (!raw) abort();
    for (long i = 0; i < n; i++) raw[i] = (unsigned char)((p[PRISM_ARR_ELEM0 + i] >> 1) & 0xFF);
    long out = prism_string_of_raw(raw, n);
    free(raw);
    return out;
}
