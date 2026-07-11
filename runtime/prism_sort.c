/* The polymorphic sort primitive: a stable merge sort with a radix fast path. */
#include "prism_sort.h"
#include "prism_int.h"
#include "prism_mem.h"
#include "prism_string.h"

/* ---- native sort kernel (the `sort`/`sort_by_ord` fast path) ---------------
 * `kind` selects how to compare two element words off the cons spine:
 *   0 Integer (tagged-or-bignum, via prism_rt_int_cmp), 1 I64, 2 U64, 3 Float,
 * the last three boxed (one payload word). Floats use the IEEE total order so
 * the result matches the interpreter's f64::total_cmp. */
static unsigned long prism_flt_key(long boxed) {
    unsigned long b = (unsigned long)prism_unbox(boxed);
    return (b >> 63) ? ~b : (b | 0x8000000000000000UL);
}

static int prism_sort_cmp(long kind, long a, long b) {
    switch (kind) {
    case 1: {
        long x = prism_unbox(a), y = prism_unbox(b);
        return (x > y) - (x < y);
    }
    case 2: {
        unsigned long x = (unsigned long)prism_unbox(a), y = (unsigned long)prism_unbox(b);
        return (x > y) - (x < y);
    }
    case 3: {
        unsigned long x = prism_flt_key(a), y = prism_flt_key(b);
        return (x > y) - (x < y);
    }
    default: {
        long c = prism_rt_int_cmp(a, b);
        return (c > 0) - (c < 0);
    }
    }
}

/* Stable bottom-up merge sort of `src` (length n), ping-ponging with `buf`;
 * returns whichever buffer holds the sorted result. The width and index
 * arithmetic runs in size_t: a list of n cells occupies at least 4n words, so
 * n (and hence 2*w) sits far below SIZE_MAX and the unsigned doubling cannot
 * wrap, where the previous signed forms were undefined at the same extremes. */
static long *prism_msort(long *src, long *buf, size_t n, long kind) {
    for (size_t w = 1; w < n; w *= 2) {
        for (size_t i = 0; i < n; i += 2 * w) {
            size_t mid = i + w < n ? i + w : n;
            size_t hi = i + 2 * w < n ? i + 2 * w : n;
            size_t a = i, b = mid, k = i;
            while (a < mid && b < hi)
                buf[k++] = prism_sort_cmp(kind, src[b], src[a]) < 0 ? src[b++] : src[a++];
            while (a < mid) buf[k++] = src[a++];
            while (b < hi) buf[k++] = src[b++];
        }
        long *t = src;
        src = buf;
        buf = t;
    }
    return src;
}

/* The unsigned radix key for a fixed-width element so plain ascending u64 order
 * reproduces the element's order: flip the sign bit for signed i64, pass u64
 * through, and use the IEEE total-order transform for floats. */
static unsigned long prism_sort_key(long kind, long h) {
    switch (kind) {
    case 1: return (unsigned long)prism_unbox(h) ^ 0x8000000000000000UL;
    case 2: return (unsigned long)prism_unbox(h);
    case 3: return prism_flt_key(h);
    default: return 0;
    }
}

/* Stable LSD radix sort (eight byte passes) of `heads` by parallel `keys`. Eight
 * passes is even, so the sorted result lands back in `heads`/`keys`. */
static void prism_radix(long *heads, unsigned long *keys, size_t n) {
    long *th = malloc(n * sizeof(long));
    unsigned long *tk = malloc(n * sizeof(unsigned long));
    if (!th || !tk) abort();
    long *sh = heads, *dh = th;
    unsigned long *sk = keys, *dk = tk;
    for (int shift = 0; shift < 64; shift += 8) {
        size_t count[256] = {0};
        for (size_t i = 0; i < n; i++) count[(sk[i] >> shift) & 0xff]++;
        size_t sum = 0;
        for (int b = 0; b < 256; b++) {
            size_t c = count[b];
            count[b] = sum;
            sum += c;
        }
        for (size_t i = 0; i < n; i++) {
            size_t pos = count[(sk[i] >> shift) & 0xff]++;
            dh[pos] = sh[i];
            dk[pos] = sk[i];
        }
        long *t = sh;
        sh = dh;
        dh = t;
        unsigned long *u = sk;
        sk = dk;
        dk = u;
    }
    free(th);
    free(tk);
}

/* Borrows `list` (builtin args are dropped by the caller) and returns a sorted
 * list. Fixed-width elements use radix; Integer keeps the bignum-aware merge.
 * When the spine is uniquely owned (every cell rc == 1) the cells are reused in
 * place -- the sorted heads are written back into the existing spine, no
 * allocation -- and the result aliases `list`, which the caller drops twice (the
 * borrowed arg and the returned value), so its rc is bumped once to balance.
 * A shared spine falls back to a fresh copy that shares each element (one
 * rc_inc). Either way the live-cell balance holds. Cons/Nil tags are read off
 * the input spine, so no constructor layout is baked in here. */
long prism_sort_prim(long kind, long list) {
    kind >>= 1; /* untag the small-int kind */
    /* The spine length counts in size_t: a list of n cells occupies at least
     * 4n words, so the count sits far below SIZE_MAX and cannot wrap where a
     * signed counter would be undefined; it also feeds mallocs directly. */
    size_t n = 0;
    for (long q = list; !(q & 1) && q && ((long *)q)[PRISM_ARITY_W] == 2;
         q = ((long *)q)[PRISM_HDR_WORDS + 1])
        n++;

    long *cells = n ? malloc(n * sizeof(long)) : NULL;
    long *heads = n ? malloc(n * sizeof(long)) : NULL;
    if (n && (!cells || !heads)) abort();
    long cons_tag = 0, p = list, unique = 1;
    size_t i = 0;
    while (!(p & 1) && p && ((long *)p)[PRISM_ARITY_W] == 2) {
        long *cell = (long *)p;
        if (i == 0) cons_tag = cell[PRISM_TAG_W];
        if (cell[PRISM_RC_W] != 1) unique = 0;
        cells[i] = p;
        heads[i] = cell[PRISM_HDR_WORDS + 0];
        i++;
        p = cell[PRISM_HDR_WORDS + 1];
    }
    long nil_tag = (!(p & 1) && p) ? ((long *)p)[PRISM_TAG_W] : 0;

    if (n > 1) {
        if (kind == 0) {
            long *buf = malloc(n * sizeof(long));
            if (!buf) abort();
            long *res = prism_msort(heads, buf, n, kind);
            if (res != heads) memcpy(heads, res, n * sizeof(long));
            free(buf);
        } else {
            unsigned long *keys = malloc(n * sizeof(unsigned long));
            if (!keys) abort();
            for (size_t j = 0; j < n; j++) keys[j] = prism_sort_key(kind, heads[j]);
            prism_radix(heads, keys, n);
            free(keys);
        }
    }

    long ret;
    if (unique) {
        for (size_t j = 0; j < n; j++) ((long *)cells[j])[PRISM_HDR_WORDS + 0] = heads[j];
        prism_rc_inc(list);
        ret = list;
    } else {
        long *nil = prism_alloc(0);
        nil[PRISM_TAG_W] = nil_tag;
        long acc = (long)nil;
        for (size_t j = n; j-- > 0;) {
            prism_rc_inc(heads[j]);
            long *c = prism_alloc(2);
            c[PRISM_TAG_W] = cons_tag;
            c[PRISM_HDR_WORDS + 0] = heads[j];
            c[PRISM_HDR_WORDS + 1] = acc;
            acc = (long)c;
        }
        ret = acc;
    }
    free(cells);
    free(heads);
    return ret;
}
