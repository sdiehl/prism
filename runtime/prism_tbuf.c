/* Unboxed typed buffers: raw 8-byte words with the rc==1 in-place discipline,
 * copied from prism_array_set/prism_buf_set. See prism_tbuf.h. */
#include "prism_tbuf.h"
#include "prism_mem.h"

/* The length word sits first in the payload; the element words follow it. */
#define PRISM_TBUF_LEN_W (PRISM_HDR_WORDS)
#define PRISM_TBUF_ELEM0 (PRISM_HDR_WORDS + 1)

_Noreturn void prism_tbuf_oob(void) {
    fprintf(stderr, "fatal: buffer index out of bounds\n");
    exit(1);
}

static long tbuf_len(long *p) {
    return p[PRISM_TBUF_LEN_W];
}
static void tbuf_setlen(long *p, long l) {
    p[PRISM_TBUF_LEN_W] = l;
}
static long *tbuf_data(long *p) {
    return p + PRISM_TBUF_ELEM0;
}

/* Allocate a buffer of `n` raw element words with length n: the word count is the
   length word plus n element words. Checked non-negative and against overflow. */
static long *tbuf_alloc(long n) {
    if (n < 0) prism_tbuf_oob();
    size_t words;
    if (__builtin_add_overflow((size_t)n, (size_t)1, &words)) abort();
    long *p = prism_alloc((long)words);
    p[PRISM_TAG_W] = PRISM_TBUF_TAG;
    tbuf_setlen(p, n);
    return p;
}

long prism_tbuf_new(long n, long init) {
    long *p = tbuf_alloc(n);
    for (long i = 0; i < n; i++) tbuf_data(p)[i] = init;
    return (long)p;
}

long prism_tbuf_len(long b) {
    return tbuf_len((long *)b); /* raw count; the call site retags it */
}

long prism_tbuf_get(long b, long i) {
    long *p = (long *)b;
    if (i < 0 || i >= tbuf_len(p)) prism_tbuf_oob();
    /* The raw word is boxed into an ordinary Int/Float cell; the borrowed buffer
       is dropped by the caller, so the returned element carries its own ref. */
    return prism_box(tbuf_data(p)[i]);
}

long prism_tbuf_set(long b, long i, long x) {
    long *p = (long *)b;
    long len = tbuf_len(p);
    if (i < 0 || i >= len) prism_tbuf_oob();
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: write in place (FBIP) */
        tbuf_data(p)[i] = x;
        prism_rc_inc(b); /* survive the caller's drop of the borrowed arg */
        return b;
    }
    long *q = tbuf_alloc(len); /* shared: copy then set */
    memcpy(tbuf_data(q), tbuf_data(p), (size_t)len * sizeof(long));
    tbuf_data(q)[i] = x;
    return (long)q;
}

/* A buffer equal to `dst` but with `dst[dstart..dstart+n)` overwritten by
   `src[sstart..sstart+n)`. Written in place when dst is uniquely owned, else onto
   a fresh copy. Both ranges are bounds-checked without overflowing. `src` is only
   read; overlapping ranges within one buffer are handled (memmove). */
long prism_tbuf_blit(long dst, long dstart, long src, long sstart, long n) {
    long *d = (long *)dst;
    long *s = (long *)src;
    long dlen = tbuf_len(d), slen = tbuf_len(s);
    if (n < 0 || dstart < 0 || sstart < 0) prism_tbuf_oob();
    if (dstart > dlen || n > dlen - dstart) prism_tbuf_oob();
    if (sstart > slen || n > slen - sstart) prism_tbuf_oob();
    if (d[PRISM_RC_W] == 1) { /* uniquely owned: blit in place */
        memmove(tbuf_data(d) + dstart, tbuf_data(s) + sstart, (size_t)n * sizeof(long));
        prism_rc_inc(dst);
        return dst;
    }
    long *q = tbuf_alloc(dlen); /* shared: copy then blit */
    memcpy(tbuf_data(q), tbuf_data(d), (size_t)dlen * sizeof(long));
    memmove(tbuf_data(q) + dstart, tbuf_data(s) + sstart, (size_t)n * sizeof(long));
    return (long)q;
}
