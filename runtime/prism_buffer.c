/* Unboxed byte buffers, the storage under `Bytes`. A buffer is an ordinary cell
   { rc, tag=PRISM_BUF_TAG, arity, len, bytes... }: a byte length word followed by
   a contiguous raw-u8 region rounded up to whole words. The distinct tag makes
   prism_rc_dec and prism_reuse_token treat the payload as opaque (no child cells
   to recurse into), so reference counting and the leak balance apply unchanged.
   Every op BORROWS its cell args (the call site drops them afterward); an op that
   keeps or returns a buffer inc's its refcount so it survives that drop. The
   rc==1 in-place / shared-copy discipline mirrors prism_array_set exactly, so a
   uniquely-owned buffer is mutated in place and a shared one is copied, keeping
   value semantics either way. Byte arguments arrive as raw longs and are masked
   into 0..255; indices arrive raw. */
#include "prism_buffer.h"
#include "prism_array.h"
#include "prism_mem.h"
#include "prism_string.h"

/* The length word sits first in the payload; the bytes follow it. */
#define PRISM_BUF_LEN_W (PRISM_HDR_WORDS)
#define PRISM_BUF_DATA_W (PRISM_HDR_WORDS + 1)

_Noreturn void prism_buf_oob(void) {
    fprintf(stderr, "fatal: buffer index out of bounds\n");
    exit(1);
}

static long buf_len(long *p) {
    return p[PRISM_BUF_LEN_W];
}
static void buf_setlen(long *p, long l) {
    p[PRISM_BUF_LEN_W] = l;
}
static long buf_cap(long *p) {
    return (p[PRISM_ARITY_W] - 1) * 8; /* payload words minus the length word */
}
static unsigned char *buf_data(long *p) {
    return (unsigned char *)(p + PRISM_BUF_DATA_W);
}

/* Allocate a buffer with room for `cap_bytes` bytes and length 0. The word count
   is the length word plus the byte capacity rounded up; computed in size_t so a
   near-LONG_MAX capacity cannot overflow before prism_cell_bytes re-checks it. */
static long *buf_alloc(long cap_bytes) {
    if (cap_bytes < 0) abort();
    size_t span, capw;
    if (__builtin_add_overflow((size_t)cap_bytes, (size_t)7, &span)) abort();
    capw = span / 8;
    size_t words;
    if (__builtin_add_overflow(capw, (size_t)1, &words)) abort();
    long *p = prism_alloc((long)words);
    p[PRISM_TAG_W] = PRISM_BUF_TAG;
    buf_setlen(p, 0);
    return p;
}

long prism_buf_empty(void) {
    return (long)buf_alloc(0);
}

long prism_buf_new(long n, long init) {
    long *p = buf_alloc(n);
    memset(buf_data(p), (int)(init & 0xFF), (size_t)n);
    buf_setlen(p, n);
    return (long)p;
}

long prism_buf_len(long b) {
    return buf_len((long *)b); /* raw count; the call site retags it */
}

long prism_buf_get(long b, long i) {
    long *p = (long *)b;
    if (i < 0 || i >= buf_len(p)) prism_buf_oob();
    return (long)buf_data(p)[i]; /* raw byte; the call site retags it */
}

long prism_buf_set(long b, long i, long x) {
    long *p = (long *)b;
    long len = buf_len(p);
    if (i < 0 || i >= len) prism_buf_oob();
    unsigned char v = (unsigned char)(x & 0xFF);
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: write in place (FBIP) */
        buf_data(p)[i] = v;
        prism_rc_inc(b); /* survive the caller's drop of the borrowed arg */
        return b;
    }
    long *q = buf_alloc(len); /* shared: copy then set */
    memcpy(buf_data(q), buf_data(p), (size_t)len);
    buf_setlen(q, len);
    buf_data(q)[i] = v;
    return (long)q;
}

long prism_buf_push(long b, long x) {
    long *p = (long *)b;
    long len = buf_len(p), cap = buf_cap(p);
    unsigned char v = (unsigned char)(x & 0xFF);
    if (p[PRISM_RC_W] == 1 && len < cap) { /* room and unique: append in place */
        buf_data(p)[len] = v;
        buf_setlen(p, len + 1);
        prism_rc_inc(b);
        return b;
    }
    /* Full (grow by doubling) or merely shared (copy at the current capacity): only
       double when there is genuinely no room, so a shared-but-unfilled buffer copied
       every push does not blow its capacity up exponentially. Mirrors prism_array_push. */
    long ncap = len < cap ? cap : (cap < 8 ? 8 : cap * 2);
    long *q = buf_alloc(ncap);
    memcpy(buf_data(q), buf_data(p), (size_t)len);
    buf_data(q)[len] = v;
    buf_setlen(q, len + 1);
    return (long)q;
}

/* A fresh buffer holding the bytes [start, start+len) clamped to the source, so a
   slice past either end yields the in-bounds remainder (or empty), never a trap. */
long prism_buf_slice(long b, long start, long len) {
    long *p = (long *)b;
    long blen = buf_len(p);
    if (start < 0) start = 0;
    if (start > blen) start = blen;
    if (len < 0) len = 0;
    long avail = blen - start;
    long take = len < avail ? len : avail;
    long *q = buf_alloc(take);
    memcpy(buf_data(q), buf_data(p) + start, (size_t)take);
    buf_setlen(q, take);
    return (long)q;
}

long prism_buf_cat(long a, long b) {
    long *pa = (long *)a, *pb = (long *)b;
    long la = buf_len(pa), lb = buf_len(pb);
    long total;
    if (__builtin_add_overflow(la, lb, &total)) abort();
    long *q = buf_alloc(total);
    memcpy(buf_data(q), buf_data(pa), (size_t)la);
    memcpy(buf_data(q) + la, buf_data(pb), (size_t)lb);
    buf_setlen(q, total);
    return (long)q;
}

long prism_buf_eq(long a, long b) {
    long *pa = (long *)a, *pb = (long *)b;
    long la = buf_len(pa), lb = buf_len(pb);
    if (la != lb) return 0;
    return memcmp(buf_data(pa), buf_data(pb), (size_t)la) == 0 ? 1 : 0;
}

long prism_buf_cmp(long a, long b) {
    long *pa = (long *)a, *pb = (long *)b;
    long la = buf_len(pa), lb = buf_len(pb);
    long n = la < lb ? la : lb;
    int c = memcmp(buf_data(pa), buf_data(pb), (size_t)n);
    if (c < 0) return -1;
    if (c > 0) return 1;
    return la < lb ? -1 : la > lb ? 1 : 0;
}

long prism_buf_hash(long b) {
    long *p = (long *)b;
    return prism_blake3_bytes(buf_data(p), buf_len(p));
}

long prism_buf_of_string(long s) {
    long n = prism_str_len_bytes(s);
    long *q = buf_alloc(n);
    memcpy(buf_data(q), prism_str_data(s), (size_t)n);
    buf_setlen(q, n);
    return (long)q;
}

long prism_string_of_buf(long b) {
    long *p = (long *)b;
    return prism_string_of_raw(buf_data(p), buf_len(p));
}

long prism_buf_utf8_valid(long b) {
    long *p = (long *)b;
    return (long)prism_utf8_valid(buf_data(p), buf_len(p)); /* raw bool; retagged */
}

const unsigned char *prism_buf_ptr(long b) {
    return buf_data((long *)b);
}
