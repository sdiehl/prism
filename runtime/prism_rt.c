/* Portability: requires GCC >= 5 or Clang >= 3.8.
 * Uses __attribute__((destructor)) for the leak/reuse/effop report hooks and
 * __builtin_add_overflow/sub/mul for checked arithmetic. */

/* Opt-in mimalloc (cargo --features mimalloc): route every libc allocation
 * through mi_* so alloc/free pairing flips together. Must precede any use. The
 * symbols come from the libmimalloc-sys crate; declare them here so no mimalloc
 * header or in-tree source is needed. */
#ifdef PRISM_MIMALLOC
#include <stddef.h>
extern void *mi_malloc(size_t);
extern void mi_free(void *);
extern void *mi_realloc(void *, size_t);
extern void *mi_calloc(size_t, size_t);
#define malloc(n) mi_malloc(n)
#define free(p) mi_free(p)
#define realloc(p, n) mi_realloc(p, n)
#define calloc(a, b) mi_calloc(a, b)
#endif

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

/* Object layout: { i64 refcount, i64 tag, i64 arity, i64 fields[n] }
 * arity is the field count, letting prism_rc_dec recurse into children.
 * The word indices below are cross-checked against the byte offsets the
 * code generator uses by the `layout_matches_runtime` test in emit.rs. */
#define PRISM_RC_W 0
#define PRISM_TAG_W 1
#define PRISM_ARITY_W 2
#define PRISM_HDR_WORDS 3

/* Live-cell balance, the box-1 acceptance oracle: every prism_alloc bumps it,
 * every freed cell drops it. With PRISM_CHECK_LEAKS set, a destructor prints the
 * final balance to stderr at exit; a clean run reports zero. stderr keeps stdout
 * (the parity-checked channel) untouched, so normal runs are byte-identical. */
static long prism_live_cells = 0;

__attribute__((destructor)) static void prism_leak_report(void) {
    if (getenv("PRISM_CHECK_LEAKS")) {
        fprintf(stderr, "prism: %ld cells leaked\n", prism_live_cells);
    }
}

/* Checked header+payload byte size. A hostile or computed word count must never
 * overflow the size argument to malloc: an overflow would under-allocate and the
 * subsequent field stores would write out of bounds. Reject a negative count (a
 * corrupt length) and any add/mul overflow, aborting rather than handing back an
 * undersized cell. */
static size_t prism_cell_bytes(long n_words) {
    size_t words, bytes;
    if (n_words < 0) abort();
    if (__builtin_add_overflow((size_t)PRISM_HDR_WORDS, (size_t)n_words, &words)) abort();
    if (__builtin_mul_overflow(words, (size_t)8, &bytes)) abort();
    return bytes;
}

void *prism_alloc(long n_words) {
    long *p = malloc(prism_cell_bytes(n_words));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = 0;
    p[PRISM_ARITY_W] = n_words;
    prism_live_cells++;
    return p;
}

/* Build a constructor cell { rc, tag, arity, fields... }, mirroring the inline
 * cells codegen emits (prism_alloc + tag word + field words). Tags follow the
 * ADT's declaration order, so for the prelude's `Option(a) = None | Some(a)`
 * None=0/Some=1 and `Result(a, e) = Ok(a) | Err(e)` Ok=0/Err=1. */
static long prism_ctor(long tag, long n, const long *fields) {
    long *p = prism_alloc(n);
    p[PRISM_TAG_W] = tag;
    for (long i = 0; i < n; i++) p[PRISM_HDR_WORDS + i] = fields[i];
    return (long)p;
}

/* A string is a refcounted cell { rc, tag=PRISM_STR_TAG, byte_len, utf8... }:
 * the bytes live inline after the header and are NUL-terminated for printf
 * interop. The distinct tag tells prism_rc_dec to free the cell without
 * recursing into the bytes (they are not child cells). Every string the program
 * builds, including literals (allocated fresh at each use), is a counted cell
 * that prism_rc_dec frees, so the live-cell balance includes strings. */
#define PRISM_STR_TAG 0x53545200L

/* An Integer is a sign-magnitude bignum cell { rc, tag=PRISM_BIG_TAG, n, limbs... }:
 * n is a signed limb count whose sign is the value's sign, the magnitude is |n|
 * u64 limbs little-endian starting at offset 24 with no leading zero limbs, and
 * zero is n == 0 with no limbs. Like strings, the tag tells prism_rc_dec and
 * prism_reuse_token not to recurse into the payload (limbs are not child cells). */
#define PRISM_BIG_TAG 0x42494700L

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8, "prism runtime assumes LP64");

static long *prism_str_alloc(long byte_len) {
    /* Room for the bytes plus the NUL terminator, rounded up to whole words.
     * `byte_len + 8` is computed in size_t so a near-LONG_MAX length cannot
     * overflow before prism_cell_bytes re-checks the final allocation size. */
    size_t span;
    if (byte_len < 0) abort();
    if (__builtin_add_overflow((size_t)byte_len, (size_t)8, &span)) abort();
    long words = (long)(span / 8);
    long *p = malloc(prism_cell_bytes(words));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = PRISM_STR_TAG;
    p[PRISM_ARITY_W] = byte_len;
    prism_live_cells++;
    return p;
}

static char *prism_str_data(long s) {
    return (char *)((long *)s + PRISM_HDR_WORDS);
}

static long prism_str_len_bytes(long s) {
    return ((long *)s)[PRISM_ARITY_W];
}

long prism_str_lit(const char *src, long byte_len) {
    long *p = prism_str_alloc(byte_len);
    char *d = (char *)(p + PRISM_HDR_WORDS);
    memcpy(d, src, (size_t)byte_len);
    d[byte_len] = 0;
    return (long)p;
}

static long utf8_adv(unsigned char c) {
    if (c < 0x80) return 1;
    if (c < 0xE0) return 2;
    if (c < 0xF0) return 3;
    return 4;
}

/* Advance clamped to the byte length: read_file/getenv can import bytes that
 * are not valid UTF-8, and a lying lead byte must not walk past the buffer. */
static long utf8_step(const char *d, long b, long nb) {
    long a = utf8_adv((unsigned char)d[b]);
    return a > nb - b ? nb - b : a;
}

void prism_div_zero(void) {
    fprintf(stderr, "fatal: division by zero\n");
    exit(1);
}

/* Reached only on an arity bug: a closure dispatched to an apply_n with no
 * matching lambda tag. A diagnostic abort beats raw `unreachable` UB. */
void prism_apply_error(void) {
    fprintf(stderr, "fatal: closure applied at wrong arity\n");
    exit(1);
}

void prism_fatal(long s) {
    fprintf(stderr, "fatal: %s\n", prism_str_data(s));
    exit(1);
}

/* A box is an arity-0 cell whose single payload word holds one opaque i64: the
 * raw double bits for a float. Boxing makes a float a self-describing cell, so a
 * float field of a constructor is safe for prism_rc_dec to free without
 * recursing into the payload. The backends unbox at every float-op boundary. */
long prism_box(long payload) {
    long *p = prism_alloc(1);
    p[PRISM_ARITY_W] = 0;
    p[PRISM_HDR_WORDS] = payload;
    return (long)p;
}

long prism_unbox(long p) {
    return ((long *)p)[PRISM_HDR_WORDS];
}

/* inc/dec take the raw i64 value, not a pointer: immediates (low bit set) and
 * unit (zero) are skipped without a dereference, so dup/drop stay no-ops on
 * non-cell values under polymorphism. dec frees a cell's children before the
 * cell; a string cell holds inline bytes rather than child cells, so its tag
 * short-circuits the traversal. */
void prism_rc_inc(long v) {
    if ((v & 1) || !v) return;
    ((long *)v)[PRISM_RC_W]++;
}

/* Freeing is iterative via an intrusive worklist: a dead cell's rc word (now 0,
 * doubling as the NULL terminator) is reused as the next link of a pending free
 * list, so arbitrarily deep structures drop in O(1) extra space with no
 * allocation instead of recursing once per child on the C stack. */
void prism_rc_dec(long v) {
    if ((v & 1) || !v) return;
    long *p = (long *)v;
    if (--p[PRISM_RC_W] != 0) return;
    while (p) {
        long *next = (long *)p[PRISM_RC_W];
        if (p[PRISM_TAG_W] != PRISM_STR_TAG && p[PRISM_TAG_W] != PRISM_BIG_TAG) {
            long n = p[PRISM_ARITY_W];
            for (long i = 0; i < n; i++) {
                long c = p[PRISM_HDR_WORDS + i];
                if ((c & 1) || !c) continue;
                long *cp = (long *)c;
                if (--cp[PRISM_RC_W] == 0) {
                    cp[PRISM_RC_W] = (long)next;
                    next = cp;
                }
            }
        }
        free(p);
        prism_live_cells--;
        p = next;
    }
}

/* FBIP reuse (Lorenzen and Leijen, "Reference Counting with Frame-Limited
 * Reuse"): a uniquely-owned cell about to be dropped is turned into a reuse
 * token and handed to the matching constructor allocation in the same arm, so
 * the cell is overwritten in place instead of freed and re-malloced. The token
 * call recurses into the old children exactly as prism_rc_dec would, but keeps
 * the shell when rc is 1 (returning it) and returns 0 otherwise (a shared cell
 * is decremented and allocation falls back to malloc). Either way the live-cell
 * counter is untouched, so a reused cell neither leaks nor double-counts. */
static long prism_reuse_hits = 0;

__attribute__((destructor)) static void prism_reuse_report(void) {
    if (getenv("PRISM_REUSE_STATS")) {
        fprintf(stderr, "prism: %ld cells reused\n", prism_reuse_hits);
    }
}

/* Effect-op allocation counter: every EOp cell the free-monad lowering builds
 * for a `do op` bumps this. With PRISM_EFFOP_STATS set a destructor reports the
 * total to stderr, leaving stdout (the parity-checked channel) untouched, so a
 * fused pipeline can be asserted to allocate zero EOp cells while a genuinely
 * escaping effect's fallback count stays observable. */
static long prism_effop_allocs = 0;

__attribute__((destructor)) static void prism_effop_report(void) {
    if (getenv("PRISM_EFFOP_STATS")) {
        fprintf(stderr, "prism: %ld eff ops allocated\n", prism_effop_allocs);
    }
}

void prism_effop_alloc(void) { prism_effop_allocs++; }

long prism_reuse_token(long v) {
    if ((v & 1) || !v) return 0;
    long *p = (long *)v;
    if (p[PRISM_TAG_W] == PRISM_STR_TAG || p[PRISM_TAG_W] == PRISM_BIG_TAG) return 0;
    if (p[PRISM_RC_W] == 1) {
        long n = p[PRISM_ARITY_W];
        for (long i = 0; i < n; i++) prism_rc_dec(p[PRISM_HDR_WORDS + i]);
        prism_reuse_hits++;
        return v;
    }
    p[PRISM_RC_W]--;
    return 0;
}

void *prism_reuse_alloc(long token, long n_words) {
    if (token) {
        long *p = (long *)token;
        p[PRISM_RC_W] = 1;
        p[PRISM_TAG_W] = 0;
        p[PRISM_ARITY_W] = n_words;
        return p;
    }
    return prism_alloc(n_words);
}

long prism_tag(void *p) {
    return ((long *)p)[PRISM_TAG_W];
}

long prism_field(void *p, long i) {
    return ((long *)p)[PRISM_HDR_WORDS + i];
}

long prism_read_int(void) {
    long n = 0;
    if (scanf("%ld", &n) != 1) {
        fprintf(stderr, "fatal: read_int: no integer on stdin\n");
        exit(1);
    }
    return n;
}

long prism_read_line(void) {
    char *buf = 0;
    size_t cap = 0;
    long n = getline(&buf, &cap, stdin);
    if (n < 0) {
        free(buf);
        return prism_str_lit("", 0);
    }
    while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) buf[--n] = 0;
    long cell = prism_str_lit(buf, n);
    free(buf);
    return cell;
}

/* Printing helpers used by the MLIR backend. The LLVM backend inlines printf
 * directly; these give both backends one shared runtime to link against. */
void print_int(long n) {
    printf("%ld\n", n);
}

void print_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    printf("%g\n", d);
}

void print_str(long s) {
    printf("%s\n", prism_str_data(s));
}

void exit_code(long n) {
    exit((int)n);
}

/* String builders operate on string cells and return fresh counted cells, so
 * the live-cell balance stays zero. str_len/char_at/substring index by Unicode
 * codepoint (not byte), so multi-byte UTF-8 text behaves as the source reads. */
long prism_str_concat(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    long *p = prism_str_alloc(la + lb);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    memcpy(o, prism_str_data(a), (size_t)la);
    memcpy(o + la, prism_str_data(b), (size_t)lb);
    o[la + lb] = 0;
    return (long)p;
}

long prism_str_len(long a) {
    const char *d = prism_str_data(a);
    long nb = prism_str_len_bytes(a), n = 0;
    for (long i = 0; i < nb; i++)
        if (((unsigned char)d[i] & 0xC0) != 0x80) n++;
    return n;
}

long prism_byte_len(long s) {
    return prism_str_len_bytes(s); /* raw byte count; the call site retags it */
}

long prism_byte_at(long s, long i) {
    if (i < 0 || i >= prism_str_len_bytes(s)) return -1;
    return (long)(unsigned char)prism_str_data(s)[i];
}

long prism_str_eq(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    if (la != lb) return 0;
    return memcmp(prism_str_data(a), prism_str_data(b), (size_t)la) == 0 ? 1 : 0;
}

long prism_show_bool(long b) {
    return b ? prism_str_lit("true", 4) : prism_str_lit("false", 5);
}

long prism_show_char(long cp) {
    unsigned long c = (unsigned long)cp;
    char buf[4];
    int k;
    if (c < 0x80) {
        buf[0] = (char)c;
        k = 1;
    } else if (c < 0x800) {
        buf[0] = (char)(0xC0 | (c >> 6));
        buf[1] = (char)(0x80 | (c & 0x3F));
        k = 2;
    } else if (c < 0x10000) {
        buf[0] = (char)(0xE0 | (c >> 12));
        buf[1] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[2] = (char)(0x80 | (c & 0x3F));
        k = 3;
    } else {
        buf[0] = (char)(0xF0 | (c >> 18));
        buf[1] = (char)(0x80 | ((c >> 12) & 0x3F));
        buf[2] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[3] = (char)(0x80 | (c & 0x3F));
        k = 4;
    }
    return prism_str_lit(buf, k);
}

long prism_show_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    char buf[32];
    int k = snprintf(buf, sizeof buf, "%g", d);
    return prism_str_lit(buf, k);
}

long prism_substring(long s, long start, long len) {
    const char *d = prism_str_data(s);
    long nb = prism_str_len_bytes(s);
    if (start < 0) start = 0;
    if (len < 0) len = 0;
    long b = 0, skipped = 0;
    while (b < nb && skipped < start) { b += utf8_step(d, b, nb); skipped++; }
    long bstart = b, taken = 0;
    while (b < nb && taken < len) { b += utf8_step(d, b, nb); taken++; }
    long out_len = b - bstart;
    long *p = prism_str_alloc(out_len);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    memcpy(o, d + bstart, (size_t)out_len);
    o[out_len] = 0;
    return (long)p;
}

long prism_char_at(long s, long i) {
    if (i < 0) return -1;
    const char *d = prism_str_data(s);
    long nb = prism_str_len_bytes(s);
    long cp = 0;
    for (long b = 0; b < nb;) {
        unsigned char c = (unsigned char)d[b];
        long adv = utf8_step(d, b, nb);
        long val = c < 0x80 ? c : c < 0xE0 ? c & 0x1F : c < 0xF0 ? c & 0x0F : c & 0x07;
        for (long k = 1; k < adv; k++)
            val = (val << 6) | ((unsigned char)d[b + k] & 0x3F);
        if (cp == i) return val;
        cp++;
        b += adv;
    }
    return -1;
}

static int prism_ws(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\f' || c == '\r';
}

long prism_str_cmp(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    long n = la < lb ? la : lb;
    int c = memcmp(prism_str_data(a), prism_str_data(b), (size_t)n);
    if (c < 0) return -1;
    if (c > 0) return 1;
    return la < lb ? -1 : la > lb ? 1 : 0;
}

static long *prism_big_alloc(long nlimbs) {
    long *p = malloc((PRISM_HDR_WORDS + nlimbs) * 8);
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
    if (n) memcpy(p + PRISM_HDR_WORDS, m, (size_t)n * 8);
    p[PRISM_ARITY_W] = neg ? -n : n;
    return (long)p;
}

static int mag_cmp(const unsigned long *a, long na, const unsigned long *b, long nb) {
    if (na != nb) return na < nb ? -1 : 1;
    for (long i = na - 1; i >= 0; i--)
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}

static long mag_add(const unsigned long *a, long na, const unsigned long *b, long nb, unsigned long *o) {
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
static long mag_sub(const unsigned long *a, long na, const unsigned long *b, long nb, unsigned long *o) {
    long borrow = 0;
    for (long i = 0; i < na; i++) {
        __int128 t = (__int128)a[i] - (i < nb ? b[i] : 0) - borrow;
        o[i] = (unsigned long)t;
        borrow = t < 0;
    }
    return na;
}

static void mag_mul(const unsigned long *a, long na, const unsigned long *b, long nb, unsigned long *o) {
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
    if (p == q) { *ok = 0; return 0; }
    for (const char *t = p; t < q; t++)
        if (*t < '0' || *t > '9') { *ok = 0; return 0; }
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
    o += snprintf(o, (size_t)(buf + cap - o), "%lu", chunk[k - 1]);
    for (long i = k - 2; i >= 0; i--)
        o += snprintf(o, (size_t)(buf + cap - o), "%019lu", chunk[i]);
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
    return (v << 1) | 1;
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
    *fresh = w & 1;
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
    if ((a & b & 1) && !__builtin_add_overflow(a >> 1, b >> 1, &r) &&
        r >= PRISM_IMM_MIN && r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_add);
}

long prism_rt_int_sub(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_sub_overflow(a >> 1, b >> 1, &r) &&
        r >= PRISM_IMM_MIN && r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_sub);
}

long prism_rt_int_mul(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_mul_overflow(a >> 1, b >> 1, &r) &&
        r >= PRISM_IMM_MIN && r <= PRISM_IMM_MAX)
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
 * returns whichever buffer holds the sorted result. */
static long *prism_msort(long *src, long *buf, long n, long kind) {
    for (long w = 1; w < n; w *= 2) {
        for (long i = 0; i < n; i += 2 * w) {
            long mid = i + w < n ? i + w : n;
            long hi = i + 2 * w < n ? i + 2 * w : n;
            long a = i, b = mid, k = i;
            while (a < mid && b < hi)
                buf[k++] = prism_sort_cmp(kind, src[b], src[a]) < 0 ? src[b++] : src[a++];
            while (a < mid) buf[k++] = src[a++];
            while (b < hi) buf[k++] = src[b++];
        }
        long *t = src; src = buf; buf = t;
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
static void prism_radix(long *heads, unsigned long *keys, long n) {
    long *th = malloc((size_t)n * sizeof(long));
    unsigned long *tk = malloc((size_t)n * sizeof(unsigned long));
    long *sh = heads, *dh = th;
    unsigned long *sk = keys, *dk = tk;
    for (int shift = 0; shift < 64; shift += 8) {
        long count[256] = {0};
        for (long i = 0; i < n; i++) count[(sk[i] >> shift) & 0xff]++;
        long sum = 0;
        for (int b = 0; b < 256; b++) { long c = count[b]; count[b] = sum; sum += c; }
        for (long i = 0; i < n; i++) {
            long pos = count[(sk[i] >> shift) & 0xff]++;
            dh[pos] = sh[i];
            dk[pos] = sk[i];
        }
        long *t = sh; sh = dh; dh = t;
        unsigned long *u = sk; sk = dk; dk = u;
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
    long n = 0;
    for (long q = list; !(q & 1) && q && ((long *)q)[PRISM_ARITY_W] == 2;
         q = ((long *)q)[PRISM_HDR_WORDS + 1])
        n++;

    long *cells = n ? malloc((size_t)n * sizeof(long)) : NULL;
    long *heads = n ? malloc((size_t)n * sizeof(long)) : NULL;
    long cons_tag = 0, i = 0, p = list, unique = 1;
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
            long *buf = malloc((size_t)n * sizeof(long));
            long *res = prism_msort(heads, buf, n, kind);
            if (res != heads) memcpy(heads, res, (size_t)n * sizeof(long));
            free(buf);
        } else {
            unsigned long *keys = malloc((size_t)n * sizeof(unsigned long));
            for (long j = 0; j < n; j++) keys[j] = prism_sort_key(kind, heads[j]);
            prism_radix(heads, keys, n);
            free(keys);
        }
    }

    long ret;
    if (unique) {
        for (long j = 0; j < n; j++) ((long *)cells[j])[PRISM_HDR_WORDS + 0] = heads[j];
        prism_rc_inc(list);
        ret = list;
    } else {
        long *nil = prism_alloc(0);
        nil[PRISM_TAG_W] = nil_tag;
        long acc = (long)nil;
        for (long j = n - 1; j >= 0; j--) {
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

/* Generic print for values whose type elaboration could not pin down (a var
 * read is an effect op whose row-polymorphic signature hides the payload
 * type). Cells are self-describing via their tag, so dispatch at runtime to
 * keep parity with the interpreter's dynamic show. */
void prism_print_int(long w) {
    if (w & 1) {
        printf("%ld", w >> 1);
    } else if (!w) {
        printf("0");
    } else if (((long *)w)[PRISM_TAG_W] == PRISM_STR_TAG) {
        printf("%s", prism_str_data(w));
    } else {
        long s = prism_big_show(w);
        printf("%s", prism_str_data(s));
        prism_rc_dec(s);
    }
}

void prism_print_nl(void) { putchar('\n'); }

/* SplitMix64. A single global stream, seeded to the same default constant the
 * interpreter uses so unseeded `rand` is reproducible across backends. */
static unsigned long prism_rng = 0x9E3779B97F4A7C15UL;

void prism_srand(long seed) { prism_rng = (unsigned long)seed; }

long prism_rand(void) {
    prism_rng += 0x9E3779B97F4A7C15UL;
    unsigned long z = prism_rng;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
    z ^= z >> 31;
    return (long)(z >> 2);
}

long prism_parse_float(long s) {
    double d = strtod(prism_str_data(s), NULL);
    long bits;
    memcpy(&bits, &d, 8);
    return prism_box(bits);
}

long prism_pow_float(long a, long b) {
    double x, y;
    memcpy(&x, &a, 8);
    memcpy(&y, &b, 8);
    double r = pow(x, y);
    long bits;
    memcpy(&bits, &r, 8);
    return prism_box(bits);
}

long prism_show_float_prec(long f, long digits) {
    double d;
    memcpy(&d, &f, 8);
    if (digits < 0) digits = 0;
    char buf[64];
    int k = snprintf(buf, sizeof buf, "%.*f", (int)digits, d);
    if (k < 0) k = 0;
    if (k >= (int)sizeof buf) k = (int)sizeof buf - 1;
    return prism_str_lit(buf, k);
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

long prism_int_of_i64(long p) {
    long v = prism_unbox(p);
    if (v >= PRISM_IMM_MIN && v <= PRISM_IMM_MAX) return int_imm(v);
    return prism_big_from_int(v);
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
long prism_i64_and(long a, long b) { return prism_box(prism_unbox(a) & prism_unbox(b)); }
long prism_i64_or(long a, long b) { return prism_box(prism_unbox(a) | prism_unbox(b)); }
long prism_i64_xor(long a, long b) { return prism_box(prism_unbox(a) ^ prism_unbox(b)); }
long prism_u64_and(long a, long b) { return prism_box(prism_unbox(a) & prism_unbox(b)); }
long prism_u64_or(long a, long b) { return prism_box(prism_unbox(a) | prism_unbox(b)); }
long prism_u64_xor(long a, long b) { return prism_box(prism_unbox(a) ^ prism_unbox(b)); }

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

/* OS surface. getenv/arg return a fresh counted string cell (empty when
 * unset, never NULL), writes consume their argument cells via the caller's
 * rc_dec and return unit. read_file fails loudly on any error and caps the
 * slurp so a pathological file cannot exhaust memory. */
#define PRISM_READ_CAP (1L << 30)

static void prism_read_fatal(const char *why, const char *path) {
    fprintf(stderr, "prism: read_file: %s: %s\n", why, path);
    exit(1);
}

static int prism_argc = 0;
static char **prism_argv = 0;

long prism_args_count(void) {
    return prism_argc;
}

long prism_arg(long i) {
    if (i < 0 || i >= prism_argc) return prism_str_lit("", 0);
    const char *a = prism_argv[i];
    return prism_str_lit(a, (long)strlen(a));
}

long prism_getenv(long name) {
    const char *v = getenv(prism_str_data(name));
    if (!v) return prism_str_lit("", 0);
    return prism_str_lit(v, (long)strlen(v));
}

long prism_read_file(long path) {
    const char *name = prism_str_data(path);
    FILE *f = fopen(name, "rb");
    if (!f) prism_read_fatal("cannot open", name);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) prism_read_fatal("cannot size", name);
    if (n > PRISM_READ_CAP) prism_read_fatal("exceeds 1GB cap", name);
    long *p = prism_str_alloc(n);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    long got = (long)fread(o, 1, (size_t)n, f);
    o[got] = 0;
    p[PRISM_ARITY_W] = got;
    fclose(f);
    return (long)p;
}

/* Result(Unit, String): Ok(()) with the immediate Unit field, or Err(msg). */
static long prism_file_ok(void) {
    long unit = 0;
    return prism_ctor(0, 1, &unit);
}

static long prism_file_err(const char *msg) {
    long s = prism_str_lit(msg, (long)strlen(msg));
    return prism_ctor(1, 1, &s);
}

static long prism_file_write(long path, long contents, const char *mode) {
    FILE *f = fopen(prism_str_data(path), mode);
    if (!f) return prism_file_err("cannot open file for writing");
    size_t want = (size_t)prism_str_len_bytes(contents);
    size_t got = fwrite(prism_str_data(contents), 1, want, f);
    fclose(f);
    if (got < want) return prism_file_err("short write");
    return prism_file_ok();
}

long prism_write_file(long path, long contents) {
    return prism_file_write(path, contents, "wb");
}

long prism_append_file(long path, long contents) {
    return prism_file_write(path, contents, "ab");
}

long prism_file_exists(long path) {
    FILE *f = fopen(prism_str_data(path), "rb");
    if (f) fclose(f);
    return f != 0;
}

long prism_remove_file(long path) {
    remove(prism_str_data(path));
    return 0;
}

void prism_array_oob(void) {
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
static long arr_len(long *p) { return p[PRISM_HDR_WORDS] >> 1; }
static void arr_setlen(long *p, long l) { p[PRISM_HDR_WORDS] = (l << 1) | 1; }
static long arr_cap(long *p) { return p[PRISM_ARITY_W] - 1; }

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

/* Build a string from an array of byte values (each a small Int 0..255, stored
   tagged so `>> 1` recovers it). Borrows the array. */
long prism_string_of_bytes(long arr) {
    long *p = (long *)arr;
    long n = arr_len(p);
    long *out = prism_str_alloc(n);
    char *o = (char *)(out + PRISM_HDR_WORDS);
    for (long i = 0; i < n; i++) o[i] = (char)((p[PRISM_ARR_ELEM0 + i] >> 1) & 0xFF);
    o[n] = 0;
    return (long)out;
}

/* Run a shell command, returning its exit code (-1 on spawn failure or signal
   death). The result is a raw int the call site retags as an Int. */
long prism_system(long cmd) {
    int rc = system(prism_str_data(cmd));
    if (rc == -1 || !WIFEXITED(rc)) return -1;
    return WEXITSTATUS(rc);
}

/* Write a string to stderr (no trailing newline). Returns unit. */
long prism_eprint(long s) {
    fputs(prism_str_data(s), stderr);
    return 0;
}

long prism_exit(long code) {
    exit((int)code);
}

extern long prism_main(void);

int main(int argc, char **argv) {
    prism_argc = argc;
    prism_argv = argv;
    long r = prism_main();
    int code = (int)(r & 1 ? r >> 1 : 0);
    if (!(r & 1) && r) prism_rc_dec(r);
    return code;
}
