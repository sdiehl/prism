/* Strings: counted string cells, their byte/codepoint operations, the scalar
 * show helpers, and the blake3 hash. */
#include "prism_string.h"
#include "prism_mem.h"

long *prism_str_alloc(long byte_len) {
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

char *prism_str_data(long s) {
    return (char *)((long *)s + PRISM_HDR_WORDS);
}

long prism_str_len_bytes(long s) {
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

/* Shared with the interpreter's C differential oracle, which links this file and
 * calls print_str to echo shown values. Backends print via the prism_print_*
 * entry points below, not this one. */
void print_str(long s) {
    printf("%s\n", prism_str_data(s));
}

/* String builders operate on string cells and return fresh counted cells, so
 * the live-cell balance stays zero. str_len/char_at/substring index by Unicode
 * codepoint (not byte), so multi-byte UTF-8 text behaves as the source reads. */
long prism_str_concat(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    long lab = prism_ckd_ladd(la, lb);
    long *p = prism_str_alloc(lab);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    memcpy(o, prism_str_data(a), (size_t)la);
    memcpy(o + la, prism_str_data(b), (size_t)lb);
    o[lab] = 0;
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
    /* Non-scalar code points (surrogates, past U+10FFFF, negative) are not
     * encodable and show as the empty string, matching char::from_u32. */
    if (cp < 0 || cp > PRISM_CP_MAX || (cp >= PRISM_SURROGATE_LO && cp <= PRISM_SURROGATE_HI))
        return prism_str_lit("", 0);
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

/* --- blake3, one-shot ------------------------------------------------------
 *
 * A portable, single-threaded blake3 over a byte buffer, returned as lowercase
 * hex. This is the native half of the `blake3` builtin every derived `Hash`
 * instance folds through; it must produce output byte-identical to the Rust
 * `blake3` crate the interpreter uses (gated by tests/hash_value_parity.rs), so
 * it follows the reference spec exactly: 1024-byte chunks, a binary tree of
 * parent nodes, the seven-round G-permutation, and the CHUNK/PARENT/ROOT flags. */

#define B3_BLOCK_LEN 64
#define B3_CHUNK_LEN 1024
#define B3_CHUNK_START 1u
#define B3_CHUNK_END 2u
#define B3_PARENT 4u
#define B3_ROOT 8u

static const uint32_t B3_IV[8] = {0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
                                  0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u};

static const uint8_t B3_MSG_PERM[16] = {2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8};

static inline uint32_t b3_rotr(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));
}

static inline uint32_t b3_le32(const uint8_t *b) {
    return (uint32_t)b[0] | ((uint32_t)b[1] << 8) | ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24);
}

static inline void b3_g(uint32_t s[16], int a, int b, int c, int d, uint32_t x, uint32_t y) {
    s[a] = s[a] + s[b] + x;
    s[d] = b3_rotr(s[d] ^ s[a], 16);
    s[c] = s[c] + s[d];
    s[b] = b3_rotr(s[b] ^ s[c], 12);
    s[a] = s[a] + s[b] + y;
    s[d] = b3_rotr(s[d] ^ s[a], 8);
    s[c] = s[c] + s[d];
    s[b] = b3_rotr(s[b] ^ s[c], 7);
}

static void b3_round(uint32_t s[16], const uint32_t m[16]) {
    b3_g(s, 0, 4, 8, 12, m[0], m[1]);
    b3_g(s, 1, 5, 9, 13, m[2], m[3]);
    b3_g(s, 2, 6, 10, 14, m[4], m[5]);
    b3_g(s, 3, 7, 11, 15, m[6], m[7]);
    b3_g(s, 0, 5, 10, 15, m[8], m[9]);
    b3_g(s, 1, 6, 11, 12, m[10], m[11]);
    b3_g(s, 2, 7, 8, 13, m[12], m[13]);
    b3_g(s, 3, 4, 9, 14, m[14], m[15]);
}

/* Compress one 64-byte block, writing the 16 output words (the first 8 are the
 * chaining value; the full 16 are the extendable output for a root node). */
static void b3_compress(const uint32_t cv[8], const uint8_t block[64], uint64_t counter,
                        uint32_t block_len, uint32_t flags, uint32_t out[16]) {
    uint32_t m[16];
    for (size_t i = 0; i < 16; i++) m[i] = b3_le32(block + 4 * i);
    uint32_t s[16] = {cv[0],
                      cv[1],
                      cv[2],
                      cv[3],
                      cv[4],
                      cv[5],
                      cv[6],
                      cv[7],
                      B3_IV[0],
                      B3_IV[1],
                      B3_IV[2],
                      B3_IV[3],
                      (uint32_t)counter,
                      (uint32_t)(counter >> 32),
                      block_len,
                      flags};
    for (int r = 0; r < 7; r++) {
        b3_round(s, m);
        if (r < 6) {
            uint32_t t[16];
            for (int i = 0; i < 16; i++) t[i] = m[B3_MSG_PERM[i]];
            memcpy(m, t, sizeof t);
        }
    }
    for (int i = 0; i < 8; i++) {
        out[i] = s[i] ^ s[i + 8];
        out[i + 8] = s[i + 8] ^ cv[i];
    }
}

/* Chain the blocks of one chunk into its 8-word chaining value. `root` sets the
 * ROOT flag on the final block (the whole input is a single chunk). */
static void b3_chunk_cv(const uint8_t *in, size_t len, uint64_t counter, int root,
                        uint32_t out_cv[8]) {
    uint32_t cv[8];
    memcpy(cv, B3_IV, sizeof cv);
    size_t nblocks = len == 0 ? 1 : (len + B3_BLOCK_LEN - 1) / B3_BLOCK_LEN;
    for (size_t b = 0; b < nblocks; b++) {
        size_t off = b * B3_BLOCK_LEN;
        size_t blen = len - off < B3_BLOCK_LEN ? len - off : B3_BLOCK_LEN;
        uint8_t block[64];
        memset(block, 0, sizeof block);
        memcpy(block, in + off, blen);
        uint32_t flags = 0;
        if (b == 0) flags |= B3_CHUNK_START;
        if (b == nblocks - 1) {
            flags |= B3_CHUNK_END;
            if (root) flags |= B3_ROOT;
        }
        uint32_t words[16];
        b3_compress(cv, block, counter, (uint32_t)blen, flags, words);
        memcpy(cv, words, sizeof cv);
    }
    memcpy(out_cv, cv, sizeof(uint32_t) * 8);
}

/* Bytes on the left of a subtree split: the largest power-of-two chunk count
 * strictly less than the total, times the chunk length. */
static size_t b3_left_len(size_t len) {
    size_t full = (len - 1) / B3_CHUNK_LEN;
    size_t p = 1;
    while (p * 2 <= full) p *= 2;
    return p * B3_CHUNK_LEN;
}

/* Chaining value of a non-root subtree covering `in[0..len]`. Recurses on the
 * binary tree split; depth is bounded by log2(len / B3_CHUNK_LEN) <= 54 for any
 * size_t len, so the call chain cannot exhaust the stack. */
/* NOLINTNEXTLINE(misc-no-recursion) */
static void b3_subtree_cv(const uint8_t *in, size_t len, uint64_t counter, uint32_t out[8]) {
    if (len <= B3_CHUNK_LEN) {
        b3_chunk_cv(in, len, counter, 0, out);
        return;
    }
    size_t left = b3_left_len(len);
    uint32_t l[8], r[8];
    b3_subtree_cv(in, left, counter, l);
    b3_subtree_cv(in + left, len - left, counter + left / B3_CHUNK_LEN, r);
    uint8_t block[64];
    memcpy(block, l, 32);
    memcpy(block + 32, r, 32);
    uint32_t words[16];
    b3_compress(B3_IV, block, 0, B3_BLOCK_LEN, B3_PARENT, words);
    memcpy(out, words, sizeof(uint32_t) * 8);
}

static void b3_hash(const uint8_t *in, size_t len, uint8_t out[32]) {
    uint32_t words[8];
    if (len <= B3_CHUNK_LEN) {
        b3_chunk_cv(in, len, 0, 1, words);
    } else {
        size_t left = b3_left_len(len);
        uint32_t l[8], r[8];
        b3_subtree_cv(in, left, 0, l);
        b3_subtree_cv(in + left, len - left, left / B3_CHUNK_LEN, r);
        uint8_t block[64];
        memcpy(block, l, 32);
        memcpy(block + 32, r, 32);
        uint32_t full[16];
        b3_compress(B3_IV, block, 0, B3_BLOCK_LEN, B3_PARENT | B3_ROOT, full);
        memcpy(words, full, sizeof words);
    }
    for (size_t i = 0; i < 8; i++)
        for (size_t j = 0; j < 4; j++) out[i * 4 + j] = (uint8_t)(words[i] >> (8 * j));
}

/* blake3 of a raw byte span, returned as a 64-char lowercase-hex string cell.
 * The single home for the hash: prism_blake3 (a string's bytes) and the buffer
 * module's prism_buf_hash both fold through here, so the string and byte hash
 * paths can never diverge. */
long prism_blake3_bytes(const void *data, long len) {
    uint8_t dig[32];
    b3_hash((const uint8_t *)data, (size_t)len, dig);
    static const char hexd[] = "0123456789abcdef";
    char hex[64];
    for (size_t i = 0; i < 32; i++) {
        hex[2 * i] = hexd[dig[i] >> 4];
        hex[2 * i + 1] = hexd[dig[i] & 15];
    }
    return prism_str_lit(hex, 64);
}

long prism_blake3(long s) {
    return prism_blake3_bytes(prism_str_data(s), prism_str_len_bytes(s));
}

long prism_substring(long s, long start, long len) {
    const char *d = prism_str_data(s);
    long nb = prism_str_len_bytes(s);
    if (start < 0) start = 0;
    if (len < 0) len = 0;
    long b = 0, skipped = 0;
    while (b < nb && skipped < start) {
        b += utf8_step(d, b, nb);
        skipped++;
    }
    long bstart = b, taken = 0;
    while (b < nb && taken < len) {
        b += utf8_step(d, b, nb);
        taken++;
    }
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
        for (long k = 1; k < adv; k++) val = (val << 6) | ((unsigned char)d[b + k] & 0x3F);
        if (cp == i) return val;
        cp++;
        b += adv;
    }
    return -1;
}

int prism_ws(char c) {
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
