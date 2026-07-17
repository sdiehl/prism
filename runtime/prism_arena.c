/* prism_arena.c: a region (arena) allocator.
 *
 * Standalone and self-contained: the linked runtime does not include this file.
 * Runtime tests build it directly so the allocator can be tested and reasoned
 * about independently of `prism_rt.c` and codegen.
 *
 * The design is the textbook region allocator (Hanson, "C Interfaces and
 * Implementations", ch. 6; Tofte/Talpin regions): a singly linked list of
 * blocks, bump-pointer allocation inside the current block, a fresh block when
 * one fills, and O(1) bulk reclamation. `reset` keeps the blocks and rewinds
 * their offsets so a per-iteration arena pays malloc once and reuses forever;
 * `destroy` returns everything. Individual objects are never freed: that is the
 * whole point, and what makes a region cheaper than a general allocator.
 *
 * Deliberately simple: no per-size free lists, no thread safety, no compaction.
 * An arena is single-threaded and owned by one scope, which is exactly the
 * `with_arena` handler's lifetime.
 *
 * Build the self-test:  cc -DPRISM_ARENA_TEST -O2 runtime/prism_arena.c -o /tmp/at && /tmp/at
 */

#ifndef _POSIX_C_SOURCE
// clang-format off: a feature-test macro must be one line, and the NOLINT must
// stay on it to suppress the reserved-identifier lint.
#define _POSIX_C_SOURCE 200809L /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp): the standard feature-test macro */
// clang-format on
#endif

#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Default block size when the caller passes 0: large enough that most scopes
 * never allocate a second block, small enough not to waste a page on a tiny
 * region. */
#define PRISM_ARENA_DEFAULT_BLOCK ((size_t)64 * 1024)

/* The natural alignment for any C object, the guarantee malloc gives. */
#define PRISM_ARENA_ALIGN (alignof(max_align_t))

typedef struct PrismBlock {
    struct PrismBlock *next;
    size_t cap; /* usable bytes in `data` */
    size_t off; /* bytes handed out so far */
    /* max_align_t so `data` itself is maximally aligned; then any interior
     * offset rounded up to a divisor of that alignment stays valid. */
    max_align_t data[]; /* flexible array member */
} PrismBlock;

typedef struct PrismArena {
    PrismBlock *head; /* first block, start of the reuse chain */
    PrismBlock *cur;  /* block currently being bumped */
    size_t block_size;
    size_t used; /* bytes handed out since the last reset (stats) */
} PrismArena;

/* Round address `n` up to a multiple of the power-of-two `align`. Aligning the
 * absolute address (not the block-relative offset) is what lets an arena serve
 * an alignment stronger than the block's own base alignment. */
static uintptr_t prism_align_up(uintptr_t n, size_t align) {
    return (n + (align - 1)) & ~((uintptr_t)align - 1);
}

/* Whether `size` at `align` fits `b` starting from its current offset, and if so
 * the aligned offset to hand out. */
static int prism_block_fits(const PrismBlock *b, size_t size, size_t align, size_t *out_off) {
    uintptr_t base = (uintptr_t)b->data;
    size_t start = (size_t)(prism_align_up(base + b->off, align) - base);
    size_t end;
    if (start > b->cap || __builtin_add_overflow(start, size, &end) || end > b->cap) { return 0; }
    *out_off = start;
    return 1;
}

/* Allocate one block with at least `cap` usable bytes, offsets rewound. */
static PrismBlock *prism_block_new(size_t cap) {
    size_t total;
    if (__builtin_add_overflow(sizeof(PrismBlock), cap, &total)) { return NULL; }
    PrismBlock *b = malloc(total);
    if (!b) { return NULL; }
    b->next = NULL;
    b->cap = cap;
    b->off = 0;
    return b;
}

PrismArena *prism_arena_create(size_t block_size) {
    if (block_size == 0) { block_size = PRISM_ARENA_DEFAULT_BLOCK; }
    PrismArena *a = malloc(sizeof(PrismArena));
    if (!a) { return NULL; }
    PrismBlock *b = prism_block_new(block_size);
    if (!b) {
        free(a);
        return NULL;
    }
    a->head = b;
    a->cur = b;
    a->block_size = block_size;
    a->used = 0;
    return a;
}

/* Bump `size` bytes at `align` (a power of two) out of the arena. Returns NULL
 * only on allocation failure or a size/alignment overflow; a size of 0 yields a
 * valid aligned pointer that owns no bytes. */
void *prism_arena_alloc_aligned(PrismArena *a, size_t size, size_t align) {
    if (align < PRISM_ARENA_ALIGN) { align = PRISM_ARENA_ALIGN; }
    /* prism_align_up masks with align-1, which only rounds correctly for a power
     * of two; a stray non-power-of-two would silently mis-align every object.
     * Alignment is a compile-time-shaped input, so a violation is a codegen bug:
     * trap always rather than hand back a mis-aligned pointer. */
    if ((align & (align - 1)) != 0) { abort(); }
    for (;;) {
        PrismBlock *b = a->cur;
        size_t start;
        if (prism_block_fits(b, size, align, &start)) {
            b->off = start + size;
            a->used += size;
            return (unsigned char *)b->data + start;
        }
        /* Does not fit the current block. Reuse the next block in the chain if
         * one survives from before a reset and is big enough; else grow. */
        size_t nstart;
        if (b->next && prism_block_fits(b->next, size, align, &nstart)) {
            a->cur = b->next;
            continue;
        }
        /* A fresh block: the default size, or exactly this request when it is
         * oversized. `align - 1` of headroom covers the interior rounding. */
        size_t want;
        if (__builtin_add_overflow(size, align - 1, &want)) { return NULL; }
        size_t cap = want > a->block_size ? want : a->block_size;
        PrismBlock *nb = prism_block_new(cap);
        if (!nb) { return NULL; }
        nb->next = b->next; /* splice in, preserving the rest of the chain */
        b->next = nb;
        a->cur = nb;
    }
}

/* Bump `size` bytes at the natural alignment. */
void *prism_arena_alloc(PrismArena *a, size_t size) {
    return prism_arena_alloc_aligned(a, size, PRISM_ARENA_ALIGN);
}

/* Reclaim every object in one step by rewinding all blocks, keeping the memory
 * for reuse. O(blocks), which is tiny; no per-object free. */
void prism_arena_reset(PrismArena *a) {
    for (PrismBlock *b = a->head; b; b = b->next) { b->off = 0; }
    a->cur = a->head;
    a->used = 0;
}

/* Return every block to the system and free the arena itself. */
void prism_arena_destroy(PrismArena *a) {
    if (!a) { return; }
    PrismBlock *b = a->head;
    while (b) {
        PrismBlock *next = b->next;
        free(b);
        b = next;
    }
    free(a);
}

/* Bytes handed out since the last reset, for stats and tests. */
size_t prism_arena_used(const PrismArena *a) {
    return a->used;
}

#ifdef PRISM_ARENA_TEST
#include <assert.h>
#include <stdio.h>

int main(void) {
    /* Small blocks so the chain grows and oversized allocations are exercised. */
    PrismArena *a = prism_arena_create(256);
    assert(a);

    /* Many small allocations: aligned, in bounds, distinct. */
    unsigned char *prev = NULL;
    for (int i = 0; i < 1000; i++) {
        size_t n = (size_t)(i % 40) + 1;
        unsigned char *p = prism_arena_alloc(a, n);
        assert(p);
        assert((uintptr_t)p % PRISM_ARENA_ALIGN == 0);
        memset(p, 0xAB, n); /* would trip ASan on any overlap/overrun */
        if (prev) { assert(p != prev); }
        prev = p;
    }

    /* Custom alignment. */
    void *q = prism_arena_alloc_aligned(a, 24, 64);
    assert((uintptr_t)q % 64 == 0);

    /* Oversized: larger than a block, still served. */
    unsigned char *big = prism_arena_alloc(a, 4096);
    assert(big);
    memset(big, 0xCD, 4096);

    /* Reset reuses memory: the first pointer after reset matches the first
     * pointer of the original run (same head block, rewound). */
    prism_arena_alloc(a, 0); /* no-op sanity: valid pointer, owns nothing */
    prism_arena_reset(a);
    assert(prism_arena_used(a) == 0);
    unsigned char *first_after = prism_arena_alloc(a, 1);
    prism_arena_reset(a);
    unsigned char *first_again = prism_arena_alloc(a, 1);
    assert(first_after == first_again); /* deterministic reuse */

    prism_arena_destroy(a);
    printf("prism_arena: OK\n");
    return 0;
}
#endif
