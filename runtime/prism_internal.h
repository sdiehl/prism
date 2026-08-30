/* Shared internal foundation for the Prism C runtime modules.
 *
 * The runtime is split into semantic translation units (prism_mem, prism_string,
 * prism_int, prism_float, prism_effect, prism_array, prism_sort, prism_io); this
 * header carries what every one of them needs identically: the system includes
 * and the optional mimalloc shim (which must precede any allocation), the heap
 * cell layout, and the string/bignum tags plus Unicode bounds. Module-local
 * constants live in their own module. The canonical list of the runtime source
 * files is defined once in the Rust tree (build.rs, mirrored into the embedded
 * runtime by src/codegen/rt.rs); this header is not on that list because it is
 * pulled in by #include, not compiled on its own. */
#ifndef PRISM_INTERNAL_H
#define PRISM_INTERNAL_H

/* Portability: requires GCC >= 5 or Clang >= 3.8.
 * Uses __attribute__((destructor)) for the leak/reuse/effop report hooks and
 * __builtin_add_overflow/sub/mul for checked arithmetic. */

#if defined(__GNUC__) || defined(__clang__)
#define PRISM_USED __attribute__((used))
#define PRISM_WEAK_DEFINE __attribute__((weak))
#if defined(__APPLE__)
#define PRISM_WEAK_EXTERN __attribute__((weak_import))
#else
#define PRISM_WEAK_EXTERN __attribute__((weak))
#endif
#else
#define PRISM_USED
#define PRISM_WEAK_DEFINE
#define PRISM_WEAK_EXTERN
#endif

/* getline is POSIX.1-2008; under -std=c11 glibc hides it unless a feature-test
 * macro requests it. macOS exposes it regardless, so this only bites on Linux.
 * Must precede every system header (including mimalloc's <stddef.h> below). */
#ifndef _POSIX_C_SOURCE
// clang-format off: a feature-test macro must be one line, and the NOLINT must
// stay on it to suppress the reserved-identifier lint.
#define _POSIX_C_SOURCE 200809L /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp): the standard feature-test macro */
// clang-format on
#endif

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

#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
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

/* Arena-owned marker in the refcount word: a cell handed out by a `with_arena`
 * region instead of malloc. The region is the cell's sole owner, so the cell is
 * refcount-inert: prism_rc_inc, prism_rc_dec, the child-scan decrement, and
 * prism_reuse_token all treat it as a no-op, and every `rc == 1` uniqueness
 * fast path in the runtime correctly sees it as never-unique. The bit lives in
 * the rc word rather than the tag word because generated code compares tag
 * words directly for match dispatch; only the rc machinery reads rc words. Bit
 * 62 keeps the value hugely positive, so the PRISM_RT_DEBUG `rc > 0` check and
 * any stray arithmetic stay harmless, and it can never collide with a real
 * count or the zero that terminates the free worklist. */
#define PRISM_ARENA_OWNED (1L << 62)

/* Forwarding marker set on an arena cell during one promotion walk: this cell
 * has already been copied, and the copy's address is in its tag word. It appears
 * only on cells that also carry PRISM_ARENA_OWNED, only between the start and
 * the end of prism_promote, and only on cells the region is about to destroy, so
 * nothing outside that walk ever observes it and no mark needs clearing. The tag
 * word is free to hold the pointer because prism_promote_shell copies the tag
 * into the new cell before the mark is set, and the arena teardown that follows
 * reads only arity and fields. Without this the walk revisits a shared arena
 * sub-DAG once per path and copies it once per path, so a diamond costs
 * exponential time and heap while still producing the correct value. */
#define PRISM_ARENA_FORWARDED (1L << 61)

/* Visited marker set on an ordinary (non-arena) cell during one promotion walk:
 * this cell's arena-valued fields have already been rewritten in place, so a
 * second path reaching it must not descend it again. It appears only between the
 * start and end of prism_promote and, unlike the arena marks above, sits on
 * cells the region keeps, so the walk records every marked cell and clears the
 * bit before returning. It is distinct from the arena marks: an ordinary cell is
 * never copied, only descended, so the tag word stays untouched. Without this
 * the walk re-descends a shared ordinary spine once per incoming path, costing
 * exponential time on a diamond while still producing the correct value. The bit
 * is not in PRISM_RC_INERT, so a count increment on a marked cell still lands;
 * it stays clear of the low count bits, so clearing it restores the true rc. */
#define PRISM_PROMOTE_SEEN (1L << 59)

/* Static-cell marker in the refcount word: a cell the compiler baked into the
 * executable image (a string literal), never allocated and never freed. The
 * cell may live in read-only memory, so every path that would write its rc
 * word must test this bit and leave; every `rc == 1` uniqueness fast path
 * correctly sees it as never-unique, because the marker keeps the word hugely
 * positive and never equal to one. It is distinct from PRISM_ARENA_OWNED
 * because the promotion walk copies arena cells out of a dying region, while a
 * static cell outlives every region and must be shared, never copied. Static
 * cells are outside the live-cell balance by construction: they are not
 * allocations, so no counter moves when one is mentioned or dropped. */
#define PRISM_STATIC_CELL (1L << 60)

/* Cells the count machinery must not touch: arena-owned (the region owns the
 * cell) and static (the image owns it). One mask, so a future inert class
 * cannot be added to some rc-writing sites and missed at others. */
#define PRISM_RC_INERT (PRISM_ARENA_OWNED | PRISM_STATIC_CELL)

/* A string is a cell { rc, tag=PRISM_STR_TAG, byte_len, utf8... }: the bytes
 * live inline after the header and are NUL-terminated for printf interop. The
 * distinct tag tells prism_rc_dec to free the cell without recursing into the
 * bytes (they are not child cells). A string the program builds at run time is
 * a counted cell that prism_rc_dec frees, so the live-cell balance includes
 * it; a source literal is instead one PRISM_STATIC_CELL per distinct spelling,
 * emitted into the image and shared by every mention. */
#define PRISM_STR_TAG 0x53545200L

/* A string view is a cell { rc, tag=PRISM_STRVIEW_TAG, 3, parent, off, len }: a
 * byte window into another string's inline bytes, taking no copy. Unlike the
 * inline-payload tags it is an ordinary child-bearing cell, so the collector,
 * the promotion walk, and the reuse path all handle it with no special case:
 * the parent is a strong reference, which is exactly what makes "a view cannot
 * outlive its parent" structural rather than a static analysis, and `off`/`len`
 * are tagged immediates the child scan skips like any other. A view's parent is
 * always a materialized string cell, never another view, so reading through one
 * is a single hop no matter how many times a span is re-sliced.
 *
 * Two invariants pay for the aliasing. The window is UTF-8 boundary-aligned, so
 * a view is valid UTF-8 whenever its parent is and slicing never has to repair
 * bytes it does not own; and the bytes are NOT NUL-terminated (the parent's next
 * byte follows them), so no path may hand `prism_str_data` to a C library
 * function that reads to a terminator. `prism_str_cstr` is that boundary. */
#define PRISM_STRVIEW_TAG 0x53565700L

/* An Integer is a sign-magnitude bignum cell { rc, tag=PRISM_BIG_TAG, n, limbs... }:
 * n is a signed limb count whose sign is the value's sign, the magnitude is |n|
 * u64 limbs little-endian starting at offset 24 with no leading zero limbs, and
 * zero is n == 0 with no limbs. Like strings, the tag tells prism_rc_dec and
 * prism_reuse_token not to recurse into the payload (limbs are not child cells). */
#define PRISM_BIG_TAG 0x42494700L

/* An unboxed byte buffer cell { rc, tag=PRISM_BUF_TAG, arity, len, bytes... }:
 * a contiguous region of raw u8 held inline after a length word, the numeric
 * analogue of a string cell but with no UTF-8 interpretation and no NUL
 * terminator, so a `Bytes` value threads byte-for-byte identically on both
 * backends. arity is the payload word count (the length word plus the byte
 * capacity rounded up to whole words); the byte length lives in the first
 * payload word. Like strings and bignums, the tag tells prism_rc_dec and
 * prism_reuse_token not to recurse into the payload (bytes are not child cells),
 * so Perceus reference counting, the leak balance, and the rc==1 in-place / shared
 * -copy discipline apply to it unchanged. */
#define PRISM_BUF_TAG 0x42554600L

/* A typed buffer cell { rc, tag=PRISM_TBUF_TAG, arity, len, words... }: a
 * contiguous region of raw 8-byte words (a double or fixed-width integer by bit
 * pattern) held inline after a length word, the flat storage under the tensor
 * library. arity is the payload word count (the length word plus one word per
 * element); the element count lives in the first payload word. Like strings,
 * bignums, and byte buffers, the tag tells prism_rc_dec and prism_reuse_token not
 * to recurse into the payload (raw words are not child cells), so Perceus
 * reference counting, the leak balance, and the rc==1 in-place / shared-copy
 * discipline apply to it unchanged. */
#define PRISM_TBUF_TAG 0x54425546L

/* The one membership test over the inline-payload tag family above. A cell with
 * one of these tags stores bytes, limbs, or raw words behind its arity slot, so
 * its arity is a payload measure and its payload words are never child values;
 * every other tag is an ordinary cell whose arity is a genuine field count.
 * The collector, the promotion walk, the reuse-token check, and the debug
 * field-bounds check all decide the same question, so they all ask it here:
 * admitting a new payload tag is one line, not four sites to keep in step. */
static inline int prism_tag_has_payload(long tag) {
    return tag == PRISM_STR_TAG || tag == PRISM_BIG_TAG || tag == PRISM_BUF_TAG ||
           tag == PRISM_TBUF_TAG;
}

/* The one membership test over the two spellings of a String value: bytes held
 * inline, or a window onto another cell's. The string accessors answer for both,
 * so a runtime dispatch that recognizes strings by tag must admit both. */
static inline int prism_tag_is_str(long tag) {
    return tag == PRISM_STR_TAG || tag == PRISM_STRVIEW_TAG;
}

/* The abort text an out-of-bounds buffer index prints before dying. Both the
 * byte buffer and the typed buffer fault the same way, and the interpreter's
 * builtin path checks for this exact string, so the words are shared from one
 * home rather than re-typed at each site; a matching drift guard in the root
 * crate reads this header and the interpreter const to hold the two in step. */
#define PRISM_BUFFER_INDEX_ERROR "buffer index out of bounds"

/* Unicode scalar-value bounds. The interpreter's show_char is char::from_u32,
 * which admits U+0000..U+D7FF and U+E000..U+10FFFF, rejecting the UTF-16
 * surrogate range and anything past the last code point; a rejected value shows
 * as the empty string. Native must gate on the identical bounds. */
#define PRISM_CP_MAX 0x10FFFFL
#define PRISM_SURROGATE_LO 0xD800L
#define PRISM_SURROGATE_HI 0xDFFFL

/* The size in bytes of one heap word (a long, per the LP64 assertion below). */
#define PRISM_WORD_BYTES 8

/* Checked length and capacity arithmetic. C signed overflow is undefined
 * behavior, and an overflowed size handed to an allocator under-allocates and
 * corrupts the heap, so every length, capacity, and byte-count computation
 * that could leave the long domain goes through these helpers; the policy on
 * overflow matches prism_alloc's, an immediate abort rather than a value the
 * callee cannot repair. */
static inline long prism_ckd_ladd(long a, long b) {
    long r;
    if (__builtin_add_overflow(a, b, &r)) abort();
    return r;
}

static inline long prism_ckd_lmul(long a, long b) {
    long r;
    if (__builtin_mul_overflow(a, b, &r)) abort();
    return r;
}

/* A nonnegative long as a size_t; a negative length or count is a caller bug. */
static inline size_t prism_ckd_size(long n) {
    if (n < 0) abort();
    return (size_t)n;
}

/* A word count as a malloc byte count, sign and multiply both checked. */
static inline size_t prism_ckd_words_bytes(long n_words) {
    size_t bytes;
    if (__builtin_mul_overflow(prism_ckd_size(n_words), (size_t)PRISM_WORD_BYTES, &bytes)) abort();
    return bytes;
}

/* Doubling capacity growth over a module's floor: the floor when below it,
 * otherwise twice the current capacity, checked. */
static inline long prism_ckd_grow(long cap, long floor_cap) {
    return cap < floor_cap ? floor_cap : prism_ckd_lmul(cap, 2);
}

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8, "prism runtime assumes LP64");
/* The heap-word size constant must track the actual word type; the code
 * generator cross-checks the same constant against `abi::WORD_BYTES` in
 * emit.rs's `layout_matches_runtime`, so both halves of the ABI stay pinned. */
_Static_assert(PRISM_WORD_BYTES == (long)sizeof(long),
               "PRISM_WORD_BYTES must equal the heap word size");

#endif /* PRISM_INTERNAL_H */
