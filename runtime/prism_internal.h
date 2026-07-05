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

/* Unicode scalar-value bounds. The interpreter's show_char is char::from_u32,
 * which admits U+0000..U+D7FF and U+E000..U+10FFFF, rejecting the UTF-16
 * surrogate range and anything past the last code point; a rejected value shows
 * as the empty string. Native must gate on the identical bounds. */
#define PRISM_CP_MAX 0x10FFFFL
#define PRISM_SURROGATE_LO 0xD800L
#define PRISM_SURROGATE_HI 0xDFFFL

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8, "prism runtime assumes LP64");

#endif /* PRISM_INTERNAL_H */
