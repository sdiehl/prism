/* Unboxed typed buffers: a contiguous, refcounted region of raw 8-byte words,
 * each an IEEE-754 double or fixed-width integer by bit pattern, the flat storage
 * the tensor library indexes with computed strides. A buffer cell is header-
 * compatible with every other heap cell (see PRISM_TBUF_TAG in prism_internal.h),
 * so Perceus reference counting, the leak balance, and the rc==1 in-place /
 * shared-copy discipline apply to it unchanged; only the payload is raw words
 * rather than child cells, so prism_rc_dec and prism_reuse_token skip it. The
 * element kind is a surface-level fact (it decides which builtin boxes or unboxes
 * the word); the C here moves raw words and is element-kind-agnostic. */
#ifndef PRISM_TBUF_H
#define PRISM_TBUF_H

#include "prism_internal.h"

/* Does not return: prints to stderr and exits (like prism_array_oob). */
_Noreturn void prism_tbuf_oob(void);

long prism_tbuf_new(long n, long init);
long prism_tbuf_len(long b);
long prism_tbuf_get(long b, long i);
long prism_tbuf_set(long b, long i, long x);
long prism_tbuf_blit(long dst, long dstart, long src, long sstart, long n);

#endif /* PRISM_TBUF_H */
