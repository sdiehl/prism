/* Unboxed byte buffers: a contiguous, refcounted region of raw u8 with no UTF-8
 * interpretation, the storage under the `Bytes` type. A buffer cell is header-
 * compatible with every other heap cell (see PRISM_BUF_TAG in prism_internal.h),
 * so Perceus reference counting, the leak balance, and the rc==1 in-place /
 * shared-copy discipline apply to it unchanged; only the payload is raw bytes
 * rather than child cells. */
#ifndef PRISM_BUFFER_H
#define PRISM_BUFFER_H

#include "prism_internal.h"

/* Does not return: prints to stderr and exits (like prism_array_oob). */
_Noreturn void prism_buf_oob(void);

long prism_buf_empty(void);
long prism_buf_new(long n, long init);
long prism_buf_len(long b);
long prism_buf_get(long b, long i);
long prism_buf_set(long b, long i, long x);
long prism_buf_push(long b, long x);
long prism_buf_slice(long b, long start, long len);
long prism_buf_cat(long a, long b);
long prism_buf_eq(long a, long b);
long prism_buf_cmp(long a, long b);
long prism_buf_hash(long b);
long prism_buf_of_string(long s);
long prism_string_of_buf(long b);
long prism_buf_utf8_valid(long b);

/* Read-only view of a buffer's raw bytes, for a C consumer that must copy the
 * payload verbatim (the file writer). Borrows; the pointer is valid only while
 * the caller holds a reference to `b`. Mirrors prism_str_data for strings. */
const unsigned char *prism_buf_ptr(long b);

#endif /* PRISM_BUFFER_H */
