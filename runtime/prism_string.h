/* Strings: the counted string cell, its byte/codepoint operations, the show
 * helpers for the scalar types, and the blake3 hash (the native half of the
 * `blake3` builtin). String cells carry inline UTF-8 bytes, not child cells. */
#ifndef PRISM_STRING_H
#define PRISM_STRING_H

#include "prism_internal.h"

/* Low-level string-cell access, shared with the integer, float, array, and IO
 * modules that read or build string cells directly. Both accessors resolve a
 * string view to its parent's bytes, so a reader that stays inside the returned
 * length needs no view case of its own. */
long *prism_str_alloc(long byte_len);
char *prism_str_data(long s);
long prism_str_len_bytes(long s);
/* A NUL-terminated copy of a string value's bytes, for the OS calls that take a
 * C string. A view's bytes run to its window's end with the parent's next byte
 * after them, so passing prism_str_data to a terminator-reading libc function
 * would read past the value; every such boundary allocates here instead. The
 * caller frees the result with free(). */
char *prism_str_cstr(long s);
/* True when a value is a string view rather than a materialized string cell.
 * Only a caller that must decide whether to pay for a terminated copy needs it;
 * ordinary readers stay inside the two accessors above, which answer for both. */
int prism_str_is_view(long s);
/* The `len` bytes of `s` from byte offset `lo` (exclusive upper bound `hi`),
 * clamped to the string's bounds. Returns a view sharing the parent's bytes
 * when both endpoints fall on UTF-8 character boundaries, and otherwise falls
 * back to the lossy decode that repairs a split sequence, which is what a
 * byte-level slice has always produced. */
long prism_prim_str_slice(long s, long lo, long hi);

long prism_str_lit(const char *src, long byte_len);
void print_str(long s);
long prism_str_concat(long a, long b);
long prism_str_len(long a);
long prism_byte_len(long s);
long prism_byte_at(long s, long i);
long prism_str_eq(long a, long b);
long prism_show_bool(long b);
long prism_show_char(long cp);
long prism_blake3(long s);
/* blake3 of a raw byte span as lowercase hex; shared with the buffer module. */
long prism_blake3_bytes(const void *data, long len);
long prism_substring(long s, long start, long len);
long prism_char_at(long s, long i);
long prism_str_cmp(long a, long b);
/* ASCII whitespace predicate, shared with the integer string parser. */
int prism_ws(char c);

#endif /* PRISM_STRING_H */
