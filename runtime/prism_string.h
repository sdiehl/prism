/* Strings: the counted string cell, its byte/codepoint operations, the show
 * helpers for the scalar types, and the blake3 hash (the native half of the
 * `blake3` builtin). String cells carry inline UTF-8 bytes, not child cells. */
#ifndef PRISM_STRING_H
#define PRISM_STRING_H

#include "prism_internal.h"

/* Low-level string-cell access, shared with the integer, float, array, and IO
 * modules that read or build string cells directly. */
long *prism_str_alloc(long byte_len);
char *prism_str_data(long s);
long prism_str_len_bytes(long s);

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
