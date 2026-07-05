/* Growable arrays and the array-to-string conversions (codepoint arrays and raw
 * UTF-8 byte arrays). Arrays are ordinary constructor cells with a length and a
 * capacity ahead of the elements. */
#ifndef PRISM_ARRAY_H
#define PRISM_ARRAY_H

#include "prism_internal.h"

/* Does not return: prints to stderr and exits (see prism_io.h's traps). */
_Noreturn void prism_array_oob(void);
long prism_array_empty(void);
long prism_array_new(long n, long init);
long prism_array_len(long a);
long prism_array_get(long a, long i);
long prism_array_set(long a, long i, long x);
long prism_array_push(long a, long x);
long prism_array_pop(long a);
long prism_string_of_array(long arr);
long prism_string_of_bytes(long arr);
/* Lossy UTF-8 decode of a raw byte span into a fresh string cell (ill-formed
 * sequences become U+FFFD); shared with the buffer module. */
long prism_string_of_raw(const unsigned char *raw, long n);
/* True when a raw byte span is well-formed UTF-8; shared with the buffer module. */
int prism_utf8_valid(const unsigned char *raw, long n);

#endif /* PRISM_ARRAY_H */
