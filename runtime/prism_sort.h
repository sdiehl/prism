/* The polymorphic sort primitive: a stable merge sort with a radix fast path,
 * keyed by the element kind (int, float, string). */
#ifndef PRISM_SORT_H
#define PRISM_SORT_H

#include "prism_internal.h"

long prism_sort_prim(long kind, long list);

#endif /* PRISM_SORT_H */
