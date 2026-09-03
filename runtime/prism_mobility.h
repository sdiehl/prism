/* The mobility envelope: freezing a portable, single-use computation into bytes
 * and landing those bytes back into a running machine. A native binary has no
 * machine to land one in, so both entry points are classified refusals here (see
 * prism_mobility.c) rather than absent symbols the linker would trip over. */
#ifndef PRISM_MOBILITY_H
#define PRISM_MOBILITY_H

#include "prism_internal.h"

long prism_prim_kont_encode(long work);
long prism_prim_kont_resume(long envelope);

#endif /* PRISM_MOBILITY_H */
