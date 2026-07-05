/* Effects and continuations: the type-aligned continuation queue (the Freer
 * representation of an EOp's continuation), the reified driver frames
 * (bind/handle/mask), and the constant-stack continuation splice. */
#ifndef PRISM_EFFECT_H
#define PRISM_EFFECT_H

#include "prism_internal.h"

long prism_taq_snoc(long q, long arrow);
long prism_taq_concat(long q1, long q2);
long prism_taq_uncons(long q);
long prism_frame_bind(long next, long kfn, long env);
long prism_frame_handle(long next, long table, long env);
long prism_frame_mask(long next, long ops);
long prism_kont_splice(long top, long base);

#endif /* PRISM_EFFECT_H */
