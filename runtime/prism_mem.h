/* Memory core: cell allocation, the tagged-immediate scheme, Perceus reference
 * counting, FBIP reuse, local mutable refs, and the runtime instrumentation
 * counters. Every other module allocates and reference-counts through here. */
#ifndef PRISM_MEM_H
#define PRISM_MEM_H

#include "prism_internal.h"

/* Live-cell balance (the leak oracle). Bumped by every cell allocator, including
 * the string and bignum allocators in their own modules, and dropped by the
 * reference-count collector here, so it is shared rather than module-local. */
extern long prism_live_cells;

/* Checked header+payload byte size for an n-word cell; shared with the string
 * and bignum allocators so the overflow guard has one definition. */
size_t prism_cell_bytes(long n_words);

void *prism_alloc(long n_words);
/* Arena bump: hand out a raw n-word cell for a constructor the arena-lowering
 * pass split into `alloc` + `init_at`. It delegates to `prism_alloc`, so an arena
 * constructor is byte-identical to an ordinary one. Returns the cell as a
 * `long`, the representation `init_at` fills. */
long prism_bump(long n_words);
/* Build a constructor cell { rc, tag, arity, fields... }; shared with the effect,
 * integer, and IO modules that assemble tagged cells (queues, boxed ints, Result
 * values). */
long prism_ctor(long tag, long n, const long *fields);
long prism_box(long payload);
long prism_unbox(long p);
void prism_rc_inc(long v);
void prism_rc_dec(long v);
long prism_reuse_token(long v);
void *prism_reuse_alloc(long token, long n_words);
long prism_ref_new(long v);
long prism_ref_get(long c);
void prism_ref_set(long c, long v);
long prism_tag(void *p);
long prism_field(void *p, long i);
void prism_effop_alloc(void);
void prism_drive_step(void);

#endif /* PRISM_MEM_H */
