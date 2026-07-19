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
 * pass split into `alloc` + `init_at`. Inside a `with_arena` activation the cell
 * is carved from that activation's region and marked arena-owned
 * (refcount-inert); with no active region it delegates to `prism_alloc`, so the
 * cell is byte-identical to an ordinary one. Returns the cell as a `long`, the
 * representation `init_at` fills. */
long prism_bump(long n_words);
/* Region brackets, emitted by the arena-lowering pass around each `with_arena`
 * handler activation. `enter` opens a region and returns its activation depth,
 * a token `exit` checks so the pair can never silently unbalance. `exit`
 * promotes every arena-owned cell reachable from `v` into ordinary refcounted
 * cells (a value may escape its region), releases the refcounted children the
 * region's cells own, reclaims the whole region, and returns the promoted
 * value (owned by the caller). Unlike every other builtin, `exit` CONSUMES `v`:
 * the caller's release of an arena-owned `v` would read a header the reclaimed
 * region no longer backs, so the release happens inside, and codegen emits no
 * post-call dec for it. */
long prism_arena_enter(void);
long prism_arena_exit(long token, long v);
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
