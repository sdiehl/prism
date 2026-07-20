/* Memory core: allocation, tagged immediates, Perceus reference counting, FBIP
 * reuse, local mutable refs, the `with_arena` region policy, and the runtime
 * instrumentation counters. */
#include "prism_arena.h"
#include "prism_mem.h"

/* Live-cell balance, the box-1 acceptance oracle: every prism_alloc bumps it,
 * every freed cell drops it. With PRISM_CHECK_LEAKS set, a destructor prints the
 * final balance to stderr at exit; a clean run reports zero. stderr keeps stdout
 * (the parity-checked channel) untouched, so normal runs are byte-identical. */
long prism_live_cells = 0;

__attribute__((destructor)) static void prism_leak_report(void) {
    if (getenv("PRISM_CHECK_LEAKS")) {
        fprintf(stderr, "prism: %ld cells leaked\n", prism_live_cells);
    }
}

/* Total-allocation counter, the per-pipeline fusion oracle for pull sequences.
 * A lazy `Sequence` runs no algebraic effects, so the EOp counter is vacuously
 * zero on it and cannot see a fusion regression; what a stream materializes is
 * heap cells (one `SMore` cons plus its step thunk per element per unfused
 * stage). Every prism_alloc bumps this monotonically, so a fused pipeline can be
 * asserted to allocate O(1) cells while an unfused one grows one-per-element.
 * FBIP reuse bypasses prism_alloc (prism_reuse_alloc recycles the cell in
 * place), so a recycled cell is correctly NOT counted here: this measures cells
 * genuinely materialized, not cells constructed. stderr keeps stdout (the
 * parity-checked channel) untouched, so counted runs stay byte-identical. */
static long prism_alloc_total = 0;

__attribute__((destructor)) static void prism_alloc_report(void) {
    if (getenv("PRISM_ALLOC_STATS")) {
        fprintf(stderr, "prism: %ld cells allocated\n", prism_alloc_total);
    }
}

/* Checked header+payload byte size. A hostile or computed word count must never
 * overflow the size argument to malloc: an overflow would under-allocate and the
 * subsequent field stores would write out of bounds. Reject a negative count (a
 * corrupt length) and any add/mul overflow, aborting rather than handing back an
 * undersized cell. */
size_t prism_cell_bytes(long n_words) {
    size_t words, bytes;
    if (n_words < 0) abort();
    if (__builtin_add_overflow((size_t)PRISM_HDR_WORDS, (size_t)n_words, &words)) abort();
    if (__builtin_mul_overflow(words, (size_t)8, &bytes)) abort();
    return bytes;
}

void *prism_alloc(long n_words) {
    long *p = malloc(prism_cell_bytes(n_words));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = 0;
    p[PRISM_ARITY_W] = n_words;
    prism_live_cells++;
    prism_alloc_total++;
    return p;
}

/* Build a constructor cell { rc, tag, arity, fields... }, mirroring the inline
 * cells codegen emits (prism_alloc + tag word + field words). Tags follow the
 * ADT's declaration order, so for the prelude's `Option(a) = None | Some(a)`
 * None=0/Some=1 and `Result(a, e) = Ok(a) | Err(e)` Ok=0/Err=1. */
long prism_ctor(long tag, long n, const long *fields) {
    long *p = prism_alloc(n);
    p[PRISM_TAG_W] = tag;
    for (long i = 0; i < n; i++) p[PRISM_HDR_WORDS + i] = fields[i];
    return (long)p;
}

/* ---- The `with_arena` region policy -------------------------------------
 *
 * One region per `with_arena` handler activation. The arena-lowering pass
 * emits `prism_arena_enter` before the handler and `prism_arena_exit` around
 * its result; the handler's `alloc` clause discharges into `prism_bump`, which
 * carves cells from the innermost open region. Activations bracket strictly
 * (the body of `with_arena` has the closed row `{Alloc}`, so no foreign effect
 * can unwind past the return clause, and `alloc` is graded `once`), so a plain
 * stack of regions is sound; the depth token makes any compiler bug that
 * unbalances the bracket a trap instead of a corruption.
 *
 * Arena cells carry PRISM_ARENA_OWNED in their rc word: dup/drop and the
 * child-scan are no-ops on them and the region is their sole owner. Their
 * refcounted children are owned as usual and released once, at exit, by
 * walking the region's cell registry (an intrusive chain threaded through a
 * link word bumped in front of every cell). Values may escape the region
 * through the handler's result; exit deep-promotes any arena-owned cell
 * reachable from the result into ordinary refcounted cells before the region
 * is destroyed, so escape costs a copy, never soundness. */

typedef struct PrismRegion {
    PrismArena *arena;
    long *cells; /* registry: head link word, each followed by its cell */
    struct PrismRegion *next;
    long depth; /* 1-based activation depth, the enter/exit pairing token */
} PrismRegion;

static PrismRegion *prism_region_top = NULL;

/* Arena bump. The arena-lowering pass rewrites a constructor built under a
 * `with_arena` scope into `alloc(n)` + `init_at`, and the handler discharges
 * the `alloc` into this call. Inside an activation the cell comes from the
 * region: no malloc, no live-cell accounting (the region owns it wholesale),
 * fields zeroed so a cell a handler never resumes into stays walkable. With no
 * open region (an `Alloc` handler outside `with_arena`, or a build without the
 * lowering) it delegates to `prism_alloc` and the cell is ordinary. */
long prism_bump(long n_words) {
    PrismRegion *r = prism_region_top;
    if (!r) return (long)prism_alloc(n_words);
    /* link word + { rc, tag, arity, fields } */
    size_t bytes = prism_ckd_words_bytes(
        prism_ckd_ladd(1 + PRISM_HDR_WORDS, n_words));
    long *w = prism_arena_alloc(r->arena, bytes);
    if (!w) abort();
    w[0] = (long)r->cells;
    r->cells = w;
    long *p = w + 1;
    p[PRISM_RC_W] = PRISM_ARENA_OWNED;
    p[PRISM_TAG_W] = 0;
    p[PRISM_ARITY_W] = n_words;
    for (long i = 0; i < n_words; i++) p[PRISM_HDR_WORDS + i] = 0;
    return (long)p;
}

long prism_arena_enter(void) {
    PrismRegion *r = malloc(sizeof *r);
    if (!r) abort();
    r->arena = prism_arena_create(0);
    if (!r->arena) abort();
    r->cells = NULL;
    r->next = prism_region_top;
    r->depth = prism_region_top ? prism_region_top->depth + 1 : 1;
    prism_region_top = r;
    return r->depth;
}

/* Whether the collector and the promotion walk may read a cell's payload words
 * as child values. Strings, bignums, and buffers hold inline bytes/limbs/words
 * behind the arity slot, not children; everything else (constructors, tuples,
 * closures, boxes, arrays) stores ordinary tagged values. */
static int prism_cell_has_children(const long *p) {
    long tag = p[PRISM_TAG_W];
    return tag != PRISM_STR_TAG && tag != PRISM_BIG_TAG && tag != PRISM_BUF_TAG &&
           tag != PRISM_TBUF_TAG;
}

/* A fresh refcounted copy of an arena cell's header (fields filled by the
 * promotion walk). Only constructor/tuple cells are ever arena-allocated, so
 * arity is always a genuine field count here. */
static long *prism_promote_shell(const long *p) {
    long *q = prism_alloc(p[PRISM_ARITY_W]);
    q[PRISM_TAG_W] = p[PRISM_TAG_W];
    return q;
}

/* One step of the iterative promotion walk: fields [i..arity) of `src` remain
 * to visit. `dst` is the refcounted copy being filled when `src` is an arena
 * cell, or NULL when `src` is an ordinary cell whose arena-valued fields are
 * rewritten in place. */
typedef struct {
    long *src;
    long *dst;
    long i;
} PrismPromoteFrame;

/* Deep-promote every arena-owned cell reachable from `v` into ordinary
 * refcounted cells. `v` is borrowed; the result is an owned reference (the
 * original when nothing was arena-owned at the root). Iterative with an
 * explicit worklist, like prism_rc_dec, so escaping structures of any depth
 * promote in bounded C stack. Values are acyclic (data is immutable and refs
 * cannot capture themselves), so the walk terminates; shared arena cells are
 * duplicated per path, which preserves the value and is unobservable. */
static long prism_promote(long v) {
    if ((v & 1) || !v) return v;
    long *root = (long *)v;
    PrismPromoteFrame *stack = NULL;
    size_t sp = 0, cap = 0;
    long out;
    if (root[PRISM_RC_W] & PRISM_ARENA_OWNED) {
        long *q = prism_promote_shell(root);
        out = (long)q;
        stack = malloc(sizeof *stack);
        if (!stack) abort();
        cap = 1;
        stack[sp++] = (PrismPromoteFrame){root, q, 0};
    } else {
        prism_rc_inc(v); /* borrowed in, owned result out */
        out = v;
        if (prism_cell_has_children(root)) {
            stack = malloc(sizeof *stack);
            if (!stack) abort();
            cap = 1;
            stack[sp++] = (PrismPromoteFrame){root, NULL, 0};
        }
    }
    while (sp) {
        PrismPromoteFrame *f = &stack[sp - 1];
        if (f->i >= f->src[PRISM_ARITY_W]) {
            sp--;
            continue;
        }
        long idx = f->i;
        f->i++;
        long c = f->src[PRISM_HDR_WORDS + idx];
        if ((c & 1) || !c) {
            if (f->dst) f->dst[PRISM_HDR_WORDS + idx] = c;
            continue;
        }
        long *cp = (long *)c;
        PrismPromoteFrame next;
        if (cp[PRISM_RC_W] & PRISM_ARENA_OWNED) {
            long *q = prism_promote_shell(cp);
            (f->dst ? f->dst : f->src)[PRISM_HDR_WORDS + idx] = (long)q;
            next = (PrismPromoteFrame){cp, q, 0};
        } else {
            if (f->dst) {
                prism_rc_inc(c); /* the copy takes its own reference */
                f->dst[PRISM_HDR_WORDS + idx] = c;
            }
            if (!prism_cell_has_children(cp)) continue;
            next = (PrismPromoteFrame){cp, NULL, 0};
        }
        if (sp == cap) { /* grow; `f` is dead past this point */
            size_t ncap = cap * 2;
            PrismPromoteFrame *ns = realloc(stack, ncap * sizeof *ns);
            if (!ns) abort();
            stack = ns;
            cap = ncap;
        }
        stack[sp++] = next;
    }
    free(stack);
    return out;
}

long prism_arena_exit(long token, long v) {
    PrismRegion *r = prism_region_top;
    if (!r || r->depth != token) {
        fprintf(stderr, "fatal: unbalanced arena exit (token %ld, depth %ld)\n", token,
                r ? r->depth : 0);
        abort();
    }
    long out = prism_promote(v);
    /* Release the refcounted children the region's cells own. Arena-owned
     * children die with the region itself; the promotion above already took
     * fresh references for everything the escaping value keeps. */
    for (long *lw = r->cells; lw; lw = (long *)*lw) {
        long *cell = lw + 1;
        long n = cell[PRISM_ARITY_W];
        for (long i = 0; i < n; i++) {
            long c = cell[PRISM_HDR_WORDS + i];
            if ((c & 1) || !c) continue;
            if (((long *)c)[PRISM_RC_W] & PRISM_ARENA_OWNED) continue;
            prism_rc_dec(c);
        }
    }
    /* Consume the caller's reference to `v` (this builtin's one deviation from
     * the borrowed-argument convention, mirrored in codegen): when `v` is an
     * arena cell, even the no-op release reads its header for the arena bit, so
     * it must happen here, before the region backing that header is freed. */
    prism_rc_dec(v);
    prism_region_top = r->next;
    prism_arena_destroy(r->arena);
    free(r);
    return out;
}

/* A box is an arity-0 cell whose single payload word holds one opaque i64: the
 * raw double bits for a float. Boxing makes a float a self-describing cell, so a
 * float field of a constructor is safe for prism_rc_dec to free without
 * recursing into the payload. The backends unbox at every float-op boundary. */
long prism_box(long payload) {
    long *p = prism_alloc(1);
    p[PRISM_ARITY_W] = 0;
    p[PRISM_HDR_WORDS] = payload;
    return (long)p;
}

/* Optional in-binary structural backstop. A compiled program's memory safety
 * otherwise rests entirely on codegen emitting correct tags, refcounts, and
 * field indices: a tagging or rc bug is plain UB with no trap in a shipped
 * binary. Building the runtime with -DPRISM_RT_DEBUG (the canonical PRISM_RT_CHECKS
 * knob adds it to the cc invocation; PRISM_CC_FLAGS=-DPRISM_RT_DEBUG also works)
 * inserts a cheap validity check at every cell
 * dereference: the value must be a non-null, 8-byte-aligned heap pointer (low
 * tag bit clear) carrying a positive refcount, and a constructor field read must
 * be in bounds. A violation aborts with a diagnostic instead of corrupting
 * memory. Compiled out entirely (zero overhead) by default, so release builds
 * and the parity oracle stay byte-identical. ASan/UBSan remain the gold standard
 * in CI; this is the always-available, no-instrumentation net for builds where
 * sanitizers are unavailable. */
#ifdef PRISM_RT_DEBUG
static void prism_rt_check(long p, const char *who) {
    if (p == 0 || (p & 1L)) {
        fprintf(stderr, "prism_rt: %s on non-cell value 0x%lx\n", who, (unsigned long)p);
        abort();
    }
    if (((unsigned long)p) & 7UL) {
        fprintf(stderr, "prism_rt: %s on misaligned pointer 0x%lx\n", who, (unsigned long)p);
        abort();
    }
    long rc = ((long *)p)[PRISM_RC_W];
    if (rc <= 0) {
        fprintf(stderr, "prism_rt: %s on cell 0x%lx with non-positive rc %ld (use-after-free?)\n",
                who, (unsigned long)p, rc);
        abort();
    }
}
#define PRISM_RT_CHECK(p, who) prism_rt_check((long)(p), (who))
#else
#define PRISM_RT_CHECK(p, who) ((void)0)
#endif

long prism_unbox(long p) {
    PRISM_RT_CHECK(p, "prism_unbox");
    return ((long *)p)[PRISM_HDR_WORDS];
}

/* inc/dec take the raw i64 value, not a pointer: immediates (low bit set) and
 * unit (zero) are skipped without a dereference, so dup/drop stay no-ops on
 * non-cell values under polymorphism. dec frees a cell's children before the
 * cell; a string cell holds inline bytes rather than child cells, so its tag
 * short-circuits the traversal. */
void prism_rc_inc(long v) {
    if ((v & 1) || !v) return;
    long *p = (long *)v;
    /* An arena-owned cell's sole owner is its region: inert. */
    if (p[PRISM_RC_W] & PRISM_ARENA_OWNED) return;
    p[PRISM_RC_W]++;
}

/* Freeing is iterative via an intrusive worklist: a dead cell's rc word (now 0,
 * doubling as the NULL terminator) is reused as the next link of a pending free
 * list, so arbitrarily deep structures drop in O(1) extra space with no
 * allocation instead of recursing once per child on the C stack. */
void prism_rc_dec(long v) {
    if ((v & 1) || !v) return;
    long *p = (long *)v;
    /* Arena-owned: the region reclaims it wholesale, never this collector. */
    if (p[PRISM_RC_W] & PRISM_ARENA_OWNED) return;
    if (--p[PRISM_RC_W] != 0) return;
    while (p) {
        long *next = (long *)p[PRISM_RC_W];
        long dtag = p[PRISM_TAG_W];
        if (dtag != PRISM_STR_TAG && dtag != PRISM_BIG_TAG && dtag != PRISM_BUF_TAG &&
            dtag != PRISM_TBUF_TAG) {
            long n = p[PRISM_ARITY_W];
            for (long i = 0; i < n; i++) {
                long c = p[PRISM_HDR_WORDS + i];
                if ((c & 1) || !c) continue;
                long *cp = (long *)c;
                /* An arena-owned child is the region's, not this cell's, so the
                 * cascade must neither decrement nor free it. Only live children
                 * are inspected here, so the rc word read is always a genuine
                 * count (never a worklist link). */
                if (cp[PRISM_RC_W] & PRISM_ARENA_OWNED) continue;
                if (--cp[PRISM_RC_W] == 0) {
                    cp[PRISM_RC_W] = (long)next;
                    next = cp;
                }
            }
        }
        free(p);
        prism_live_cells--;
        p = next;
    }
}

/* A var cell: an arity-1 mutable cell holding one owned value. Escape-checked
 * local mutable state (`var x := e`) compiles to one of these, so reads and
 * writes are loads/stores and a `var` loop is a real constant-stack loop instead
 * of the algebraic-effect free monad. `prism_ref_set` overwrites the field in
 * place regardless of the cell's refcount: sound because the cell never aliases a
 * distinct value, established before this lowering by two independent compile-time
 * checks (an escape analysis over the handled block, with principal effect-row
 * inference as the backstop: a `var` op that slips past the syntactic check still
 * surfaces as an unhandled private `Var@..` effect). The cell is an ordinary
 * arity-1 cell, so `prism_rc_dec` frees its field
 * with it; the caller (codegen) owns the cell reference and rc_decs it after each
 * read/write, the rc pass having dup'd so each use has its own reference. */
long prism_ref_new(long v) {
    long *p = prism_alloc(1); /* rc=1, arity=1 */
    p[PRISM_HDR_WORDS] = v;   /* v moves into the cell */
    return (long)p;
}

long prism_ref_get(long c) {
    long e = ((long *)c)[PRISM_HDR_WORDS];
    prism_rc_inc(e); /* an owned snapshot; the caller rc_decs the cell */
    return e;
}

void prism_ref_set(long c, long v) {
    PRISM_RT_CHECK(c, "prism_ref_set");
    long *p = (long *)c;
    /* The store lands in field 0, so the cell must have at least one field. A
     * var cell is always arity 1 by construction (prism_ref_new), so this never
     * fires for correct codegen and shipped output stays byte-identical; it is a
     * load+compare on the arity word, already on the header cache line the field
     * access below touches, so the guard is always on and turns a mis-issued
     * ref_set into a trap instead of an out-of-bounds write. */
    if (p[PRISM_ARITY_W] < 1) {
        fprintf(stderr, "fatal: ref_set on a cell with no field (arity %ld)\n", p[PRISM_ARITY_W]);
        abort();
    }
    prism_rc_dec(p[PRISM_HDR_WORDS]); /* free the old value */
    p[PRISM_HDR_WORDS] = v;           /* v moves into the cell */
}

/* FBIP reuse (Lorenzen and Leijen, "Reference Counting with Frame-Limited
 * Reuse"): a uniquely-owned cell about to be dropped is turned into a reuse
 * token and handed to the matching constructor allocation in the same arm, so
 * the cell is overwritten in place instead of freed and re-malloced. The token
 * call recurses into the old children exactly as prism_rc_dec would, but keeps
 * the shell when rc is 1 (returning it) and returns 0 otherwise (a shared cell
 * is decremented and allocation falls back to malloc). Either way the live-cell
 * counter is untouched, so a reused cell neither leaks nor double-counts. */
static long prism_reuse_hits = 0;

__attribute__((destructor)) static void prism_reuse_report(void) {
    if (getenv("PRISM_REUSE_STATS")) {
        fprintf(stderr, "prism: %ld cells reused\n", prism_reuse_hits);
    }
}

/* Effect-op allocation counter: every EOp cell the free-monad lowering builds
 * for a `do op` bumps this. With PRISM_EFFOP_STATS set a destructor reports the
 * total to stderr, leaving stdout (the parity-checked channel) untouched, so a
 * fused pipeline can be asserted to allocate zero EOp cells while a genuinely
 * escaping effect's fallback count stays observable. */
static long prism_effop_allocs = 0;

__attribute__((destructor)) static void prism_effop_report(void) {
    if (getenv("PRISM_EFFOP_STATS")) {
        fprintf(stderr, "prism: %ld eff ops allocated\n", prism_effop_allocs);
    }
}

void prism_effop_alloc(void) {
    prism_effop_allocs++;
}

/* Driver work-step counter: every structural reduction turn of the residual
 * free-monad driver (an `ebind`/handler/mask driver entry) bumps this. With
 * PRISM_DRIVE_STATS set a destructor reports the total to stderr (stdout, the
 * parity-checked channel, stays untouched). Unlike the allocation counter this
 * tracks the driver's actual *work*, so it scales ~n on a deep non-tail effectful
 * recursion when the trampoline is linear and flips to ~n^2 when it is not (the
 * EBounce-class re-association blowup that allocation counts are blind to). */
static long prism_drive_steps = 0;

__attribute__((destructor)) static void prism_drive_report(void) {
    if (getenv("PRISM_DRIVE_STATS")) {
        fprintf(stderr, "prism: %ld drive steps\n", prism_drive_steps);
    }
}

void prism_drive_step(void) {
    prism_drive_steps++;
}

long prism_reuse_token(long v) {
    if ((v & 1) || !v) return 0;
    long *p = (long *)v;
    /* An arena-owned cell is never uniquely owned by the dropping frame (the
     * region owns it), so it can never become a reuse shell; its rc word must
     * also stay untouched. Constructing over it falls back to fresh allocation. */
    if (p[PRISM_RC_W] & PRISM_ARENA_OWNED) return 0;
    if (p[PRISM_TAG_W] == PRISM_STR_TAG || p[PRISM_TAG_W] == PRISM_BIG_TAG ||
        p[PRISM_TAG_W] == PRISM_BUF_TAG || p[PRISM_TAG_W] == PRISM_TBUF_TAG)
        return 0;
    if (p[PRISM_RC_W] == 1) {
        long n = p[PRISM_ARITY_W];
        for (long i = 0; i < n; i++) prism_rc_dec(p[PRISM_HDR_WORDS + i]);
        prism_reuse_hits++;
        return v;
    }
    p[PRISM_RC_W]--;
    return 0;
}

void *prism_reuse_alloc(long token, long n_words) {
    if (token) {
        long *p = (long *)token;
        /* FBIP reuse is compiler-trusted: the shell was allocated for its old
         * arity, so recycling it for a larger payload would write past the
         * allocation. A codegen bug here is a silent heap overflow, so the guard
         * is always on: it is one integer compare against the arity word already
         * loaded on this path, and it never fires for correct codegen, so shipped
         * binaries stay byte-identical while a growth bug traps instead of
         * corrupting the heap. */
        if (n_words > p[PRISM_ARITY_W]) {
            fprintf(stderr, "fatal: reuse_alloc grows a cell (%ld > %ld words)\n", n_words,
                    p[PRISM_ARITY_W]);
            abort();
        }
        p[PRISM_RC_W] = 1;
        p[PRISM_TAG_W] = 0;
        p[PRISM_ARITY_W] = n_words;
        return p;
    }
    return prism_alloc(n_words);
}

long prism_tag(void *p) {
    PRISM_RT_CHECK(p, "prism_tag");
    return ((long *)p)[PRISM_TAG_W];
}

long prism_field(void *p, long i) {
    PRISM_RT_CHECK(p, "prism_field");
#ifdef PRISM_RT_DEBUG
    {
        long tag = ((long *)p)[PRISM_TAG_W];
        long arity = ((long *)p)[PRISM_ARITY_W];
        /* String/bignum/buffer cells carry an inline byte/limb payload, not child
         * fields, so their arity slot is a length or payload-word count, not a
         * field count: skip the bounds check for them (prism_field is not a valid
         * accessor there). */
        if (tag != PRISM_STR_TAG && tag != PRISM_BIG_TAG && tag != PRISM_BUF_TAG &&
            (i < 0 || i >= arity)) {
            fprintf(stderr, "prism_rt: prism_field index %ld out of bounds (arity %ld)\n", i,
                    arity);
            abort();
        }
    }
#endif
    return ((long *)p)[PRISM_HDR_WORDS + i];
}
