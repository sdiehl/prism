/* Memory core: allocation, tagged immediates, Perceus reference counting, FBIP
 * reuse, local mutable refs, and the runtime instrumentation counters. */
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
    ((long *)v)[PRISM_RC_W]++;
}

/* Freeing is iterative via an intrusive worklist: a dead cell's rc word (now 0,
 * doubling as the NULL terminator) is reused as the next link of a pending free
 * list, so arbitrarily deep structures drop in O(1) extra space with no
 * allocation instead of recursing once per child on the C stack. */
void prism_rc_dec(long v) {
    if ((v & 1) || !v) return;
    long *p = (long *)v;
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
