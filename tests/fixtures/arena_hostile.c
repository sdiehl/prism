/* Hostile-input harness for the `with_arena` region policy in prism_mem.c.
 *
 * Drives the runtime's own entry points (never codegen) through the shapes a
 * compiler bug or hostile lowering could produce: zero-arity and oversized
 * bumps, block-chain growth, refcount traffic against arena-owned cells,
 * escape promotion over shared/DAG/deep structures, cross-region references,
 * release of refcounted children at region destruction, and the unbalanced
 * exit trap. Properties checked: arena cells are refcount-inert; promotion
 * yields a structurally equal, arena-free copy in bounded C stack; the
 * live-cell balance returns to its baseline after every scenario; a mismatched
 * bracket aborts instead of corrupting.
 *
 * Compiled and run by `arena_region_hostile_harness` in src/codegen/rt.rs
 * against the materialized embedded runtime, the same flow as the kont lookup
 * harness.
 */
#include <assert.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "prism_internal.h"
#include "prism_mem.h"

#define IMM(n) ((((long)(n)) << 1) | 1)

/* Build an arena constructor the way codegen's `init_at` does: bump a raw
 * cell, then store the tag and owned field values. */
static long arena_ctor(long tag, long n, const long *fields) {
    long cell = prism_bump(n);
    long *p = (long *)cell;
    assert(p[PRISM_ARITY_W] == n);
    p[PRISM_TAG_W] = tag;
    for (long i = 0; i < n; i++) p[PRISM_HDR_WORDS + i] = fields[i];
    return cell;
}

static int is_cell(long v) {
    return v && !(v & 1);
}

static int is_arena(long v) {
    return is_cell(v) && (((long *)v)[PRISM_RC_W] & PRISM_ARENA_OWNED) != 0;
}

/* Structural equality over cells and immediates, recursion bounded by the
 * shallow scenarios that use it (the deep chain is checked iteratively). */
static int value_eq(long a, long b) {
    if (a == b) return 1;
    if (!is_cell(a) || !is_cell(b)) return 0;
    long *pa = (long *)a, *pb = (long *)b;
    if (pa[PRISM_TAG_W] != pb[PRISM_TAG_W] || pa[PRISM_ARITY_W] != pb[PRISM_ARITY_W]) return 0;
    for (long i = 0; i < pa[PRISM_ARITY_W]; i++) {
        if (!value_eq(pa[PRISM_HDR_WORDS + i], pb[PRISM_HDR_WORDS + i])) return 0;
    }
    return 1;
}

/* No arena-owned cell anywhere under `v`. */
static int arena_free_deep(long v) {
    if (!is_cell(v)) return 1;
    if (is_arena(v)) return 0;
    long *p = (long *)v;
    for (long i = 0; i < p[PRISM_ARITY_W]; i++) {
        if (!arena_free_deep(p[PRISM_HDR_WORDS + i])) return 0;
    }
    return 1;
}

/* A. With no open region, bump is ordinary allocation. */
static void no_region_delegates(void) {
    long base = prism_live_cells;
    long cell = prism_bump(2);
    long *p = (long *)cell;
    assert(p[PRISM_RC_W] == 1 && !is_arena(cell));
    assert(prism_live_cells == base + 1);
    p[PRISM_TAG_W] = 0;
    p[PRISM_HDR_WORDS] = IMM(1);
    p[PRISM_HDR_WORDS + 1] = IMM(2);
    prism_rc_dec(cell);
    assert(prism_live_cells == base);
}

/* B. Region lifecycle under hostile sizes: zero arity, block-chain growth, and
 * refcount inertness of every cell handed out. */
static void region_lifecycle(void) {
    long base = prism_live_cells;
    long tok = prism_arena_enter();
    long zero = prism_bump(0);
    assert(is_arena(zero) && ((long *)zero)[PRISM_ARITY_W] == 0);
    assert(((unsigned long)zero & 7UL) == 0);
    /* Enough 8-word cells to outgrow the default 64K block several times. */
    long prev = 0;
    for (int i = 0; i < 3000; i++) {
        long c = prism_bump(8);
        long *p = (long *)c;
        assert(is_arena(c) && ((unsigned long)c & 7UL) == 0);
        assert(p[PRISM_TAG_W] == 0 && p[PRISM_ARITY_W] == 8);
        for (long w = 0; w < 8; w++) assert(p[PRISM_HDR_WORDS + w] == 0);
        assert(c != prev);
        prev = c;
        /* Inert: inc, dec, and token leave the header word untouched. */
        long rc = p[PRISM_RC_W];
        prism_rc_inc(c);
        prism_rc_dec(c);
        assert(prism_reuse_token(c) == 0);
        assert(p[PRISM_RC_W] == rc);
    }
    /* An oversized request larger than the block size is still served. */
    long big = prism_bump(20000);
    assert(is_arena(big) && ((long *)big)[PRISM_ARITY_W] == 20000);
    /* Nothing above touched the ordinary allocator. */
    assert(prism_live_cells == base);
    long out = prism_arena_exit(tok, IMM(7));
    assert(out == IMM(7));
    assert(prism_live_cells == base);
}

/* C. Escape promotion over an adversarial mixed shape: a shared arena child
 * reached twice (duplicated per path), an ordinary refcounted cell in the
 * middle whose arena field must be rewritten in place, and refcounted leaves
 * owned by arena cells. */
static void promotion_dag(void) {
    long base = prism_live_cells;
    long tok = prism_arena_enter();

    long leaf_fields[1] = {IMM(11)};
    long rc_leaf = prism_ctor(1, 1, leaf_fields); /* ordinary cell */
    long shared_fields[1] = {IMM(5)};
    long shared = arena_ctor(2, 1, shared_fields); /* arena cell reached twice */
    long mid_fields[2] = {shared, IMM(9)};
    /* Ordinary cell holding an arena child: promotion must rewrite in place. */
    long rc_mid = prism_ctor(3, 2, mid_fields);
    long root_fields[4] = {rc_mid, shared, IMM(1), rc_leaf};
    long root = arena_ctor(4, 4, root_fields);

    long out = prism_arena_exit(tok, root);
    long *op = (long *)out;
    assert(is_cell(out) && !is_arena(out));
    assert(arena_free_deep(out));
    assert(op[PRISM_TAG_W] == 4 && op[PRISM_ARITY_W] == 4);
    /* The shared arena child was reached by two paths; each got its own
     * refcounted copy, structurally equal. */
    long via_mid = ((long *)op[PRISM_HDR_WORDS])[PRISM_HDR_WORDS];
    long direct = op[PRISM_HDR_WORDS + 1];
    assert(via_mid != direct && value_eq(via_mid, direct));
    /* The ordinary middle cell was kept (not copied), fields rewritten. */
    assert(op[PRISM_HDR_WORDS] == rc_mid);
    assert(op[PRISM_HDR_WORDS + 3] == rc_leaf);
    prism_rc_dec(out);
    assert(prism_live_cells == base);
}

/* D. A deep arena chain promotes and frees without growing the C stack: both
 * the promotion walk and the collector are iterative. */
static void promotion_deep_chain(void) {
    enum { DEPTH = 200000 };
    long base = prism_live_cells;
    long tok = prism_arena_enter();
    long chain = IMM(0); /* nil */
    for (int i = 0; i < DEPTH; i++) {
        long fields[2] = {IMM(i), chain};
        chain = arena_ctor(1, 2, fields);
    }
    long out = prism_arena_exit(tok, chain);
    long depth = 0;
    for (long v = out; is_cell(v); v = ((long *)v)[PRISM_HDR_WORDS + 1]) {
        assert(!is_arena(v));
        depth++;
    }
    assert(depth == DEPTH);
    prism_rc_dec(out);
    assert(prism_live_cells == base);
}

/* E. Nested regions: an outer arena cell referenced from the inner region's
 * escaping value is promoted at the inner exit (promotion cannot and need not
 * distinguish regions), and the outer region still reclaims cleanly. */
static void nested_regions(void) {
    long base = prism_live_cells;
    long tok1 = prism_arena_enter();
    long outer_fields[1] = {IMM(21)};
    long outer_cell = arena_ctor(1, 1, outer_fields);
    long tok2 = prism_arena_enter();
    long inner_fields[2] = {IMM(2), outer_cell};
    long inner_cell = arena_ctor(2, 2, inner_fields);
    long promoted = prism_arena_exit(tok2, inner_cell);
    assert(arena_free_deep(promoted));
    assert(((long *)promoted)[PRISM_HDR_WORDS + 1] != outer_cell);
    /* The outer region is intact: its cell still carries the arena bit and its
     * exit still balances. */
    assert(is_arena(outer_cell));
    long out = prism_arena_exit(tok1, IMM(3));
    assert(out == IMM(3));
    prism_rc_dec(promoted);
    assert(prism_live_cells == base);
}

/* F. Refcounted children owned by arena cells are released exactly once, at
 * region destruction, when nothing escapes. */
static void children_released_at_destroy(void) {
    long base = prism_live_cells;
    long tok = prism_arena_enter();
    long leaf_fields[1] = {IMM(1)};
    long rc_child = prism_ctor(1, 1, leaf_fields);
    assert(prism_live_cells == base + 1);
    long holder_fields[2] = {rc_child, rc_child};
    prism_rc_inc(rc_child); /* the second field takes its own reference */
    long holder = arena_ctor(2, 2, holder_fields);
    (void)holder;
    long out = prism_arena_exit(tok, IMM(0));
    assert(out == IMM(0));
    assert(prism_live_cells == base);
}

/* G. A mismatched bracket traps. The child closes stderr so the diagnostic
 * stays out of the harness output. */
static void unbalanced_exit_traps(void) {
    pid_t pid = fork();
    assert(pid >= 0);
    if (pid == 0) {
        close(2);
        long tok = prism_arena_enter();
        (void)prism_arena_exit(tok + 1, IMM(0)); /* wrong token: must abort */
        _exit(0);                                /* unreachable on a correct runtime */
    }
    int status = 0;
    assert(waitpid(pid, &status, 0) == pid);
    assert(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
}

/* The runtime's own `main` shim (prism_io.c) drives the generated entry
 * symbol; the harness stands in for a generated program by defining it. The
 * tagged-immediate return is the process exit code. */
long prismfn_main(void) {
    no_region_delegates();
    region_lifecycle();
    promotion_dag();
    promotion_deep_chain();
    nested_regions();
    children_released_at_destroy();
    unbalanced_exit_traps();
    printf("arena_hostile: OK\n");
    return IMM(0);
}
