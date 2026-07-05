/* Effects and continuations: the type-aligned continuation queue, the reified
 * driver frames, and the constant-stack continuation splice. */
#include "prism_effect.h"
#include "prism_mem.h"

/* Type-aligned continuation queue (the Freer representation of an EOp's
 * continuation). A queue is a persistent binary tree of Kleisli arrows (thunks):
 * the empty queue is 0 (unit, rc-skipped), a Leaf holds one arrow, a Node joins
 * two non-empty queues. snoc and concat are O(1) (one Node); uncons walks the
 * left spine, re-associating Node(Node(a,b),c) -> Node(a,Node(b,c)) so a queue
 * built by repeated snoc drains in amortized O(1) per element -- the exact
 * re-association the old EBounce trampoline redid on every bounce (O(n^2)), done
 * here once. The tree is never mutated, only rebuilt sharing its leaves, so a
 * captured continuation is cloneable for multishot; rc is the existing Perceus
 * discipline (a retained child is rc_inc'd; the runtime-call wrapper rc_decs the
 * borrowed args). Leaf/Node carry distinct tags so rc_dec still frees them
 * field-recursively; the TQNil/TQCons results uncons returns are ordinary
 * constructor cells (tags 0/1) the Core `qApply` template pattern-matches. */
#define PRISM_TAQ_LEAF 0x5441514cL /* 'TAQL' */
#define PRISM_TAQ_NODE 0x5441514eL /* 'TAQN' */

static long prism_taq_leaf(long arrow) {
    long *p = prism_alloc(1);
    p[PRISM_TAG_W] = PRISM_TAQ_LEAF;
    prism_rc_inc(arrow);
    p[PRISM_HDR_WORDS] = arrow;
    return (long)p;
}

/* Build a Node taking ownership of l and r (no rc_inc; the caller transfers its
 * references in). */
static long prism_taq_node_own(long l, long r) {
    long *p = prism_alloc(2);
    p[PRISM_TAG_W] = PRISM_TAQ_NODE;
    p[PRISM_HDR_WORDS] = l;
    p[PRISM_HDR_WORDS + 1] = r;
    return (long)p;
}

/* snoc(Q, arrow): append one arrow at the right. Q and arrow are borrowed. */
long prism_taq_snoc(long q, long arrow) {
    long leaf = prism_taq_leaf(arrow);
    if (!q) return leaf;
    prism_rc_inc(q);
    return prism_taq_node_own(q, leaf);
}

/* concat(Q1, Q2): O(1) join. Both borrowed. */
long prism_taq_concat(long q1, long q2) {
    if (!q1) {
        prism_rc_inc(q2);
        return q2;
    }
    if (!q2) {
        prism_rc_inc(q1);
        return q1;
    }
    prism_rc_inc(q1);
    prism_rc_inc(q2);
    return prism_taq_node_own(q1, q2);
}

/* uncons(Q): the leftmost arrow and the remaining queue, as TQCons(head, tail);
 * the empty queue gives TQNil. Q is borrowed and never mutated -- the result
 * shares Q's leaves (rc_inc'd) and rebuilds only the spine -- so unconsing a
 * shared queue leaves the original intact for another resumption. */
long prism_taq_uncons(long q) {
    if (!q) return prism_ctor(0, 0, 0); /* TQNil */
    long cur = q;
    long acc = 0; /* accumulated right tail (owned) */
    while (prism_tag((void *)cur) == PRISM_TAQ_NODE) {
        long l = prism_field((void *)cur, 0);
        long r = prism_field((void *)cur, 1);
        prism_rc_inc(r);
        acc = acc ? prism_taq_node_own(r, acc) : r;
        cur = l;
    }
    /* cur is a Leaf */
    long head = prism_field((void *)cur, 0);
    prism_rc_inc(head);
    long fields[2] = {head, acc};
    return prism_ctor(1, 2, fields); /* TQCons(head, tail) */
}

/* Heap-allocated continuation frames for the native effect machine: the pending
 * work that the interpreter keeps in a `Vec<Frame>` lives here as a chain of
 * counted cells so object-program recursion across an effect boundary never
 * grows the C stack. Field 0 is always `next`, the link to the frame below
 * (toward the handler); a chain whose deepest frame links to 0 is a delimited
 * slice. Because `next` is an ordinary field, `prism_rc_dec` frees a whole
 * abandoned continuation through its existing iterative worklist, in O(1) C
 * stack regardless of depth.
 *
 *   Bind(next, kfn, env)    a sequencing frame: resume the value into `kfn`
 *                           under `env` (the analogue of `Frame::Bind`/`Args`).
 *   Handle(next, table, env) a prompt: `table` carries the handler clauses,
 *                           `env` their closure environment.
 *   Mask(next, ops)         skips `ops` for one capture, so an inner handler
 *                           does not intercept an effect meant for an outer one.
 *
 * Constructors borrow their arguments and retain (rc_inc) what they store, the
 * same convention as the queue cells above, so a codegen call site rc_decs the
 * borrowed operands afterward. Distinct tags keep the cells self-describing when
 * a capture walks the chain. */
#define PRISM_FRAME_BIND 0x46524d42L   /* 'FRMB' */
#define PRISM_FRAME_HANDLE 0x46524d48L /* 'FRMH' */
#define PRISM_FRAME_MASK 0x46524d4dL   /* 'FRMM' */

long prism_frame_bind(long next, long kfn, long env) {
    long *p = prism_alloc(3);
    p[PRISM_TAG_W] = PRISM_FRAME_BIND;
    prism_rc_inc(next);
    prism_rc_inc(kfn);
    prism_rc_inc(env);
    p[PRISM_HDR_WORDS] = next;
    p[PRISM_HDR_WORDS + 1] = kfn;
    p[PRISM_HDR_WORDS + 2] = env;
    return (long)p;
}

long prism_frame_handle(long next, long table, long env) {
    long *p = prism_alloc(3);
    p[PRISM_TAG_W] = PRISM_FRAME_HANDLE;
    prism_rc_inc(next);
    prism_rc_inc(table);
    prism_rc_inc(env);
    p[PRISM_HDR_WORDS] = next;
    p[PRISM_HDR_WORDS + 1] = table;
    p[PRISM_HDR_WORDS + 2] = env;
    return (long)p;
}

long prism_frame_mask(long next, long ops) {
    long *p = prism_alloc(2);
    p[PRISM_TAG_W] = PRISM_FRAME_MASK;
    prism_rc_inc(next);
    prism_rc_inc(ops);
    p[PRISM_HDR_WORDS] = next;
    p[PRISM_HDR_WORDS + 1] = ops;
    return (long)p;
}

/* Splice a copy of the delimited slice `top` (a `next`-chain ending at 0) on top
 * of `base`, returning the new top. Resuming a captured continuation re-pushes a
 * clone so it can be entered again (multishot); a fresh copy also lets `base`
 * differ from the stack the slice was captured on. The slice itself is never
 * mutated, so a still-live capture is unaffected. The copy is built in one
 * forward pass (each new cell links to the previously built one, leaving the
 * clone in reverse order) and then reversed in place; both passes run in O(1) C
 * stack, so a deep continuation splices without recursion. Stored payloads are
 * rc_inc'd into the clone; `base` is retained once, as the deepest frame's
 * `next`. `top` and `base` are borrowed. */
long prism_kont_splice(long top, long base) {
    prism_rc_inc(base);
    if (!top) return base; /* empty slice resumes straight into base */
    long rev = 0;          /* clone, accumulated in reverse (deepest first) */
    long cur = top;
    while (cur) {
        long *src = (long *)cur;
        long n = src[PRISM_ARITY_W];
        long *cp = prism_alloc(n);
        cp[PRISM_TAG_W] = src[PRISM_TAG_W];
        cp[PRISM_HDR_WORDS] = rev; /* link toward the deepest clone so far */
        for (long i = 1; i < n; i++) {
            long f = src[PRISM_HDR_WORDS + i];
            prism_rc_inc(f);
            cp[PRISM_HDR_WORDS + i] = f;
        }
        rev = (long)cp;
        cur = src[PRISM_HDR_WORDS]; /* original next */
    }
    /* `rev` heads the clone in reverse (the slice's deepest frame). Reverse it
     * in place so the original top heads it again, and link the deepest frame's
     * `next` to `base`. */
    long prev = base, node = rev;
    while (node) {
        long *np = (long *)node;
        long nxt = np[PRISM_HDR_WORDS];
        np[PRISM_HDR_WORDS] = prev;
        prev = node;
        node = nxt;
    }
    return prev;
}
