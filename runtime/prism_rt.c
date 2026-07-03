/* Portability: requires GCC >= 5 or Clang >= 3.8.
 * Uses __attribute__((destructor)) for the leak/reuse/effop report hooks and
 * __builtin_add_overflow/sub/mul for checked arithmetic. */

/* getline is POSIX.1-2008; under -std=c11 glibc hides it unless a feature-test
 * macro requests it. macOS exposes it regardless, so this only bites on Linux.
 * Must precede every system header (including mimalloc's <stddef.h> below). */
#ifndef _POSIX_C_SOURCE
// clang-format off: a feature-test macro must be one line, and the NOLINT must
// stay on it to suppress the reserved-identifier lint.
#define _POSIX_C_SOURCE 200809L /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp): the standard feature-test macro */
// clang-format on
#endif

/* Opt-in mimalloc (cargo --features mimalloc): route every libc allocation
 * through mi_* so alloc/free pairing flips together. Must precede any use. The
 * symbols come from the libmimalloc-sys crate; declare them here so no mimalloc
 * header or in-tree source is needed. */
#ifdef PRISM_MIMALLOC
#include <stddef.h>
extern void *mi_malloc(size_t);
extern void mi_free(void *);
extern void *mi_realloc(void *, size_t);
extern void *mi_calloc(size_t, size_t);
#define malloc(n) mi_malloc(n)
#define free(p) mi_free(p)
#define realloc(p, n) mi_realloc(p, n)
#define calloc(a, b) mi_calloc(a, b)
#endif

#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

/* Object layout: { i64 refcount, i64 tag, i64 arity, i64 fields[n] }
 * arity is the field count, letting prism_rc_dec recurse into children.
 * The word indices below are cross-checked against the byte offsets the
 * code generator uses by the `layout_matches_runtime` test in emit.rs. */
#define PRISM_RC_W 0
#define PRISM_TAG_W 1
#define PRISM_ARITY_W 2
#define PRISM_HDR_WORDS 3

/* Live-cell balance, the box-1 acceptance oracle: every prism_alloc bumps it,
 * every freed cell drops it. With PRISM_CHECK_LEAKS set, a destructor prints the
 * final balance to stderr at exit; a clean run reports zero. stderr keeps stdout
 * (the parity-checked channel) untouched, so normal runs are byte-identical. */
static long prism_live_cells = 0;

__attribute__((destructor)) static void prism_leak_report(void) {
    if (getenv("PRISM_CHECK_LEAKS")) {
        fprintf(stderr, "prism: %ld cells leaked\n", prism_live_cells);
    }
}

/* Checked header+payload byte size. A hostile or computed word count must never
 * overflow the size argument to malloc: an overflow would under-allocate and the
 * subsequent field stores would write out of bounds. Reject a negative count (a
 * corrupt length) and any add/mul overflow, aborting rather than handing back an
 * undersized cell. */
static size_t prism_cell_bytes(long n_words) {
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
    return p;
}

/* Build a constructor cell { rc, tag, arity, fields... }, mirroring the inline
 * cells codegen emits (prism_alloc + tag word + field words). Tags follow the
 * ADT's declaration order, so for the prelude's `Option(a) = None | Some(a)`
 * None=0/Some=1 and `Result(a, e) = Ok(a) | Err(e)` Ok=0/Err=1. */
static long prism_ctor(long tag, long n, const long *fields) {
    long *p = prism_alloc(n);
    p[PRISM_TAG_W] = tag;
    for (long i = 0; i < n; i++) p[PRISM_HDR_WORDS + i] = fields[i];
    return (long)p;
}

/* A string is a refcounted cell { rc, tag=PRISM_STR_TAG, byte_len, utf8... }:
 * the bytes live inline after the header and are NUL-terminated for printf
 * interop. The distinct tag tells prism_rc_dec to free the cell without
 * recursing into the bytes (they are not child cells). Every string the program
 * builds, including literals (allocated fresh at each use), is a counted cell
 * that prism_rc_dec frees, so the live-cell balance includes strings. */
#define PRISM_STR_TAG 0x53545200L

/* An Integer is a sign-magnitude bignum cell { rc, tag=PRISM_BIG_TAG, n, limbs... }:
 * n is a signed limb count whose sign is the value's sign, the magnitude is |n|
 * u64 limbs little-endian starting at offset 24 with no leading zero limbs, and
 * zero is n == 0 with no limbs. Like strings, the tag tells prism_rc_dec and
 * prism_reuse_token not to recurse into the payload (limbs are not child cells). */
#define PRISM_BIG_TAG 0x42494700L

/* Unicode scalar-value bounds. The interpreter's show_char is char::from_u32,
 * which admits U+0000..U+D7FF and U+E000..U+10FFFF, rejecting the UTF-16
 * surrogate range and anything past the last code point; a rejected value shows
 * as the empty string. Native must gate on the identical bounds. */
#define PRISM_CP_MAX 0x10FFFFL
#define PRISM_SURROGATE_LO 0xD800L
#define PRISM_SURROGATE_HI 0xDFFFL

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8, "prism runtime assumes LP64");

static long *prism_str_alloc(long byte_len) {
    /* Room for the bytes plus the NUL terminator, rounded up to whole words.
     * `byte_len + 8` is computed in size_t so a near-LONG_MAX length cannot
     * overflow before prism_cell_bytes re-checks the final allocation size. */
    size_t span;
    if (byte_len < 0) abort();
    if (__builtin_add_overflow((size_t)byte_len, (size_t)8, &span)) abort();
    long words = (long)(span / 8);
    long *p = malloc(prism_cell_bytes(words));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = PRISM_STR_TAG;
    p[PRISM_ARITY_W] = byte_len;
    prism_live_cells++;
    return p;
}

static char *prism_str_data(long s) {
    return (char *)((long *)s + PRISM_HDR_WORDS);
}

static long prism_str_len_bytes(long s) {
    return ((long *)s)[PRISM_ARITY_W];
}

long prism_str_lit(const char *src, long byte_len) {
    long *p = prism_str_alloc(byte_len);
    char *d = (char *)(p + PRISM_HDR_WORDS);
    memcpy(d, src, (size_t)byte_len);
    d[byte_len] = 0;
    return (long)p;
}

static long utf8_adv(unsigned char c) {
    if (c < 0x80) return 1;
    if (c < 0xE0) return 2;
    if (c < 0xF0) return 3;
    return 4;
}

/* Advance clamped to the byte length: read_file/getenv can import bytes that
 * are not valid UTF-8, and a lying lead byte must not walk past the buffer. */
static long utf8_step(const char *d, long b, long nb) {
    long a = utf8_adv((unsigned char)d[b]);
    return a > nb - b ? nb - b : a;
}

void prism_div_zero(void) {
    fprintf(stderr, "fatal: division by zero\n");
    exit(1);
}

/* Reached only on an arity bug: a closure dispatched to an apply_n with no
 * matching lambda tag. A diagnostic abort beats raw `unreachable` UB. */
void prism_apply_error(void) {
    fprintf(stderr, "fatal: closure applied at wrong arity\n");
    exit(1);
}

/* Reached only if a `case` scrutinee carries a tag no arm covers: exhaustiveness
 * checking proves this dead for well-typed code, so it fires only on a compiler
 * bug (a coverage hole or a miscompile). A diagnostic abort beats raw
 * `unreachable` UB, and matches the interpreter's clean "no matching pattern"
 * error instead of forking native semantics into undefined behavior. */
void prism_match_error(void) {
    fprintf(stderr, "fatal: no matching pattern in case\n");
    exit(1);
}

void prism_fatal(long s) {
    fprintf(stderr, "fatal: %s\n", prism_str_data(s));
    exit(1);
}

/* `error(n)` raises the Exn fault: the interpreter reports it and terminates
 * with status 1, so native must too, rather than treating the payload as a
 * process exit code (that is `exit`, a separate builtin). exit() flushes stdout,
 * so any output printed before the fault is preserved on both backends. */
void prism_error_int(long n) {
    fprintf(stderr, "error(%ld)\n", n);
    exit(1);
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
        if (p[PRISM_TAG_W] != PRISM_STR_TAG && p[PRISM_TAG_W] != PRISM_BIG_TAG) {
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
    if (p[PRISM_TAG_W] == PRISM_STR_TAG || p[PRISM_TAG_W] == PRISM_BIG_TAG) return 0;
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
        /* String/bignum cells carry an inline byte/limb payload, not child
         * fields, so their arity slot is a length, not a field count: skip the
         * bounds check for them (prism_field is not a valid accessor there). */
        if (tag != PRISM_STR_TAG && tag != PRISM_BIG_TAG && (i < 0 || i >= arity)) {
            fprintf(stderr, "prism_rt: prism_field index %ld out of bounds (arity %ld)\n", i,
                    arity);
            abort();
        }
    }
#endif
    return ((long *)p)[PRISM_HDR_WORDS + i];
}

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

long prism_int_of_long(long v); /* defined with the Int encoding below */

long prism_prim_read_int(void) {
    /* Line-oriented to match the interpreter oracle: consume a whole line and
     * parse its trimmed contents, so a following read_line sees the next line
     * rather than the leftover newline a bare scanf("%ld") would strand. */
    char *buf = 0;
    size_t cap = 0;
    long len = getline(&buf, &cap, stdin);
    if (len < 0) {
        free(buf);
        fprintf(stderr, "fatal: read_int: no integer on stdin\n");
        exit(1);
    }
    errno = 0;
    char *end = 0;
    long n = strtol(buf, &end, 10);
    int ok = errno == 0 && end != buf;
    if (ok) {
        /* The interpreter parses the whole trimmed line (`line.trim().parse`),
         * so trailing content ("123abc") is an error, not a 123-prefix. Only
         * trailing ASCII whitespace, which `str::trim` also drops, may follow
         * the digits; strtol has already skipped the leading whitespace. */
        while (isspace((unsigned char)*end)) end++;
        ok = *end == '\0';
    }
    free(buf);
    if (!ok) {
        fprintf(stderr, "fatal: read_int: no integer on stdin\n");
        exit(1);
    }
    /* Return an encoded Int, not the raw machine word: a value in
     * (2^62, 2^63) fits an i64 but not the 63-bit tagged immediate, so
     * codegen retagging it would silently shift out bit 62 while the
     * interpreter keeps the full value. Encoding here keeps the two in
     * lockstep for the whole i64 range. */
    return prism_int_of_long(n);
}

long prism_prim_read_line(void) {
    char *buf = 0;
    size_t cap = 0;
    long n = getline(&buf, &cap, stdin);
    if (n < 0) {
        free(buf);
        return prism_str_lit("", 0);
    }
    while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) buf[--n] = 0;
    long cell = prism_str_lit(buf, n);
    free(buf);
    return cell;
}

/* Shared with the interpreter's C differential oracle, which links this file and
 * calls print_str to echo shown values. Backends print via the prism_print_*
 * entry points below, not this one. */
void print_str(long s) {
    printf("%s\n", prism_str_data(s));
}

/* String builders operate on string cells and return fresh counted cells, so
 * the live-cell balance stays zero. str_len/char_at/substring index by Unicode
 * codepoint (not byte), so multi-byte UTF-8 text behaves as the source reads. */
long prism_str_concat(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    long *p = prism_str_alloc(la + lb);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    memcpy(o, prism_str_data(a), (size_t)la);
    memcpy(o + la, prism_str_data(b), (size_t)lb);
    o[la + lb] = 0;
    return (long)p;
}

long prism_str_len(long a) {
    const char *d = prism_str_data(a);
    long nb = prism_str_len_bytes(a), n = 0;
    for (long i = 0; i < nb; i++)
        if (((unsigned char)d[i] & 0xC0) != 0x80) n++;
    return n;
}

long prism_byte_len(long s) {
    return prism_str_len_bytes(s); /* raw byte count; the call site retags it */
}

long prism_byte_at(long s, long i) {
    if (i < 0 || i >= prism_str_len_bytes(s)) return -1;
    return (long)(unsigned char)prism_str_data(s)[i];
}

long prism_str_eq(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    if (la != lb) return 0;
    return memcmp(prism_str_data(a), prism_str_data(b), (size_t)la) == 0 ? 1 : 0;
}

long prism_show_bool(long b) {
    return b ? prism_str_lit("true", 4) : prism_str_lit("false", 5);
}

long prism_show_char(long cp) {
    /* Non-scalar code points (surrogates, past U+10FFFF, negative) are not
     * encodable and show as the empty string, matching char::from_u32. */
    if (cp < 0 || cp > PRISM_CP_MAX || (cp >= PRISM_SURROGATE_LO && cp <= PRISM_SURROGATE_HI))
        return prism_str_lit("", 0);
    unsigned long c = (unsigned long)cp;
    char buf[4];
    int k;
    if (c < 0x80) {
        buf[0] = (char)c;
        k = 1;
    } else if (c < 0x800) {
        buf[0] = (char)(0xC0 | (c >> 6));
        buf[1] = (char)(0x80 | (c & 0x3F));
        k = 2;
    } else if (c < 0x10000) {
        buf[0] = (char)(0xE0 | (c >> 12));
        buf[1] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[2] = (char)(0x80 | (c & 0x3F));
        k = 3;
    } else {
        buf[0] = (char)(0xF0 | (c >> 18));
        buf[1] = (char)(0x80 | ((c >> 12) & 0x3F));
        buf[2] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[3] = (char)(0x80 | (c & 0x3F));
        k = 4;
    }
    return prism_str_lit(buf, k);
}

/* --- blake3, one-shot ------------------------------------------------------
 *
 * A portable, single-threaded blake3 over a byte buffer, returned as lowercase
 * hex. This is the native half of the `blake3` builtin every derived `Hash`
 * instance folds through; it must produce output byte-identical to the Rust
 * `blake3` crate the interpreter uses (gated by tests/hash_value_parity.rs), so
 * it follows the reference spec exactly: 1024-byte chunks, a binary tree of
 * parent nodes, the seven-round G-permutation, and the CHUNK/PARENT/ROOT flags. */

#define B3_BLOCK_LEN 64
#define B3_CHUNK_LEN 1024
#define B3_CHUNK_START 1u
#define B3_CHUNK_END 2u
#define B3_PARENT 4u
#define B3_ROOT 8u

static const uint32_t B3_IV[8] = {0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
                                  0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u};

static const uint8_t B3_MSG_PERM[16] = {2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8};

static inline uint32_t b3_rotr(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));
}

static inline uint32_t b3_le32(const uint8_t *b) {
    return (uint32_t)b[0] | ((uint32_t)b[1] << 8) | ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24);
}

static inline void b3_g(uint32_t s[16], int a, int b, int c, int d, uint32_t x, uint32_t y) {
    s[a] = s[a] + s[b] + x;
    s[d] = b3_rotr(s[d] ^ s[a], 16);
    s[c] = s[c] + s[d];
    s[b] = b3_rotr(s[b] ^ s[c], 12);
    s[a] = s[a] + s[b] + y;
    s[d] = b3_rotr(s[d] ^ s[a], 8);
    s[c] = s[c] + s[d];
    s[b] = b3_rotr(s[b] ^ s[c], 7);
}

static void b3_round(uint32_t s[16], const uint32_t m[16]) {
    b3_g(s, 0, 4, 8, 12, m[0], m[1]);
    b3_g(s, 1, 5, 9, 13, m[2], m[3]);
    b3_g(s, 2, 6, 10, 14, m[4], m[5]);
    b3_g(s, 3, 7, 11, 15, m[6], m[7]);
    b3_g(s, 0, 5, 10, 15, m[8], m[9]);
    b3_g(s, 1, 6, 11, 12, m[10], m[11]);
    b3_g(s, 2, 7, 8, 13, m[12], m[13]);
    b3_g(s, 3, 4, 9, 14, m[14], m[15]);
}

/* Compress one 64-byte block, writing the 16 output words (the first 8 are the
 * chaining value; the full 16 are the extendable output for a root node). */
static void b3_compress(const uint32_t cv[8], const uint8_t block[64], uint64_t counter,
                        uint32_t block_len, uint32_t flags, uint32_t out[16]) {
    uint32_t m[16];
    for (size_t i = 0; i < 16; i++) m[i] = b3_le32(block + 4 * i);
    uint32_t s[16] = {cv[0],
                      cv[1],
                      cv[2],
                      cv[3],
                      cv[4],
                      cv[5],
                      cv[6],
                      cv[7],
                      B3_IV[0],
                      B3_IV[1],
                      B3_IV[2],
                      B3_IV[3],
                      (uint32_t)counter,
                      (uint32_t)(counter >> 32),
                      block_len,
                      flags};
    for (int r = 0; r < 7; r++) {
        b3_round(s, m);
        if (r < 6) {
            uint32_t t[16];
            for (int i = 0; i < 16; i++) t[i] = m[B3_MSG_PERM[i]];
            memcpy(m, t, sizeof t);
        }
    }
    for (int i = 0; i < 8; i++) {
        out[i] = s[i] ^ s[i + 8];
        out[i + 8] = s[i + 8] ^ cv[i];
    }
}

/* Chain the blocks of one chunk into its 8-word chaining value. `root` sets the
 * ROOT flag on the final block (the whole input is a single chunk). */
static void b3_chunk_cv(const uint8_t *in, size_t len, uint64_t counter, int root,
                        uint32_t out_cv[8]) {
    uint32_t cv[8];
    memcpy(cv, B3_IV, sizeof cv);
    size_t nblocks = len == 0 ? 1 : (len + B3_BLOCK_LEN - 1) / B3_BLOCK_LEN;
    for (size_t b = 0; b < nblocks; b++) {
        size_t off = b * B3_BLOCK_LEN;
        size_t blen = len - off < B3_BLOCK_LEN ? len - off : B3_BLOCK_LEN;
        uint8_t block[64];
        memset(block, 0, sizeof block);
        memcpy(block, in + off, blen);
        uint32_t flags = 0;
        if (b == 0) flags |= B3_CHUNK_START;
        if (b == nblocks - 1) {
            flags |= B3_CHUNK_END;
            if (root) flags |= B3_ROOT;
        }
        uint32_t words[16];
        b3_compress(cv, block, counter, (uint32_t)blen, flags, words);
        memcpy(cv, words, sizeof cv);
    }
    memcpy(out_cv, cv, sizeof(uint32_t) * 8);
}

/* Bytes on the left of a subtree split: the largest power-of-two chunk count
 * strictly less than the total, times the chunk length. */
static size_t b3_left_len(size_t len) {
    size_t full = (len - 1) / B3_CHUNK_LEN;
    size_t p = 1;
    while (p * 2 <= full) p *= 2;
    return p * B3_CHUNK_LEN;
}

/* Chaining value of a non-root subtree covering `in[0..len]`. Recurses on the
 * binary tree split; depth is bounded by log2(len / B3_CHUNK_LEN) <= 54 for any
 * size_t len, so the call chain cannot exhaust the stack. */
/* NOLINTNEXTLINE(misc-no-recursion) */
static void b3_subtree_cv(const uint8_t *in, size_t len, uint64_t counter, uint32_t out[8]) {
    if (len <= B3_CHUNK_LEN) {
        b3_chunk_cv(in, len, counter, 0, out);
        return;
    }
    size_t left = b3_left_len(len);
    uint32_t l[8], r[8];
    b3_subtree_cv(in, left, counter, l);
    b3_subtree_cv(in + left, len - left, counter + left / B3_CHUNK_LEN, r);
    uint8_t block[64];
    memcpy(block, l, 32);
    memcpy(block + 32, r, 32);
    uint32_t words[16];
    b3_compress(B3_IV, block, 0, B3_BLOCK_LEN, B3_PARENT, words);
    memcpy(out, words, sizeof(uint32_t) * 8);
}

static void b3_hash(const uint8_t *in, size_t len, uint8_t out[32]) {
    uint32_t words[8];
    if (len <= B3_CHUNK_LEN) {
        b3_chunk_cv(in, len, 0, 1, words);
    } else {
        size_t left = b3_left_len(len);
        uint32_t l[8], r[8];
        b3_subtree_cv(in, left, 0, l);
        b3_subtree_cv(in + left, len - left, left / B3_CHUNK_LEN, r);
        uint8_t block[64];
        memcpy(block, l, 32);
        memcpy(block + 32, r, 32);
        uint32_t full[16];
        b3_compress(B3_IV, block, 0, B3_BLOCK_LEN, B3_PARENT | B3_ROOT, full);
        memcpy(words, full, sizeof words);
    }
    for (size_t i = 0; i < 8; i++)
        for (size_t j = 0; j < 4; j++) out[i * 4 + j] = (uint8_t)(words[i] >> (8 * j));
}

long prism_blake3(long s) {
    const uint8_t *data = (const uint8_t *)prism_str_data(s);
    size_t len = (size_t)prism_str_len_bytes(s);
    uint8_t dig[32];
    b3_hash(data, len, dig);
    static const char hexd[] = "0123456789abcdef";
    char hex[64];
    for (size_t i = 0; i < 32; i++) {
        hex[2 * i] = hexd[dig[i] >> 4];
        hex[2 * i + 1] = hexd[dig[i] & 15];
    }
    return prism_str_lit(hex, 64);
}

/* --- Shortest-round-trip decimal digit generation (Dragon4) ---------------
 *
 * The significant digits of a shortest-round-trip float print are produced here
 * with exact integer arithmetic, owning the digit selection in-repo rather than
 * deferring to libc's snprintf/strtod round-trip. The output is byte-identical
 * to the interpreter's shortest form by construction: same algorithm class
 * (correctly-rounded shortest decimal, round-half-to-even at boundaries), so the
 * digit string and exponent match Rust's float Display digit for digit.
 *
 * A fixed-capacity base-2^32 bignum backs the exact scaling. The widest
 * intermediate is a subnormal scaled toward its leading digit (~2^1130) or
 * DBL_MAX's denominator (~2^1027), both well under the capacity; every mutator
 * aborts rather than silently truncate if that bound is ever exceeded. */
#define PRISM_DTOA_LIMBS 48 /* 1536 bits; margin over the ~2^1130 worst case */

typedef struct {
    uint32_t w[PRISM_DTOA_LIMBS]; /* little-endian base-2^32 limbs */
    int n;                        /* used limbs; n == 0 is the value zero */
} DtoaBig;

static void dtoa_big_norm(DtoaBig *b) {
    while (b->n > 0 && b->w[b->n - 1] == 0) b->n--;
}

static void dtoa_big_set_u64(DtoaBig *b, uint64_t x) {
    b->n = 0;
    while (x) {
        b->w[b->n++] = (uint32_t)x;
        x >>= 32;
    }
}

static int dtoa_big_cmp(const DtoaBig *a, const DtoaBig *b) {
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (int i = a->n - 1; i >= 0; i--)
        if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    return 0;
}

/* a += b */
static void dtoa_big_add(DtoaBig *a, const DtoaBig *b) {
    int n = a->n > b->n ? a->n : b->n;
    uint64_t carry = 0;
    for (int i = 0; i < n; i++) {
        uint64_t s = carry + (i < a->n ? a->w[i] : 0) + (i < b->n ? b->w[i] : 0);
        a->w[i] = (uint32_t)s;
        carry = s >> 32;
    }
    if (carry) {
        if (n >= PRISM_DTOA_LIMBS) abort();
        a->w[n++] = (uint32_t)carry;
    }
    a->n = n;
    dtoa_big_norm(a);
}

/* a -= b, requires a >= b */
static void dtoa_big_sub(DtoaBig *a, const DtoaBig *b) {
    int64_t borrow = 0;
    for (int i = 0; i < a->n; i++) {
        int64_t s = (int64_t)a->w[i] - (int64_t)(i < b->n ? b->w[i] : 0) - borrow;
        if (s < 0) {
            s += (int64_t)1 << 32;
            borrow = 1;
        } else {
            borrow = 0;
        }
        a->w[i] = (uint32_t)s;
    }
    dtoa_big_norm(a);
}

/* a *= m */
static void dtoa_big_mul_small(DtoaBig *a, uint32_t m) {
    uint64_t carry = 0;
    for (int i = 0; i < a->n; i++) {
        uint64_t p = (uint64_t)a->w[i] * m + carry;
        a->w[i] = (uint32_t)p;
        carry = p >> 32;
    }
    while (carry) {
        if (a->n >= PRISM_DTOA_LIMBS) abort();
        a->w[a->n++] = (uint32_t)carry;
        carry >>= 32;
    }
    dtoa_big_norm(a);
}

/* a *= b (schoolbook) */
static void dtoa_big_mul(DtoaBig *a, const DtoaBig *b) {
    uint32_t out[PRISM_DTOA_LIMBS] = {0};
    for (int i = 0; i < a->n; i++) {
        uint64_t carry = 0;
        for (int j = 0; j < b->n; j++) {
            if (i + j >= PRISM_DTOA_LIMBS) abort();
            uint64_t cur = (uint64_t)out[i + j] + (uint64_t)a->w[i] * b->w[j] + carry;
            out[i + j] = (uint32_t)cur;
            carry = cur >> 32;
        }
        for (int k = i + b->n; carry; k++) {
            if (k >= PRISM_DTOA_LIMBS) abort();
            uint64_t cur = (uint64_t)out[k] + carry;
            out[k] = (uint32_t)cur;
            carry = cur >> 32;
        }
    }
    int outn = a->n + b->n;
    if (outn > PRISM_DTOA_LIMBS) outn = PRISM_DTOA_LIMBS;
    for (int i = 0; i < outn; i++) a->w[i] = out[i];
    a->n = outn;
    dtoa_big_norm(a);
}

/* a *= 2^bits */
static void dtoa_big_shl(DtoaBig *a, int bits) {
    if (a->n == 0 || bits == 0) return;
    int words = bits / 32, rem = bits % 32;
    if (words) {
        if (a->n + words > PRISM_DTOA_LIMBS) abort();
        for (int i = a->n - 1; i >= 0; i--) a->w[i + words] = a->w[i];
        for (int i = 0; i < words; i++) a->w[i] = 0;
        a->n += words;
    }
    if (rem) {
        uint32_t carry = 0;
        for (int i = 0; i < a->n; i++) {
            uint64_t s = ((uint64_t)a->w[i] << rem) | carry;
            a->w[i] = (uint32_t)s;
            carry = (uint32_t)(s >> 32);
        }
        if (carry) {
            if (a->n >= PRISM_DTOA_LIMBS) abort();
            a->w[a->n++] = carry;
        }
    }
    dtoa_big_norm(a);
}

/* Powers of ten that fit a single limb; PRISM_POW10_CHUNK is the largest, used
 * to multiply by 10^k in one-limb strides. */
static const uint32_t PRISM_POW10_SMALL[10] = {1,      10,      100,      1000,      10000,
                                               100000, 1000000, 10000000, 100000000, 1000000000};
#define PRISM_POW10_CHUNK_EXP 9
#define PRISM_POW10_CHUNK 1000000000u

/* a *= 10^k */
static void dtoa_big_mul_pow10(DtoaBig *a, int k) {
    while (k >= PRISM_POW10_CHUNK_EXP) {
        dtoa_big_mul_small(a, PRISM_POW10_CHUNK);
        k -= PRISM_POW10_CHUNK_EXP;
    }
    if (k > 0) dtoa_big_mul_small(a, PRISM_POW10_SMALL[k]);
}

/* Bit layout of an IEEE-754 double. */
#define PRISM_F64_MANT_BITS 52
#define PRISM_F64_EXP_BIAS 1075 /* 1023 + 52: unbiased exponent of the integer significand */
#define PRISM_F64_MIN_EXP (-1074)
#define PRISM_F64_HIDDEN (1ULL << PRISM_F64_MANT_BITS)
/* log10(2), for the initial decimal-exponent estimate (corrected exactly below). */
#define PRISM_LOG10_2 0.30102999566398119521

/* Largest significand a shortest-round-trip double print ever needs; 17 decimal
 * digits fit a u64, so the p-digit integer is exact in a machine word. */
#define PRISM_FLOAT_MAX_DIGITS 17

/* Sign of the decimal `F * 10^g` minus the rational `X / S` (S > 0). Both sides
 * are scaled to integers before comparing: multiply through by S, and by
 * 10^(-g) when g is negative, so the comparison is exact. */
static int dtoa_cmp_decimal(uint64_t F, int g, const DtoaBig *X, const DtoaBig *S) {
    DtoaBig lhs, rhs = *X;
    dtoa_big_set_u64(&lhs, F);
    if (g >= 0) {
        dtoa_big_mul_pow10(&lhs, g);
        dtoa_big_mul(&lhs, S); /* (F * 10^g) * S  vs  X */
    } else {
        dtoa_big_mul(&lhs, S); /* F * S           vs  X * 10^(-g) */
        dtoa_big_mul_pow10(&rhs, -g);
    }
    return dtoa_big_cmp(&lhs, &rhs);
}

/* Decimal significand of `d` (finite, > 0) matching the interpreter's `fmt_g`:
 * the FEWEST significant digits p in 1..17 whose correctly-rounded (round half
 * to even) p-digit decimal rounds back to exactly `d`. This is the trial loop
 * `fmt_g` runs over Rust's `{:.*e}` and `parse::<f64>()`, reproduced with exact
 * integer arithmetic so the digit string is owned in-repo rather than resting on
 * libc agreeing with Rust. The correctly-rounded p-digit value is not always the
 * shortest that round-trips (a power of two is the classic case), so this must
 * be the trial loop, not a one-pass shortest formatter, to stay byte-identical.
 *
 * Writes the digit chars into `digits` (no sign, no point), the count into `*nd`
 * (1..17), and the base-10 exponent of the leading digit into `*e10` (value ==
 * 0.d1..dn * 10^(*e10 + 1)). `digits` must hold at least 18 bytes. */
static void prism_shortest_digits(double d, char *digits, int *nd, int *e10) {
    uint64_t bits;
    memcpy(&bits, &d, sizeof bits);
    int be = (int)((bits >> PRISM_F64_MANT_BITS) & 0x7ff);
    uint64_t frac = bits & (PRISM_F64_HIDDEN - 1);
    uint64_t f;
    int e;
    if (be == 0) {
        f = frac; /* subnormal; d > 0 so frac != 0 */
        e = PRISM_F64_MIN_EXP;
    } else {
        f = frac | PRISM_F64_HIDDEN; /* normal: restore the hidden leading bit */
        e = be - PRISM_F64_EXP_BIAS;
    }
    /* Round-to-nearest-EVEN makes the rounding boundaries inclusive exactly when
     * the significand is even, so a decimal landing on a boundary round-trips. */
    int even = (f & 1) == 0;

    /* Scaled exact rationals: value == R/S, and the half-gaps to the neighboring
     * doubles are Mp/S (upper) and Mm/S (lower). Everything is scaled by 2 so a
     * half-ulp is an integer; a decimal round-trips to `d` iff it lies in
     * (value - Mm/S, value + Mp/S), boundaries included when `even`. */
    DtoaBig R, S, Mp, Mm;
    if (e >= 0) {
        dtoa_big_set_u64(&R, f);
        dtoa_big_shl(&R, e + 1); /* R = f * 2^(e+1) */
        dtoa_big_set_u64(&S, 2);
        dtoa_big_set_u64(&Mp, 1);
        dtoa_big_shl(&Mp, e); /* Mp = 2^e */
        Mm = Mp;
    } else {
        dtoa_big_set_u64(&R, f);
        dtoa_big_shl(&R, 1); /* R = f * 2 */
        dtoa_big_set_u64(&S, 1);
        dtoa_big_shl(&S, 1 - e); /* S = 2^(1-e) */
        dtoa_big_set_u64(&Mp, 1);
        dtoa_big_set_u64(&Mm, 1);
    }
    /* A power-of-two significand (and not the smallest normal, whose predecessor
     * shares its exponent) sits at a binary-exponent boundary: the gap below is
     * half the gap above. Scale R, S, Mp by 2 and leave Mm, so Mm == Mp/2. */
    if (f == PRISM_F64_HIDDEN && be > 1) {
        dtoa_big_mul_small(&R, 2);
        dtoa_big_mul_small(&S, 2);
        dtoa_big_mul_small(&Mp, 2);
    }
    /* The round-trip boundaries as integer numerators over S. */
    DtoaBig hi_num = R, lo_num = R;
    dtoa_big_add(&hi_num, &Mp);
    dtoa_big_sub(&lo_num, &Mm);

    /* Position the leading digit: A/B == value, scaled into [1/10, 1). The
     * estimate is corrected off-by-one exactly against the bignums. Positioning
     * depends only on the value, so it is done once for every precision. */
    DtoaBig A = R, B = S;
    double lv = log10((double)f) + (double)e * PRISM_LOG10_2;
    int k = (int)ceil(lv - 1e-10);
    if (k >= 0) {
        dtoa_big_mul_pow10(&B, k);
    } else {
        dtoa_big_mul_pow10(&A, -k);
    }
    for (;;) { /* pull below 1 */
        if (dtoa_big_cmp(&A, &B) >= 0) {
            dtoa_big_mul_small(&B, 10);
            k++;
        } else {
            break;
        }
    }
    for (;;) { /* push to at least 1/10 so the leading digit is nonzero */
        DtoaBig a10 = A;
        dtoa_big_mul_small(&a10, 10);
        if (dtoa_big_cmp(&a10, &B) < 0) {
            dtoa_big_mul_small(&A, 10);
            k--;
        } else {
            break;
        }
    }
    int base_e10 = k - 1;

    for (int p = 1; p <= PRISM_FLOAT_MAX_DIGITS; p++) {
        /* Emit p digits of A/B, correctly rounded half-to-even, into `digits`. */
        DtoaBig cur = A, den = B;
        for (int i = 0; i < p; i++) {
            dtoa_big_mul_small(&cur, 10);
            int dig = 0;
            while (dtoa_big_cmp(&cur, &den) >= 0) {
                dtoa_big_sub(&cur, &den);
                dig++;
            }
            digits[i] = (char)('0' + dig);
        }
        /* Round the p-th digit on the remainder `cur`: 2*cur vs den, ties even. */
        DtoaBig twice = cur;
        dtoa_big_mul_small(&twice, 2);
        int c = dtoa_big_cmp(&twice, &den);
        int e10_p = base_e10;
        if (c > 0 || (c == 0 && ((digits[p - 1] - '0') & 1))) {
            int i = p - 1;
            while (i >= 0 && digits[i] == '9') {
                digits[i] = '0';
                i--;
            }
            if (i < 0) {
                /* 999..9 carried to 1000..0: the p-digit significand is "1"
                 * followed by p-1 zeros, one decimal place higher. */
                digits[0] = '1';
                for (int j = 1; j < p; j++) digits[j] = '0';
                e10_p++;
            } else {
                digits[i]++;
            }
        }
        /* Reconstruct the exact p-digit integer (17 digits fit a u64). */
        uint64_t F = 0;
        for (int i = 0; i < p; i++) F = F * 10 + (uint64_t)(digits[i] - '0');

        /* Round-trip: does F * 10^(e10_p - (p-1)) round back to exactly d? It does
         * iff it lands strictly inside the rounding interval, or on a boundary
         * that ties to the even significand. p == 17 always round-trips. */
        int g = e10_p - (p - 1);
        int ch = dtoa_cmp_decimal(F, g, &hi_num, &S);
        int cl = dtoa_cmp_decimal(F, g, &lo_num, &S);
        int round_trips =
            (cl > 0 && ch < 0) || (even && (ch == 0 || cl == 0)) || p == PRISM_FLOAT_MAX_DIGITS;
        if (round_trips) {
            /* At the minimal p a trailing zero cannot occur (it would mean p-1
             * already round-tripped); drop one defensively to match `fmt_g`. */
            int cnt = p;
            while (cnt > 1 && digits[cnt - 1] == '0') cnt--;
            *nd = cnt;
            *e10 = e10_p;
            return;
        }
    }
}

/* Shortest decimal that round-trips back to `d`, laid out like a Python `repr`:
 * full precision with no truncation, scientific notation only when the decimal
 * exponent falls outside [-4, 16). This must stay byte-identical to the
 * interpreter's `fmt_g` (src/eval) and the Lean oracle's `fmtG` (models), which
 * are differentially tested against this runtime. Because the digits are the
 * FEWEST that round-trip, the last digit is never 0, so no trailing zeros ever
 * need stripping. */
/* Buffer size every caller of prism_fmt_float must provide; 17 significant
 * digits plus sign, point, and `e+XXX` never exceed this. */
#define PRISM_FLOAT_BUF 64

static int prism_fmt_float(double d, char *out) {
    int o = 0;
    if (isnan(d)) {
        memcpy(out, "nan", sizeof "nan");
        return 3;
    }
    if (isinf(d)) {
        if (d < 0) {
            memcpy(out, "-inf", sizeof "-inf");
            return 4;
        }
        memcpy(out, "inf", sizeof "inf");
        return 3;
    }
    if (d == 0.0) {
        if (signbit(d)) {
            memcpy(out, "-0", sizeof "-0");
            return 2;
        }
        out[0] = '0';
        return 1;
    }

    int neg = signbit(d);
    char digits[20] = {0};
    int nd = 0, e10 = 0;
    prism_shortest_digits(neg ? -d : d, digits, &nd, &e10);

    if (neg) out[o++] = '-';
    if (e10 >= -4 && e10 < 16) {
        if (e10 >= 0) {
            int k = e10 + 1;
            for (int i = 0; i < k; i++) out[o++] = i < nd ? digits[i] : '0';
            if (nd > k) {
                out[o++] = '.';
                for (int i = k; i < nd; i++) out[o++] = digits[i];
            }
        } else {
            out[o++] = '0';
            out[o++] = '.';
            for (int i = 0; i < -e10 - 1; i++) out[o++] = '0';
            for (int i = 0; i < nd; i++) out[o++] = digits[i];
        }
    } else {
        out[o++] = digits[0];
        if (nd > 1) {
            out[o++] = '.';
            for (int i = 1; i < nd; i++) out[o++] = digits[i];
        }
        o += snprintf(out + o, PRISM_FLOAT_BUF - (size_t)o, "e%c%02d", e10 < 0 ? '-' : '+',
                      e10 < 0 ? -e10 : e10);
    }
    return o;
}

long prism_show_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    char out[PRISM_FLOAT_BUF];
    int o = prism_fmt_float(d, out);
    return prism_str_lit(out, o);
}

/* `print` of a float goes through the same shortest-round-trip formatter as
 * `show_float`, so native `print(x)` agrees with the interpreter and with
 * native `print(show_float(x))` instead of C `printf("%g")`'s 6-digit form. */
void prism_print_float(long f) {
    double d;
    memcpy(&d, &f, 8);
    char out[PRISM_FLOAT_BUF];
    int o = prism_fmt_float(d, out);
    fwrite(out, 1, (size_t)o, stdout);
}

long prism_substring(long s, long start, long len) {
    const char *d = prism_str_data(s);
    long nb = prism_str_len_bytes(s);
    if (start < 0) start = 0;
    if (len < 0) len = 0;
    long b = 0, skipped = 0;
    while (b < nb && skipped < start) {
        b += utf8_step(d, b, nb);
        skipped++;
    }
    long bstart = b, taken = 0;
    while (b < nb && taken < len) {
        b += utf8_step(d, b, nb);
        taken++;
    }
    long out_len = b - bstart;
    long *p = prism_str_alloc(out_len);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    memcpy(o, d + bstart, (size_t)out_len);
    o[out_len] = 0;
    return (long)p;
}

long prism_char_at(long s, long i) {
    if (i < 0) return -1;
    const char *d = prism_str_data(s);
    long nb = prism_str_len_bytes(s);
    long cp = 0;
    for (long b = 0; b < nb;) {
        unsigned char c = (unsigned char)d[b];
        long adv = utf8_step(d, b, nb);
        long val = c < 0x80 ? c : c < 0xE0 ? c & 0x1F : c < 0xF0 ? c & 0x0F : c & 0x07;
        for (long k = 1; k < adv; k++) val = (val << 6) | ((unsigned char)d[b + k] & 0x3F);
        if (cp == i) return val;
        cp++;
        b += adv;
    }
    return -1;
}

static int prism_ws(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\f' || c == '\r';
}

long prism_str_cmp(long a, long b) {
    long la = prism_str_len_bytes(a), lb = prism_str_len_bytes(b);
    long n = la < lb ? la : lb;
    int c = memcmp(prism_str_data(a), prism_str_data(b), (size_t)n);
    if (c < 0) return -1;
    if (c > 0) return 1;
    return la < lb ? -1 : la > lb ? 1 : 0;
}

static long *prism_big_alloc(long nlimbs) {
    /* Same overflow-checked sizing as ordinary cells: a hostile or computed
     * limb count must never under-allocate and let the limb stores below write
     * out of bounds. */
    long *p = malloc(prism_cell_bytes(nlimbs));
    if (!p) abort();
    p[PRISM_RC_W] = 1;
    p[PRISM_TAG_W] = PRISM_BIG_TAG;
    p[PRISM_ARITY_W] = 0;
    prism_live_cells++;
    return p;
}

static unsigned long *big_limbs(long v) {
    return (unsigned long *)((long *)v + PRISM_HDR_WORDS);
}

static long big_count(long v) {
    return ((long *)v)[PRISM_ARITY_W];
}

static long big_mag(long v) {
    long n = big_count(v);
    return n < 0 ? -n : n;
}

static long mag_trim(const unsigned long *m, long n) {
    while (n > 0 && m[n - 1] == 0) n--;
    return n;
}

static long big_make(const unsigned long *m, long n, int neg) {
    n = mag_trim(m, n);
    long *p = prism_big_alloc(n);
    // n > 0 implies m is non-null (mag_trim already read it); the explicit `&& m`
    // says so to the analyzer, which otherwise loses the constraint through the
    // zero-bignum call big_make(0, 0, 0) and flags memcpy's nonnull `src`.
    if (n && m) memcpy(p + PRISM_HDR_WORDS, m, (size_t)n * 8);
    p[PRISM_ARITY_W] = neg ? -n : n;
    return (long)p;
}

static int mag_cmp(const unsigned long *a, long na, const unsigned long *b, long nb) {
    if (na != nb) return na < nb ? -1 : 1;
    for (long i = na - 1; i >= 0; i--)
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}

static long mag_add(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    __uint128_t c = 0;
    long n = na > nb ? na : nb;
    for (long i = 0; i < n; i++) {
        c += (__uint128_t)(i < na ? a[i] : 0) + (i < nb ? b[i] : 0);
        o[i] = (unsigned long)c;
        c >>= 64;
    }
    o[n] = (unsigned long)c;
    return n + 1;
}

/* Requires a >= b; in place (o == a) is safe. */
static long mag_sub(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    long borrow = 0;
    for (long i = 0; i < na; i++) {
        __int128 t = (__int128)a[i] - (i < nb ? b[i] : 0) - borrow;
        o[i] = (unsigned long)t;
        borrow = t < 0;
    }
    return na;
}

static void mag_mul(const unsigned long *a, long na, const unsigned long *b, long nb,
                    unsigned long *o) {
    memset(o, 0, (size_t)(na + nb) * 8);
    for (long i = 0; i < na; i++) {
        unsigned long carry = 0;
        for (long j = 0; j < nb; j++) {
            __uint128_t t = (__uint128_t)a[i] * b[j] + o[i + j] + carry;
            o[i + j] = (unsigned long)t;
            carry = (unsigned long)(t >> 64);
        }
        o[i + nb] += carry;
    }
}

/* Shift-subtract long division: q gets na limbs, r gets nb + 1. */
static void mag_divrem(const unsigned long *a, long na, const unsigned long *b, long nb,
                       unsigned long *q, unsigned long *r) {
    memset(q, 0, (size_t)na * 8);
    memset(r, 0, (size_t)(nb + 1) * 8);
    for (long i = na * 64 - 1; i >= 0; i--) {
        unsigned long bit = (a[i / 64] >> (i % 64)) & 1;
        for (long k = 0; k <= nb; k++) {
            unsigned long top = r[k] >> 63;
            r[k] = (r[k] << 1) | bit;
            bit = top;
        }
        if (mag_cmp(r, mag_trim(r, nb + 1), b, nb) >= 0) {
            mag_sub(r, nb + 1, b, nb, r);
            q[i / 64] |= 1UL << (i % 64);
        }
    }
}

static long mag_muladd_small(unsigned long *m, long n, unsigned long mul, unsigned long add) {
    __uint128_t c = add;
    for (long i = 0; i < n; i++) {
        c += (__uint128_t)m[i] * mul;
        m[i] = (unsigned long)c;
        c >>= 64;
    }
    if (c) m[n++] = (unsigned long)c;
    return n;
}

static unsigned long mag_divmod_small(unsigned long *m, long n, unsigned long d) {
    __uint128_t rem = 0;
    for (long i = n - 1; i >= 0; i--) {
        __uint128_t t = (rem << 64) | m[i];
        m[i] = (unsigned long)(t / d);
        rem = t % d;
    }
    return (unsigned long)rem;
}

long prism_big_from_int(long v) {
    unsigned long m = v < 0 ? 0UL - (unsigned long)v : (unsigned long)v;
    return big_make(&m, 1, v < 0);
}

long prism_big_of_str(long s, int *ok) {
    const char *p = prism_str_data(s);
    const char *q = p + prism_str_len_bytes(s);
    while (p < q && prism_ws(*p)) p++;
    while (q > p && prism_ws(q[-1])) q--;
    int neg = 0;
    if (p < q && (*p == '-' || *p == '+')) neg = *p++ == '-';
    if (p == q) {
        *ok = 0;
        return 0;
    }
    for (const char *t = p; t < q; t++)
        if (*t < '0' || *t > '9') {
            *ok = 0;
            return 0;
        }
    unsigned long *m = malloc((size_t)((q - p) / 19 + 2) * 8);
    if (!m) abort();
    long n = 0;
    for (; p < q; p++) n = mag_muladd_small(m, n, 10, (unsigned long)(*p - '0'));
    long r = big_make(m, n, neg);
    free(m);
    *ok = 1;
    return r;
}

static long big_addsub(long a, long b, int flip) {
    long ma = big_mag(a), mb = big_mag(b);
    int sa = big_count(a) < 0, sb = (big_count(b) < 0) ^ flip;
    const unsigned long *la = big_limbs(a), *lb = big_limbs(b);
    unsigned long *o = malloc((size_t)((ma > mb ? ma : mb) + 1) * 8);
    if (!o) abort();
    long n;
    int neg;
    if (sa == sb) {
        n = mag_add(la, ma, lb, mb, o);
        neg = sa;
    } else if (mag_cmp(la, ma, lb, mb) >= 0) {
        n = mag_sub(la, ma, lb, mb, o);
        neg = sa;
    } else {
        n = mag_sub(lb, mb, la, ma, o);
        neg = sb;
    }
    long r = big_make(o, n, neg);
    free(o);
    return r;
}

long prism_big_add(long a, long b) {
    return big_addsub(a, b, 0);
}

long prism_big_sub(long a, long b) {
    return big_addsub(a, b, 1);
}

long prism_big_mul(long a, long b) {
    long ma = big_mag(a), mb = big_mag(b);
    if (ma == 0 || mb == 0) return big_make(0, 0, 0);
    unsigned long *o = malloc((size_t)(ma + mb) * 8);
    if (!o) abort();
    mag_mul(big_limbs(a), ma, big_limbs(b), mb, o);
    long r = big_make(o, ma + mb, (big_count(a) < 0) != (big_count(b) < 0));
    free(o);
    return r;
}

/* Truncated division: quotient rounds toward zero, remainder keeps the
 * dividend's sign, matching C, Rust, and num-bigint. */
static long big_divrem(long a, long b, int want_rem) {
    long ma = big_mag(a), mb = big_mag(b);
    if (mb == 0) prism_div_zero();
    if (ma == 0) return big_make(0, 0, 0);
    unsigned long *q = malloc((size_t)ma * 8);
    unsigned long *r = malloc((size_t)(mb + 1) * 8);
    if (!q || !r) abort();
    mag_divrem(big_limbs(a), ma, big_limbs(b), mb, q, r);
    long res = want_rem ? big_make(r, mb + 1, big_count(a) < 0)
                        : big_make(q, ma, (big_count(a) < 0) != (big_count(b) < 0));
    free(q);
    free(r);
    return res;
}

long prism_big_div(long a, long b) {
    return big_divrem(a, b, 0);
}

long prism_big_rem(long a, long b) {
    return big_divrem(a, b, 1);
}

long prism_big_cmp(long a, long b) {
    long na = big_count(a), nb = big_count(b);
    if (na != nb) return na < nb ? -1 : 1;
    int c = mag_cmp(big_limbs(a), big_mag(a), big_limbs(b), big_mag(b));
    return na < 0 ? -c : c;
}

long prism_big_show(long a) {
    long n = big_mag(a);
    if (n == 0) return prism_str_lit("0", 1);
    unsigned long *t = malloc((size_t)n * 8);
    unsigned long *chunk = malloc((size_t)(n + 2) * 8);
    if (!t || !chunk) abort();
    memcpy(t, big_limbs(a), (size_t)n * 8);
    long k = 0;
    while (n > 0) {
        chunk[k++] = mag_divmod_small(t, n, 10000000000000000000UL);
        n = mag_trim(t, n);
    }
    long cap = k * 19 + 2;
    char *buf = malloc((size_t)cap);
    if (!buf) abort();
    char *o = buf;
    if (big_count(a) < 0) *o++ = '-';
    o += snprintf(o, (size_t)(buf + cap - o), "%lu", chunk[k - 1]);
    for (long i = k - 2; i >= 0; i--) o += snprintf(o, (size_t)(buf + cap - o), "%019lu", chunk[i]);
    long cell = prism_str_lit(buf, o - buf);
    free(t);
    free(chunk);
    free(buf);
    return cell;
}

/* Lean-model Int: a tagged immediate (v<<1|1) when the value fits 63 bits, a
 * PRISM_BIG_TAG cell otherwise. Canonical form is the invariant: every entry
 * point that produces an Int returns an immediate whenever the mathematical
 * value fits, so equal values never split across representations. None of
 * these functions consume their arguments; callers rc_dec after the call. */
#define PRISM_IMM_MAX ((1L << 62) - 1)
#define PRISM_IMM_MIN (-(1L << 62))

static long int_imm(long v) {
    /* Shift in unsigned: a signed left-shift of a negative value is UB in C
     * (works at -O2, but UBSan flags it). This wraps mod 2^64, matching the
     * codegen side's wrapping_shl(1) | 1 (src/codegen/emit.rs). */
    return (long)(((unsigned long)v << 1) | 1UL);
}

static long big_norm(long b) {
    long n = big_count(b);
    unsigned long lo = big_mag(b) ? big_limbs(b)[0] : 0;
    if (big_mag(b) <= 1 && lo <= (n < 0 ? 1UL << 62 : (unsigned long)PRISM_IMM_MAX)) {
        prism_rc_dec(b);
        return int_imm(n < 0 ? -(long)lo : (long)lo);
    }
    return b;
}

static long int_as_big(long w, int *fresh) {
    *fresh = (int)(w & 1);
    return *fresh ? prism_big_from_int(w >> 1) : w;
}

static long int_slow(long a, long b, long (*f)(long, long)) {
    int fa, fb;
    long ba = int_as_big(a, &fa), bb = int_as_big(b, &fb);
    long r = f(ba, bb);
    if (fa) prism_rc_dec(ba);
    if (fb) prism_rc_dec(bb);
    return big_norm(r);
}

long prism_rt_int_add(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_add_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_add);
}

long prism_rt_int_sub(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_sub_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_sub);
}

long prism_rt_int_mul(long a, long b) {
    long r;
    if ((a & b & 1) && !__builtin_mul_overflow(a >> 1, b >> 1, &r) && r >= PRISM_IMM_MIN &&
        r <= PRISM_IMM_MAX)
        return int_imm(r);
    return int_slow(a, b, prism_big_mul);
}

long prism_rt_int_div(long a, long b) {
    if (a & b & 1) {
        long y = b >> 1;
        if (y == 0) prism_div_zero();
        long q = (a >> 1) / y;
        if (q >= PRISM_IMM_MIN && q <= PRISM_IMM_MAX) return int_imm(q);
    }
    return int_slow(a, b, prism_big_div);
}

long prism_rt_int_rem(long a, long b) {
    if (a & b & 1) {
        long y = b >> 1;
        if (y == 0) prism_div_zero();
        return int_imm((a >> 1) % y);
    }
    return int_slow(a, b, prism_big_rem);
}

long prism_rt_int_cmp(long a, long b) {
    if (a & b & 1) return a < b ? -1 : a > b ? 1 : 0;
    int fa, fb;
    long ba = int_as_big(a, &fa), bb = int_as_big(b, &fb);
    long c = prism_big_cmp(ba, bb);
    if (fa) prism_rc_dec(ba);
    if (fb) prism_rc_dec(bb);
    return c;
}

long prism_show_int(long w) {
    if (w & 1) {
        char buf[32];
        int k = snprintf(buf, sizeof buf, "%ld", w >> 1);
        return prism_str_lit(buf, k);
    }
    return prism_big_show(w);
}

/* ---- native sort kernel (the `sort`/`sort_by_ord` fast path) ---------------
 * `kind` selects how to compare two element words off the cons spine:
 *   0 Integer (tagged-or-bignum, via prism_rt_int_cmp), 1 I64, 2 U64, 3 Float,
 * the last three boxed (one payload word). Floats use the IEEE total order so
 * the result matches the interpreter's f64::total_cmp. */
static unsigned long prism_flt_key(long boxed) {
    unsigned long b = (unsigned long)prism_unbox(boxed);
    return (b >> 63) ? ~b : (b | 0x8000000000000000UL);
}

static int prism_sort_cmp(long kind, long a, long b) {
    switch (kind) {
    case 1: {
        long x = prism_unbox(a), y = prism_unbox(b);
        return (x > y) - (x < y);
    }
    case 2: {
        unsigned long x = (unsigned long)prism_unbox(a), y = (unsigned long)prism_unbox(b);
        return (x > y) - (x < y);
    }
    case 3: {
        unsigned long x = prism_flt_key(a), y = prism_flt_key(b);
        return (x > y) - (x < y);
    }
    default: {
        long c = prism_rt_int_cmp(a, b);
        return (c > 0) - (c < 0);
    }
    }
}

/* Stable bottom-up merge sort of `src` (length n), ping-ponging with `buf`;
 * returns whichever buffer holds the sorted result. */
static long *prism_msort(long *src, long *buf, long n, long kind) {
    for (long w = 1; w < n; w *= 2) {
        for (long i = 0; i < n; i += 2 * w) {
            long mid = i + w < n ? i + w : n;
            long hi = i + 2 * w < n ? i + 2 * w : n;
            long a = i, b = mid, k = i;
            while (a < mid && b < hi)
                buf[k++] = prism_sort_cmp(kind, src[b], src[a]) < 0 ? src[b++] : src[a++];
            while (a < mid) buf[k++] = src[a++];
            while (b < hi) buf[k++] = src[b++];
        }
        long *t = src;
        src = buf;
        buf = t;
    }
    return src;
}

/* The unsigned radix key for a fixed-width element so plain ascending u64 order
 * reproduces the element's order: flip the sign bit for signed i64, pass u64
 * through, and use the IEEE total-order transform for floats. */
static unsigned long prism_sort_key(long kind, long h) {
    switch (kind) {
    case 1: return (unsigned long)prism_unbox(h) ^ 0x8000000000000000UL;
    case 2: return (unsigned long)prism_unbox(h);
    case 3: return prism_flt_key(h);
    default: return 0;
    }
}

/* Stable LSD radix sort (eight byte passes) of `heads` by parallel `keys`. Eight
 * passes is even, so the sorted result lands back in `heads`/`keys`. */
static void prism_radix(long *heads, unsigned long *keys, long n) {
    long *th = malloc((size_t)n * sizeof(long));
    unsigned long *tk = malloc((size_t)n * sizeof(unsigned long));
    if (!th || !tk) abort();
    long *sh = heads, *dh = th;
    unsigned long *sk = keys, *dk = tk;
    for (int shift = 0; shift < 64; shift += 8) {
        long count[256] = {0};
        for (long i = 0; i < n; i++) count[(sk[i] >> shift) & 0xff]++;
        long sum = 0;
        for (int b = 0; b < 256; b++) {
            long c = count[b];
            count[b] = sum;
            sum += c;
        }
        for (long i = 0; i < n; i++) {
            long pos = count[(sk[i] >> shift) & 0xff]++;
            dh[pos] = sh[i];
            dk[pos] = sk[i];
        }
        long *t = sh;
        sh = dh;
        dh = t;
        unsigned long *u = sk;
        sk = dk;
        dk = u;
    }
    free(th);
    free(tk);
}

/* Borrows `list` (builtin args are dropped by the caller) and returns a sorted
 * list. Fixed-width elements use radix; Integer keeps the bignum-aware merge.
 * When the spine is uniquely owned (every cell rc == 1) the cells are reused in
 * place -- the sorted heads are written back into the existing spine, no
 * allocation -- and the result aliases `list`, which the caller drops twice (the
 * borrowed arg and the returned value), so its rc is bumped once to balance.
 * A shared spine falls back to a fresh copy that shares each element (one
 * rc_inc). Either way the live-cell balance holds. Cons/Nil tags are read off
 * the input spine, so no constructor layout is baked in here. */
long prism_sort_prim(long kind, long list) {
    kind >>= 1; /* untag the small-int kind */
    long n = 0;
    for (long q = list; !(q & 1) && q && ((long *)q)[PRISM_ARITY_W] == 2;
         q = ((long *)q)[PRISM_HDR_WORDS + 1])
        n++;

    long *cells = n ? malloc((size_t)n * sizeof(long)) : NULL;
    long *heads = n ? malloc((size_t)n * sizeof(long)) : NULL;
    if (n && (!cells || !heads)) abort();
    long cons_tag = 0, i = 0, p = list, unique = 1;
    while (!(p & 1) && p && ((long *)p)[PRISM_ARITY_W] == 2) {
        long *cell = (long *)p;
        if (i == 0) cons_tag = cell[PRISM_TAG_W];
        if (cell[PRISM_RC_W] != 1) unique = 0;
        cells[i] = p;
        heads[i] = cell[PRISM_HDR_WORDS + 0];
        i++;
        p = cell[PRISM_HDR_WORDS + 1];
    }
    long nil_tag = (!(p & 1) && p) ? ((long *)p)[PRISM_TAG_W] : 0;

    if (n > 1) {
        if (kind == 0) {
            long *buf = malloc((size_t)n * sizeof(long));
            if (!buf) abort();
            long *res = prism_msort(heads, buf, n, kind);
            if (res != heads) memcpy(heads, res, (size_t)n * sizeof(long));
            free(buf);
        } else {
            unsigned long *keys = malloc((size_t)n * sizeof(unsigned long));
            if (!keys) abort();
            for (long j = 0; j < n; j++) keys[j] = prism_sort_key(kind, heads[j]);
            prism_radix(heads, keys, n);
            free(keys);
        }
    }

    long ret;
    if (unique) {
        for (long j = 0; j < n; j++) ((long *)cells[j])[PRISM_HDR_WORDS + 0] = heads[j];
        prism_rc_inc(list);
        ret = list;
    } else {
        long *nil = prism_alloc(0);
        nil[PRISM_TAG_W] = nil_tag;
        long acc = (long)nil;
        for (long j = n - 1; j >= 0; j--) {
            prism_rc_inc(heads[j]);
            long *c = prism_alloc(2);
            c[PRISM_TAG_W] = cons_tag;
            c[PRISM_HDR_WORDS + 0] = heads[j];
            c[PRISM_HDR_WORDS + 1] = acc;
            acc = (long)c;
        }
        ret = acc;
    }
    free(cells);
    free(heads);
    return ret;
}

/* Generic print for values whose type elaboration could not pin down (a var
 * read is an effect op whose row-polymorphic signature hides the payload
 * type). Cells are self-describing via their tag, so dispatch at runtime to
 * keep parity with the interpreter's dynamic show: a tagged immediate is an
 * Int, the zero word is Unit, and the two payload tags render themselves.
 *
 * A constructor, tuple, or list cell has no runtime type or field-name table to
 * show faithfully, so it cannot legitimately reach here; the elaborator routes
 * every statically-known structural type through the synthesized `show`. The
 * final `else` is an always-on guard (one tag compare, free on this IO-bound
 * path): rather than hand a foreign cell to prism_big_show, which would read its
 * header word as a limb count and its fields as magnitude, it traps. */
void prism_print_int(long w) {
    if (w & 1) {
        printf("%ld", w >> 1);
    } else if (!w) {
        printf("()"); /* Unit is the zero word; match the interpreter's `()`. */
    } else if (((long *)w)[PRISM_TAG_W] == PRISM_STR_TAG) {
        printf("%s", prism_str_data(w));
    } else if (((long *)w)[PRISM_TAG_W] == PRISM_BIG_TAG) {
        long s = prism_big_show(w);
        printf("%s", prism_str_data(s));
        prism_rc_dec(s);
    } else {
        fprintf(stderr,
                "fatal: print: non-printable value with heap tag %#lx reached "
                "the raw integer printer\n",
                (unsigned long)((long *)w)[PRISM_TAG_W]);
        abort();
    }
}

void prism_print_nl(void) {
    putchar('\n');
}

/* SplitMix64. A single global stream, seeded to the same default constant the
 * interpreter uses so unseeded `rand` is reproducible across backends. */
static unsigned long prism_rng = 0x9E3779B97F4A7C15UL;

void prism_srand(long seed) {
    prism_rng = (unsigned long)seed;
}

long prism_prim_rand(void) {
    prism_rng += 0x9E3779B97F4A7C15UL;
    unsigned long z = prism_rng;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
    z ^= z >> 31;
    return (long)(z >> 2);
}

long prism_parse_float(long s) {
    // Mirror the interpreter's `s.trim().parse::<f64>()`: the whole trimmed
    // string must be a valid decimal float, else 0.0. strtod alone diverges by
    // accepting trailing garbage (`3.14x` -> 3.14) and hex (`0x10` -> 16), which
    // the Rust parser rejects.
    const char *data = prism_str_data(s);
    while (isspace((unsigned char)*data)) data++;
    const char *digits = data + (*data == '+' || *data == '-' ? 1 : 0);
    int hex = digits[0] == '0' && (digits[1] == 'x' || digits[1] == 'X');
    char *end;
    double d = strtod(data, &end);
    if (hex || end == data) {
        d = 0.0;
    } else {
        while (isspace((unsigned char)*end)) end++;
        if (*end != '\0') d = 0.0;
    }
    long bits;
    memcpy(&bits, &d, 8);
    return prism_box(bits);
}

long prism_pow_float(long a, long b) {
    double x, y;
    memcpy(&x, &a, 8);
    memcpy(&y, &b, 8);
    double r = pow(x, y);
    long bits;
    memcpy(&bits, &r, 8);
    return prism_box(bits);
}

long prism_show_float_prec(long f, long digits) {
    double d;
    memcpy(&d, &f, 8);
    if (digits < 0) digits = 0;
    char buf[64];
    int k = snprintf(buf, sizeof buf, "%.*f", (int)digits, d);
    if (k < 0) k = 0;
    if (k >= (int)sizeof buf) k = (int)sizeof buf - 1;
    return prism_str_lit(buf, k);
}

/* Trim ASCII whitespace, optional sign, then strict base-10 digits of any
 * length: Some(n) on success, None on empty/non-numeric input. */
long prism_parse_int(long s) {
    int ok = 0;
    long b = prism_big_of_str(s, &ok);
    if (!ok) return prism_ctor(0, 0, 0); /* None */
    long n = big_norm(b);
    return prism_ctor(1, 1, &n); /* Some(n) */
}

/* Elaborator-only: a big literal whose text is known-valid digits, so it skips
 * the Option wrapper and returns the raw Integer cell. */
long prism_big_lit(long s) {
    int ok = 0;
    return big_norm(prism_big_of_str(s, &ok));
}

/* I64 and U64 are boxed 64-bit payload cells like Float. Arithmetic wraps mod
 * 2^64 and is sign-agnostic, so add/sub/mul are shared by both types. */
static unsigned long int_low64(long w) {
    if (w & 1) return (unsigned long)(w >> 1);
    unsigned long lo = big_mag(w) ? big_limbs(w)[0] : 0;
    return big_count(w) < 0 ? (unsigned long)(~lo) + 1UL : lo;
}

long prism_to_i64(long w) {
    return prism_box((long)int_low64(w));
}

long prism_to_u64(long w) {
    return prism_box((long)int_low64(w));
}

/* Encode a raw machine integer as a Prism Int: a tagged immediate when it fits
 * the 63-bit immediate range, a bignum cell otherwise. The single encoding
 * chokepoint for values entering from the machine-word world (boxed i64/u64
 * conversions, read_int). */
long prism_int_of_long(long v) {
    if (v >= PRISM_IMM_MIN && v <= PRISM_IMM_MAX) return int_imm(v);
    return prism_big_from_int(v);
}

long prism_int_of_i64(long p) {
    return prism_int_of_long(prism_unbox(p));
}

long prism_int_of_u64(long p) {
    unsigned long v = (unsigned long)prism_unbox(p);
    if (v <= (unsigned long)PRISM_IMM_MAX) return int_imm((long)v);
    return big_make(&v, 1, 0);
}

long prism_i64_add(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) + (unsigned long)prism_unbox(b)));
}

long prism_i64_sub(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) - (unsigned long)prism_unbox(b)));
}

long prism_i64_mul(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) * (unsigned long)prism_unbox(b)));
}

long prism_i64_div(long a, long b) {
    long x = prism_unbox(a), y = prism_unbox(b);
    if (y == 0) prism_div_zero();
    if (y == -1) return prism_box((long)(0UL - (unsigned long)x)); /* MIN/-1 wraps */
    return prism_box(x / y);
}

long prism_i64_rem(long a, long b) {
    long y = prism_unbox(b);
    if (y == 0) prism_div_zero();
    if (y == -1) return prism_box(0);
    return prism_box(prism_unbox(a) % y);
}

long prism_u64_div(long a, long b) {
    unsigned long y = (unsigned long)prism_unbox(b);
    if (y == 0) prism_div_zero();
    return prism_box((long)((unsigned long)prism_unbox(a) / y));
}

long prism_u64_rem(long a, long b) {
    unsigned long y = (unsigned long)prism_unbox(b);
    if (y == 0) prism_div_zero();
    return prism_box((long)((unsigned long)prism_unbox(a) % y));
}

long prism_i64_cmp(long a, long b) {
    long x = prism_unbox(a), y = prism_unbox(b);
    return x < y ? -1 : x > y ? 1 : 0;
}

long prism_u64_cmp(long a, long b) {
    unsigned long x = (unsigned long)prism_unbox(a), y = (unsigned long)prism_unbox(b);
    return x < y ? -1 : x > y ? 1 : 0;
}

/* Wrapping add/sub/mul share a bit pattern across signedness, so the u64 lane
   reuses the i64 wraparound. */
long prism_u64_add(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) + (unsigned long)prism_unbox(b)));
}
long prism_u64_sub(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) - (unsigned long)prism_unbox(b)));
}
long prism_u64_mul(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) * (unsigned long)prism_unbox(b)));
}

/* Fixed-width bitwise/shift. and/or/xor are bit-pattern identical across lanes;
   shifts mask the count to 0..64. i64_shr is arithmetic (signed >>), u64_shr
   logical (unsigned >>). */
long prism_i64_and(long a, long b) {
    return prism_box(prism_unbox(a) & prism_unbox(b));
}
long prism_i64_or(long a, long b) {
    return prism_box(prism_unbox(a) | prism_unbox(b));
}
long prism_i64_xor(long a, long b) {
    return prism_box(prism_unbox(a) ^ prism_unbox(b));
}
long prism_u64_and(long a, long b) {
    return prism_box(prism_unbox(a) & prism_unbox(b));
}
long prism_u64_or(long a, long b) {
    return prism_box(prism_unbox(a) | prism_unbox(b));
}
long prism_u64_xor(long a, long b) {
    return prism_box(prism_unbox(a) ^ prism_unbox(b));
}

long prism_i64_shl(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) << (prism_unbox(b) & 63)));
}
long prism_i64_shr(long a, long b) {
    return prism_box(prism_unbox(a) >> (prism_unbox(b) & 63)); /* arithmetic */
}
long prism_u64_shl(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) << (prism_unbox(b) & 63)));
}
long prism_u64_shr(long a, long b) {
    return prism_box((long)((unsigned long)prism_unbox(a) >> (prism_unbox(b) & 63))); /* logical */
}

long prism_show_i64(long p) {
    char buf[32];
    int k = snprintf(buf, sizeof buf, "%ld", prism_unbox(p));
    return prism_str_lit(buf, k);
}

long prism_show_u64(long p) {
    char buf[32];
    int k = snprintf(buf, sizeof buf, "%lu", (unsigned long)prism_unbox(p));
    return prism_str_lit(buf, k);
}

/* OS surface. getenv/arg return a fresh counted string cell (empty when
 * unset, never NULL), writes consume their argument cells via the caller's
 * rc_dec and return unit. read_file fails loudly on any error and caps the
 * slurp so a pathological file cannot exhaust memory. */
#define PRISM_READ_CAP (1L << 30)

static void prism_read_fatal(const char *why, const char *path) {
    fprintf(stderr, "prism: read_file: %s: %s\n", why, path);
    exit(1);
}

static int prism_argc = 0;
static char **prism_argv = 0;

long prism_prim_args_count(void) {
    return prism_argc;
}

long prism_prim_arg(long i) {
    if (i < 0 || i >= prism_argc) return prism_str_lit("", 0);
    const char *a = prism_argv[i];
    return prism_str_lit(a, (long)strlen(a));
}

long prism_prim_getenv(long name) {
    const char *v = getenv(prism_str_data(name));
    if (!v) return prism_str_lit("", 0);
    return prism_str_lit(v, (long)strlen(v));
}

long prism_prim_read_file(long path) {
    const char *name = prism_str_data(path);
    FILE *f = fopen(name, "rb");
    if (!f) prism_read_fatal("cannot open", name);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) prism_read_fatal("cannot size", name);
    if (n > PRISM_READ_CAP) prism_read_fatal("exceeds 1GB cap", name);
    long *p = prism_str_alloc(n);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    long got = (long)fread(o, 1, (size_t)n, f);
    o[got] = 0;
    p[PRISM_ARITY_W] = got;
    fclose(f);
    return (long)p;
}

/* Result(Unit, String): Ok(()) with the immediate Unit field, or Err(msg). */
static long prism_file_ok(void) {
    long unit = 0;
    return prism_ctor(0, 1, &unit);
}

static long prism_file_err(const char *msg) {
    long s = prism_str_lit(msg, (long)strlen(msg));
    return prism_ctor(1, 1, &s);
}

static long prism_file_write(long path, long contents, const char *mode) {
    FILE *f = fopen(prism_str_data(path), mode);
    if (!f) return prism_file_err("cannot open file for writing");
    size_t want = (size_t)prism_str_len_bytes(contents);
    size_t got = fwrite(prism_str_data(contents), 1, want, f);
    fclose(f);
    if (got < want) return prism_file_err("short write");
    return prism_file_ok();
}

long prism_write_file(long path, long contents) {
    return prism_file_write(path, contents, "wb");
}

long prism_append_file(long path, long contents) {
    return prism_file_write(path, contents, "ab");
}

long prism_prim_file_exists(long path) {
    FILE *f = fopen(prism_str_data(path), "rb");
    if (f) fclose(f);
    return f != 0;
}

long prism_remove_file(long path) {
    remove(prism_str_data(path));
    return 0;
}

void prism_array_oob(void) {
    fprintf(stderr, "fatal: array index out of bounds\n");
    exit(1);
}

/* Growable polymorphic array as an ordinary cell
   { rc, tag=0, arity=cap+1, len, elem0..elem_{cap-1} }, so prism_rc_dec already
   recurses into it: the length word is stored odd-tagged (skipped as an
   immediate), live slots hold elements, spare slots hold 0 (also skipped). All
   ops BORROW their cell args (the call site drops them afterward), so each
   retains a ref by inc-ing what it stores or returns. Indices arrive raw. */
#define PRISM_ARR_ELEM0 (PRISM_HDR_WORDS + 1)
static long arr_len(long *p) {
    return p[PRISM_HDR_WORDS] >> 1;
}
static void arr_setlen(long *p, long l) {
    p[PRISM_HDR_WORDS] = (l << 1) | 1;
}
static long arr_cap(long *p) {
    return p[PRISM_ARITY_W] - 1;
}

long prism_array_empty(void) {
    long *p = prism_alloc(1); /* cap 0: just the length word */
    arr_setlen(p, 0);
    return (long)p;
}

long prism_array_new(long n, long init) {
    long *p = prism_alloc(n + 1); /* cap = len = n */
    arr_setlen(p, n);
    for (long i = 0; i < n; i++) {
        prism_rc_inc(init);
        p[PRISM_ARR_ELEM0 + i] = init;
    }
    return (long)p;
}

long prism_array_len(long a) {
    return arr_len((long *)a); /* raw count; the call site retags it */
}

long prism_array_get(long a, long i) {
    long *p = (long *)a;
    if (i < 0 || i >= arr_len(p)) prism_array_oob();
    long e = p[PRISM_ARR_ELEM0 + i];
    prism_rc_inc(e); /* returned ref; the borrowed array is dropped by the caller */
    return e;
}

long prism_array_set(long a, long i, long x) {
    long *p = (long *)a;
    long len = arr_len(p);
    if (i < 0 || i >= len) prism_array_oob();
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: write in place (FBIP) */
        prism_rc_dec(p[PRISM_ARR_ELEM0 + i]);
        prism_rc_inc(x);
        p[PRISM_ARR_ELEM0 + i] = x;
        prism_rc_inc(a); /* survive the caller's drop of the borrowed arg */
        return a;
    }
    long *q = prism_alloc(len + 1); /* shared: copy compactly then set */
    arr_setlen(q, len);
    for (long j = 0; j < len; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    prism_rc_dec(q[PRISM_ARR_ELEM0 + i]);
    prism_rc_inc(x);
    q[PRISM_ARR_ELEM0 + i] = x;
    return (long)q;
}

long prism_array_push(long a, long x) {
    long *p = (long *)a;
    long len = arr_len(p), cap = arr_cap(p);
    if (p[PRISM_RC_W] == 1 && len < cap) { /* room and unique: append in place */
        prism_rc_inc(x);
        p[PRISM_ARR_ELEM0 + len] = x;
        arr_setlen(p, len + 1);
        prism_rc_inc(a); /* survive the caller's drop */
        return a;
    }
    /* full (grow, doubling) or shared (copy): one fresh array of the new size */
    long ncap = len < cap ? cap : (cap < 1 ? 1 : cap * 2);
    long *q = prism_alloc(ncap + 1);
    arr_setlen(q, len + 1);
    for (long j = 0; j < len; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    prism_rc_inc(x);
    q[PRISM_ARR_ELEM0 + len] = x;
    for (long j = len + 1; j < ncap; j++) q[PRISM_ARR_ELEM0 + j] = 0; /* skip-safe spare */
    return (long)q;
}

long prism_array_pop(long a) {
    long *p = (long *)a;
    long len = arr_len(p);
    if (len <= 0) prism_array_oob();
    if (p[PRISM_RC_W] == 1) { /* uniquely owned: drop the last in place */
        prism_rc_dec(p[PRISM_ARR_ELEM0 + len - 1]);
        p[PRISM_ARR_ELEM0 + len - 1] = 0; /* skip-safe spare */
        arr_setlen(p, len - 1);
        prism_rc_inc(a);
        return a;
    }
    long *q = prism_alloc(len); /* shared: copy len-1 elements */
    arr_setlen(q, len - 1);
    for (long j = 0; j < len - 1; j++) {
        long e = p[PRISM_ARR_ELEM0 + j];
        prism_rc_inc(e);
        q[PRISM_ARR_ELEM0 + j] = e;
    }
    return (long)q;
}

/* Concatenate every string in an array into one fresh string with a single
   allocation. Borrows the array (the caller drops it and its elements). */
long prism_string_of_array(long arr) {
    long *p = (long *)arr;
    long n = arr_len(p);
    long total = 0;
    for (long i = 0; i < n; i++) total += prism_str_len_bytes(p[PRISM_ARR_ELEM0 + i]);
    long *out = prism_str_alloc(total);
    char *o = (char *)(out + PRISM_HDR_WORDS);
    long off = 0;
    for (long i = 0; i < n; i++) {
        long s = p[PRISM_ARR_ELEM0 + i];
        long len = prism_str_len_bytes(s);
        memcpy(o + off, prism_str_data(s), (size_t)len);
        off += len;
    }
    o[total] = 0;
    return (long)out;
}

/* Classify the UTF-8 sequence at raw[i..n). On a well-formed sequence set *adv
 * to its length and return 1. On an ill-formed one set *adv to the length of the
 * maximal valid subpart (>=1, clamped to the bytes remaining when the sequence
 * runs off the end) and return 0; the caller emits a single U+FFFD and skips
 * *adv bytes. This is Rust's `from_utf8_lossy` decoder (Unicode Table 3-7 with
 * substitution of maximal subparts), which the interpreter uses via
 * `String::from_utf8_lossy`; the two must stay byte-identical. */
static int prism_utf8_seq(const unsigned char *raw, long i, long n, long *adv) {
    unsigned char b0 = raw[i];
    if (b0 < 0x80) {
        *adv = 1;
        return 1;
    }
    if (b0 < 0xC2 || b0 > 0xF4) { /* 0x80..0xC1 and 0xF5..0xFF are invalid leads */
        *adv = 1;
        return 0;
    }
    /* Continuation-byte ranges depend on the lead: E0/ED and F0/F4 narrow the
     * second byte to exclude overlong encodings and surrogates (Table 3-7). */
    long lo1 = 0x80, hi1 = 0xBF;
    long width;
    if (b0 < 0xE0) {
        width = 2;
    } else if (b0 < 0xF0) {
        width = 3;
        if (b0 == 0xE0)
            lo1 = 0xA0;
        else if (b0 == 0xED)
            hi1 = 0x9F;
    } else {
        width = 4;
        if (b0 == 0xF0)
            lo1 = 0x90;
        else if (b0 == 0xF4)
            hi1 = 0x8F;
    }
    for (long k = 1; k < width; k++) {
        if (i + k >= n) { /* incomplete trailing sequence: one U+FFFD for the rest */
            *adv = n - i;
            return 0;
        }
        unsigned char b = raw[i + k];
        long lo = k == 1 ? lo1 : 0x80;
        long hi = k == 1 ? hi1 : 0xBF;
        if (b < lo || b > hi) {
            *adv = k; /* the k valid bytes are the maximal subpart */
            return 0;
        }
    }
    *adv = width;
    return 1;
}

/* Build a string from an array of byte values (each a small Int 0..255, stored
   tagged so `>> 1` recovers it), replacing any ill-formed UTF-8 with U+FFFD so
   the result is byte-identical to the interpreter's lossy decode. Borrows the
   array. */
long prism_string_of_bytes(long arr) {
    long *p = (long *)arr;
    long n = arr_len(p);
    unsigned char *raw = malloc((size_t)(n > 0 ? n : 1));
    if (!raw) abort();
    for (long i = 0; i < n; i++) raw[i] = (unsigned char)((p[PRISM_ARR_ELEM0 + i] >> 1) & 0xFF);
    /* Two passes over the same deterministic decode: size, then fill. A U+FFFD
     * (0xEF 0xBF 0xBD) is three bytes, so the output can outgrow the input. */
    long out_len = 0;
    for (long i = 0; i < n;) {
        long adv;
        out_len += prism_utf8_seq(raw, i, n, &adv) ? adv : 3;
        i += adv;
    }
    long *out = prism_str_alloc(out_len);
    char *o = (char *)(out + PRISM_HDR_WORDS);
    long off = 0;
    for (long i = 0; i < n;) {
        long adv;
        if (prism_utf8_seq(raw, i, n, &adv)) {
            memcpy(o + off, raw + i, (size_t)adv);
            off += adv;
        } else {
            o[off] = (char)0xEF;
            o[off + 1] = (char)0xBF;
            o[off + 2] = (char)0xBD;
            off += 3;
        }
        i += adv;
    }
    o[out_len] = 0;
    free(raw);
    return (long)out;
}

/* Run a shell command, returning its exit code (-1 on spawn failure or signal
   death). The result is a raw int the call site retags as an Int. */
long prism_system(long cmd) {
    int rc = system(prism_str_data(cmd));
    if (rc == -1 || !WIFEXITED(rc)) return -1;
    return WEXITSTATUS(rc);
}

/* Write a string to stderr (no trailing newline). Returns unit. */
long prism_eprint(long s) {
    fputs(prism_str_data(s), stderr);
    return 0;
}

long prism_exit(long code) {
    exit((int)code);
}

extern long prism_main(void);

int main(int argc, char **argv) {
    prism_argc = argc;
    prism_argv = argv;
    long r = prism_main();
    int code = (int)(r & 1 ? r >> 1 : 0);
    if (!(r & 1) && r) prism_rc_dec(r);
    return code;
}
