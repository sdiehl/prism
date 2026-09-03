// Performance ratchets that `parity.rs` cannot see. A fusion or reuse regression
// produces byte-identical output and zero leaks, so the parity/leak gate stays
// green while the language's headline optimizations silently fall back to the
// slow path. These tests check the runtime allocation counters instead:
//
//   - evidence passing + stream fusion must allocate ZERO free-monad eff-op
//     cells on the fusion corpus (`PRISM_EFFOP_STATS`), and
//   - drop-guided in-place constructor reuse must actually fire at runtime
//     (`PRISM_REUSE_STATS`), the runtime complement to the static IR check in
//     `snapshots.rs`.
//
// Built once per program through the native backend, so they ride the same
// toolchain as the parity gate. A missing C compiler is a hard failure, not a
// silent skip: these ratchets are worthless if they pass without ever building
// natively.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;
use std::{env, fs};

use crate::support::{stat_build_counters, ALLOCATED_BYTES_SUFFIX, ALLOC_STATS};

// Corpus discovery and prelude-prepending source loader, shared with the parity
// oracles. The tier manifest below records the same program set those gates diff, so
// it reuses the one definition of "the runnable corpus" rather than rediscovering
// it. `corpus`/`source` are the two shared support helpers this file leans on.

const PERF_FLAT_VAR_WHILE: &str = include_str!("../cases/perf/flat_var_while.pr");
const PERF_FLAT_VAR_FOR: &str = include_str!("../cases/perf/flat_var_for.pr");
const PERF_FLAT_EARLY_RETURN: &str = include_str!("../cases/perf/flat_early_return.pr");
const PERF_PULL_SEQUENCE_MODULE: &str = include_str!("../cases/perf/pull_sequence_module.pr");
const PERF_EACH_UPDATE_REUSE: &str = include_str!("../cases/perf/each_update_reuse.pr");
const PERF_STACK_TAIL_RECURSION: &str = include_str!("../cases/perf/stack_tail_recursion.pr");
const PERF_STACK_VAR_WHILE: &str = include_str!("../cases/perf/stack_var_while.pr");
const PERF_STACK_VAR_FOR: &str = include_str!("../cases/perf/stack_var_for.pr");
const PERF_STACK_CONTINUE_WHILE: &str = include_str!("../cases/perf/stack_continue_while.pr");
const PERF_STACK_BREAK_WHILE: &str = include_str!("../cases/perf/stack_break_while.pr");
const PERF_STACK_EARLY_RETURN: &str = include_str!("../cases/perf/stack_early_return.pr");
const PERF_PARAM_PASSING_STATE: &str = include_str!("../cases/perf/param_passing_state.pr");
const PERF_DEEP_ABORT: &str = include_str!("../cases/perf/deep_abort.pr");
const PERF_SCHEDULER_YIELD: &str = include_str!("../cases/perf/scheduler_yield.pr");
const PERF_COMP_MAP_FUSED: &str = include_str!("../cases/perf/comp_map_fused.pr");
const PERF_COMP_MAP_GUARDED: &str = include_str!("../cases/perf/comp_map_guarded.pr");
const PERF_WIRE_ENCODE: &str = include_str!("../cases/perf/wire_encode.pr");
const PERF_WIRE_DECODE: &str = include_str!("../cases/perf/wire_decode.pr");
const PERF_BUF_CHUNKS: &str = include_str!("../cases/perf/buf_chunks.pr");
const PERF_BYTES_CODEC: &str = include_str!("../cases/perf/bytes_codec_slope.pr");
const PERF_STR_SLICE_WINDOW: &str = include_str!("../cases/perf/str_slice_window.pr");
const PERF_JSON_ESCAPE_RUNS: &str = include_str!("../cases/perf/json_escape_runs.pr");
const PERF_BYTES_BODY_DECODE: &str = include_str!("../cases/perf/bytes_body_decode.pr");

const N_PLACEHOLDER: &str = "__N__";
const PIPELINE_PLACEHOLDER: &str = "__PIPELINE__";
const RUN_STRATEGY_PLACEHOLDER: &str = "run_strategy";

fn cc() -> String {
    env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn instantiate(template: &str, replacements: &[(&str, String)]) -> String {
    replacements
        .iter()
        .fold(template.to_string(), |src, (needle, value)| {
            src.replace(needle, value)
        })
}

fn perf_src(template: &str, replacements: &[(&str, String)]) -> String {
    prism::with_prelude(&instantiate(template, replacements))
}

fn perf_src_n(template: &str, n: i64) -> String {
    perf_src(template, &[(N_PLACEHOLDER, n.to_string())])
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

// Assert a C compiler is reachable, panicking with an actionable message if not.
// A performance ratchet that never builds natively passes vacuously, so its
// absence fails the test loudly.
fn require_cc() {
    assert!(
        have(&cc()),
        r"C compiler `{}` not found (set PRISM_CC). The native perf gate requires it; install clang or LLVM so the ratchets actually build.",
        cc()
    );
}

// Build `case` natively, run it with `stat_env=1`, and return the integer the
// runtime reports on the stderr line ending in `suffix` (`prism: N <suffix>`).
fn stat(case: &str, stat_env: &str, suffix: &str) -> Result<i64, String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(case);
    let src = fs::read_to_string(&path).map_err(|e| format!("{case}: {e}"))?;
    stat_src(&prism::with_prelude(&src), case, stat_env, suffix)
}

// Like `stat`, but builds from a source string already carrying the prelude, so a
// test can generate sized program variants. `tag` only names the temp binary.
fn stat_src(full: &str, tag: &str, stat_env: &str, suffix: &str) -> Result<i64, String> {
    stat_build(full, tag, stat_env, suffix, |src, bin| {
        prism::build(src, bin)
    })
}

// Like `stat_src`, but at -O2, where stream fusion is default-on and the pull
// Sequence guard requires zero allocation.
fn stat_src_o2(full: &str, tag: &str, stat_env: &str, suffix: &str) -> Result<i64, String> {
    stat_build(full, tag, stat_env, suffix, |src, bin| {
        let mut cfg = prism::Config::from_env();
        cfg.update_flags(|flags| flags.opt_level = prism::OptLevel::O2);
        prism::build_on(src, &prism::default_roots(Path::new(".")), bin, &cfg)
    })
}

fn stat_build(
    full: &str,
    tag: &str,
    stat_env: &str,
    suffix: &str,
    build: impl Fn(&str, &Path) -> Result<(), prism::error::Error>,
) -> Result<i64, String> {
    stat_build_many(full, tag, stat_env, &[suffix], build).map(|v| v[0])
}

// Every counter a stats run reports is on the same stderr, so a family of them
// costs one build and one run, not one per counter. The build/run/read path
// itself is the shared `stat_build_counters` in `support`.
fn stat_build_many(
    full: &str,
    tag: &str,
    stat_env: &str,
    suffixes: &[&str],
    build: impl Fn(&str, &Path) -> Result<(), prism::error::Error>,
) -> Result<Vec<i64>, String> {
    stat_build_counters(full, tag, &[stat_env], suffixes, build)
}

// The fusion corpus: each program drives a different path to the zero-allocation
// guarantee (evidence passing under one and two handlers, open re-emit inlining,
// first-class stream fusion, fold-consumer state threading, get-style multi-op
// `State`, and the full stake + mixed-mode showcase). Every one must allocate no
// `EOp` cells.
const FUSION_PROGRAMS: &[&str] = &[
    "tests/cases/run/effop_tax.pr",
    "tests/cases/run/eff_two_handlers.pr",
    "tests/cases/run/eff_fuse.pr",
    "examples/fixtures/compiler/stream_fuse.pr",
    "examples/fixtures/compiler/stream_fold.pr",
    "examples/streams.pr",
    "examples/eff_state.pr",
];

#[test]
fn effop_fast_path_allocates_nothing() {
    require_cc();
    let mut fails = Vec::new();
    for &prog in FUSION_PROGRAMS {
        match stat(prog, "PRISM_EFFOP_STATS", "eff ops allocated") {
            Ok(0) => {}
            Ok(n) => fails.push(format!(
                "{prog}: {n} eff ops allocated; the evidence/fusion fast path regressed (want 0)"
            )),
            Err(e) => fails.push(e),
        }
    }
    assert!(
        fails.is_empty(),
        "{} of {} fusion programs regressed:\n{}",
        fails.len(),
        FUSION_PROGRAMS.len(),
        fails.join("\n")
    );
}

// A guard-free comprehension `[ head for x in s ]` lowers to a fusing stream map
// (`scollect(smap(s, \x -> head))`), not to `scollect` over a first-class
// effectful for-consumer thunk. The map fuses with the collecting fold, so the
// pipeline reifies no free-monad eff-op cells: the whole comprehension runs as a
// loop that allocates only the result list. This checks that the fast path fires,
// because it is the only lowering that reaches zero eff-op cells; a revert to the
// thunk form allocates one eff-op cell per element (measured below on the guarded
// control, which keeps the thunk path). The control also keeps this gate honest:
// it proves the corpus can reach the free monad here, so the zero above is the
// fast path at work rather than a comprehension that never reified.
#[test]
fn guard_free_comprehension_fuses() {
    require_cc();
    let n = 4000_i64;
    let fused = stat_src(
        &perf_src_n(PERF_COMP_MAP_FUSED, n),
        "comp map fused",
        "PRISM_EFFOP_STATS",
        "eff ops allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        fused, 0,
        r"a guard-free comprehension allocated {fused} eff-op cell(s); want 0. The fusing `scollect(smap(..))` lowering regressed to the free-monad for-consumer thunk."
    );
    let guarded = stat_src(
        &perf_src_n(PERF_COMP_MAP_GUARDED, n),
        "comp map guarded",
        "PRISM_EFFOP_STATS",
        "eff ops allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        guarded > 0,
        r"the guarded control comprehension allocated no eff-op cells; the gate is vacuous unless the fallback path can reach the free monad (got {guarded})"
    );
}

// Local monadification: one escaping effectful closure must not drag an
// unrelated fused pipeline off the fused path. `local_mono_combined.pr` pairs the
// escaping Log component of `local_mono_escape.pr` with a 99-element fused stream
// pipeline over a disjoint effect. The pipeline must add zero eff-op cells, so the
// combined program allocates exactly as many as the escape alone. Before local
// monadification a single escaping closure flipped the whole program monadic and
// the pipeline would have allocated one cell per element. This is the definition
// of done for the locality work.
#[test]
fn local_monadification_keeps_pipeline_fused() {
    require_cc();
    let count = |case| stat(case, "PRISM_EFFOP_STATS", "eff ops allocated");
    let escape = count("tests/cases/run/local_mono_escape.pr").unwrap_or_else(|e| panic!("{e}"));
    let combined =
        count("tests/cases/run/local_mono_combined.pr").unwrap_or_else(|e| panic!("{e}"));
    assert!(
        escape > 0,
        r"the escaping Log component must itself allocate eff-op cells (got {escape}); the gate would be vacuous otherwise"
    );
    assert_eq!(
        combined,
        escape,
        r"adding a fused stream pipeline allocated {} extra eff-op cell(s); local monadification regressed and the unrelated pipeline left the fused path",
        combined - escape
    );
}

// Asymptotic allocation gate. An optimization that fires makes a program's heap
// allocation independent of its iteration count. We run each "flat-class" program
// (one whose useful work is O(n) but whose allocation should be O(1)) at two
// sizes and assert the eff-op allocation does not grow with n. This catches any
// program that silently reifies into the free monad instead of running as a loop,
// regardless of whether it was ever named in an allowlist: the failure shows up
// as growth, which a tiny fixed input would hide behind a small constant. (This
// is exactly the blind spot that let `var` loops ship allocating ~6 cells per
// iteration and overflowing the stack.)
#[test]
fn allocation_is_flat_for_constant_space_programs() {
    require_cc();
    // Each program must allocate O(1) eff-op cells regardless of `{N}`.
    let flat: &[(&str, &str)] = &[
        ("var while-loop accumulator", PERF_FLAT_VAR_WHILE),
        ("var for-loop accumulator", PERF_FLAT_VAR_FOR),
        (
            // Early `return` out of a loop: the return-aware driver builds an
            // SMore(ctl) cell per iteration, which the FBIP reuse pass recycles in
            // place, so allocation stays flat and never reifies into the free monad.
            "early-return loop",
            PERF_FLAT_EARLY_RETURN,
        ),
    ];
    let (small, big) = (1000_i64, 10_000_i64);
    let mut fails = Vec::new();
    for (name, tmpl) in flat {
        let mk = |n: i64| perf_src_n(tmpl, n);
        let lo = stat_src(&mk(small), name, "PRISM_EFFOP_STATS", "eff ops allocated");
        let hi = stat_src(&mk(big), name, "PRISM_EFFOP_STATS", "eff ops allocated");
        match (lo, hi) {
            (Ok(lo), Ok(hi)) => {
                // Flat means allocation does not grow with n; allow a tiny constant slack.
                if hi > lo + 16 {
                    let per_iter = (hi - lo) / (big - small);
                    fails.push(format!(
                        r"{name}: allocation scales with n ({lo} cells at n={small}, {hi} at n={big}; ~{per_iter} eff-op cells/iteration). The optimization is not firing: this reifies into the free monad instead of an O(1) loop."
                    ));
                }
            }
            (Err(e), _) | (_, Err(e)) => fails.push(e),
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// THE SEQUENCE FUSION GUARD. Drives `lib/std/Sequence.pr` through
// `import Sequence as Seq` and checks each pipeline's per-element allocation
// slope at zero. The stream-fusion pass (default-on at -O2)
// collapses the whole pipeline into a `%fuse$` join loop and the dead upstream
// combinator chain is eliminated, so these pipelines materialize no
// intermediates. A nonzero slope means fusion stopped at the import boundary.
const PULL_MODULE_BASELINE: &[(&str, &str, i64)] = &[
    ("range|sum", "Seq.sum(Seq.range(1, {HI}))", 0),
    (
        "range|map|sum",
        "Seq.sum(Seq.map(Seq.range(1, {HI}), \\(x) -> x * 2))",
        0,
    ),
    (
        "range|map|filter|sum",
        "Seq.sum(Seq.filter(Seq.map(Seq.range(1, {HI}), \\(x) -> x * 2), \\(x) -> x > 5))",
        0,
    ),
];

#[test]
fn pull_sequence_module_allocation_baseline() {
    require_cc();
    let (small, big) = (1000_i64, 10_000_i64);
    let mut fails = Vec::new();
    for (name, tmpl, slope) in PULL_MODULE_BASELINE {
        let mk = |n: i64| {
            perf_src(
                PERF_PULL_SEQUENCE_MODULE,
                &[(
                    PIPELINE_PLACEHOLDER,
                    tmpl.replace("{HI}", &(n + 1).to_string()),
                )],
            )
        };
        // Stream fusion is default-on at -O2, so measure the zero-allocation
        // guarantee there. A plain -O1 build runs this pipeline unfused.
        let lo = stat_src_o2(&mk(small), name, "PRISM_ALLOC_STATS", "cells allocated");
        let hi = stat_src_o2(&mk(big), name, "PRISM_ALLOC_STATS", "cells allocated");
        match (lo, hi) {
            (Ok(lo), Ok(hi)) => {
                let per = (hi - lo) / (big - small);
                if per != *slope {
                    fails.push(format!(
                        r"{name}: {per} cells/element through `import Sequence` (baseline {slope}; {lo} at n={small}, {hi} at n={big}). If cross-module stream fusion lowered this, ratchet the baseline down; otherwise a library combinator regressed."
                    ));
                }
            }
            (Err(e), _) | (_, Err(e)) => fails.push(e),
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// ---------------------------------------------------------------------------
// Wired-nullable layout ratchet. On the native tiers `Null` is the null word
// and `This(v)` is its element word, so the nullables in an N-element list
// allocate nothing: the list costs exactly its N `Cons` cells. Parity cannot
// see a silent regression to a tagged wrapper cell (the layouts are
// observationally identical); this counter can, reading 2 cells/element.

const PERF_OR_NULL_LIST: &str = include_str!("../cases/perf/or_null_list.pr");

#[test]
fn or_null_values_allocate_no_cells() {
    require_cc();
    let (small, big) = (1_000_i64, 10_000_i64);
    let lo = stat_src_o2(
        &perf_src_n(PERF_OR_NULL_LIST, small),
        "or_null_list_lo",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let hi = stat_src_o2(
        &perf_src_n(PERF_OR_NULL_LIST, big),
        "or_null_list_hi",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let per = (hi - lo) / (big - small);
    assert_eq!(
        per, 1,
        "a list of nullables allocates {per} cells/element ({lo} at n={small}, {hi} at \
         n={big}; baseline 1, the `Cons` cell alone); the wired nullable's cell-free \
         layout regressed to a wrapper allocation"
    );
}

// ---------------------------------------------------------------------------
// Region-allocation ratchets. A `with_arena` scope routes every eligible
// constructor through the region's bump pointer, so the cells never touch
// `prism_alloc` and the whole region is reclaimed at the handler's return.
// Parity and the leak balance cannot see a silent fallback to per-cell malloc
// (the delegating path is observationally identical); these counters can.

const PERF_ARENA_REGION_FILL: &str = include_str!("../cases/perf/arena_region_fill.pr");
const PERF_ARENA_REGION_LOOP: &str = include_str!("../cases/perf/arena_region_loop.pr");
const PERF_ARENA_PROMOTE_NONE: &str = include_str!("../cases/perf/arena_promote_none.pr");
const PERF_ARENA_PROMOTE_LINEAR: &str = include_str!("../cases/perf/arena_promote_linear.pr");
const PERF_ARENA_PROMOTE_SHARED: &str = include_str!("../cases/perf/arena_promote_shared.pr");
const PERF_ARENA_PROMOTE_ORDINARY: &str = include_str!("../cases/perf/arena_promote_ordinary.pr");

// Growing the list built under one `with_arena` activation must not grow the
// runtime allocation count at all. Every `Cons` comes from the region; only the
// scalar sum escapes.
#[test]
fn arena_region_fill_allocates_zero_cells_per_element() {
    require_cc();
    let (small, big) = (500_i64, 5_000_i64);
    let lo = stat_src_o2(
        &perf_src_n(PERF_ARENA_REGION_FILL, small),
        "arena_region_fill_lo",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let hi = stat_src_o2(
        &perf_src_n(PERF_ARENA_REGION_FILL, big),
        "arena_region_fill_hi",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let per = (hi - lo) / (big - small);
    assert_eq!(
        per, 0,
        "arena fill allocates {per} cells/element through prism_alloc ({lo} at n={small}, {hi} \
         at n={big}); constructors under `with_arena` regressed off the region path"
    );
}

// Region activations in a loop: the 65 per-iteration constructor cells come
// from the region, leaving exactly the two loop-invariant evidence closures of
// the handler activation itself. Ratcheted so the region path cannot silently
// regress to per-cell malloc (a fallback reads ~66 here). The two remaining
// allocations are captureless evidence closures; hoisting them would reduce the
// baseline to zero.
#[test]
fn arena_region_loop_allocates_only_activation_constants() {
    require_cc();
    let (small, big) = (50_i64, 500_i64);
    let lo = stat_src_o2(
        &perf_src_n(PERF_ARENA_REGION_LOOP, small),
        "arena_region_loop_lo",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let hi = stat_src_o2(
        &perf_src_n(PERF_ARENA_REGION_LOOP, big),
        "arena_region_loop_hi",
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let per = (hi - lo) / (big - small);
    assert!(
        per <= 2,
        "arena activation loop allocates {per} cells/iteration through prism_alloc ({lo} at \
         n={small}, {hi} at n={big}; baseline 2, the activation's evidence closures); the \
         region path regressed"
    );
}

// ---------------------------------------------------------------------------
// The promotion oracle. Escaping a `with_arena` scope deep-copies every
// arena-owned cell the result reaches, and what that costs is invisible to every
// other gate in the tree: output parity, the leak balance, and the region
// ratchets above all stay green whether the walk copies a shared sub-DAG once or
// once per path that reaches it, because both produce the identical value and
// neither leaks. `PRISM_PROMOTE_STATS` reports the walk's own size and shape, and
// the three fixtures below pin it at nothing escaping, at an unshared spine, and
// at a shared DAG where the two behaviors differ exponentially.
//
// The counters are exact counts, not timings, which is what lets these read as
// equalities against a stated baseline rather than as thresholds. A timing gate
// would owe a distribution over repeated samples to be worth anything, because a
// single favorable run proves nothing; a count of cells copied is the same
// integer on every run of a deterministic program, so one sample is the whole
// distribution and a regression cannot hide in variance.
//
// These are anti-vacuous by construction: with the promotion walk's forwarding
// disabled, `arena_promotion_copies_a_shared_cell_once` reads roughly 2^N rather
// than N (measured 4.3 GB and 4.18 s at depth 26 against 1.4 MB and 0.00 s),
// `arena_promotion_of_an_unshared_list_is_one_copy_per_cell` is unaffected
// because that fixture has no sharing to lose, and
// `arena_promotion_does_nothing_when_nothing_escapes` is unaffected because the
// walk never runs. So the shared fixture is the one carrying the claim and it
// has been shown to fail without the behavior it asserts.

const PROMOTE_STATS: &str = "PRISM_PROMOTE_STATS";

// The four counters from one promotion-instrumented run.
struct PromoteStats {
    copied: i64,
    shared: i64,
    nodes: i64,
    edges: i64,
}

impl PromoteStats {
    // Ordered as the fields above; the runtime prints one `prism: <n> <suffix>`
    // line per counter.
    const SUFFIXES: [&'static str; 4] = [
        "cells promoted",
        "promotion copies shared",
        "promotion nodes visited",
        "promotion edges visited",
    ];

    fn measure(template: &str, tag: &str, n: i64) -> Self {
        let v = stat_build_many(
            &perf_src_n(template, n),
            tag,
            PROMOTE_STATS,
            &Self::SUFFIXES,
            |src, bin| {
                let mut cfg = prism::Config::from_env();
                cfg.update_flags(|flags| flags.opt_level = prism::OptLevel::O2);
                prism::build_on(src, &prism::default_roots(Path::new(".")), bin, &cfg)
            },
        )
        .unwrap_or_else(|e| panic!("{e}"));
        Self {
            copied: v[0],
            shared: v[1],
            nodes: v[2],
            edges: v[3],
        }
    }
}

// Nothing reachable from the result is arena-owned, so the walk never runs. A
// promotion that fires here is deep-copying a region the scope was entitled to
// drop wholesale.
#[test]
fn arena_promotion_does_nothing_when_nothing_escapes() {
    require_cc();
    let n = 500;
    let s = PromoteStats::measure(PERF_ARENA_PROMOTE_NONE, "arena_promote_none", n);
    assert_eq!(
        (s.copied, s.shared, s.nodes, s.edges),
        (0, 0, 0, 0),
        "a scope returning a scalar promoted {} cells over {} nodes and {} edges ({} shared) \
         with a {n}-element region; nothing reachable from the result is arena-owned, so the \
         promotion walk should not have run at all",
        s.copied,
        s.nodes,
        s.edges,
        s.shared
    );
}

// An unshared spine: every cell is reached by exactly one path, so each of the
// three walk measures is one per element and no edge ever finds an existing copy
// to reuse. This is what promotion costs with no sharing to preserve, and it is
// what the shared case is compared against.
#[test]
fn arena_promotion_of_an_unshared_list_is_one_copy_per_cell() {
    let (small, big) = (500_i64, 5_000_i64);
    require_cc();
    let lo = PromoteStats::measure(PERF_ARENA_PROMOTE_LINEAR, "arena_promote_linear_lo", small);
    let hi = PromoteStats::measure(PERF_ARENA_PROMOTE_LINEAR, "arena_promote_linear_hi", big);
    let span = big - small;
    let (copied, nodes, edges) = (
        (hi.copied - lo.copied) / span,
        (hi.nodes - lo.nodes) / span,
        (hi.edges - lo.edges) / span,
    );
    assert_eq!(
        (copied, nodes, hi.shared),
        (1, 1, 0),
        "promoting an unshared {big}-element list copied {copied} cells and entered {nodes} \
         nodes per element with {} shared reuses (baseline 1, 1, and 0: one copy and one visit \
         per cell, and nothing to share); {edges} edges/element",
        hi.shared
    );
    assert!(
        edges <= 2,
        "promoting an unshared list examined {edges} edges/element ({} at n={small}, {} at \
         n={big}); a `Cons` has two fields, so the walk is revisiting cells",
        lo.edges,
        hi.edges
    );
}

// A shared DAG: each level's two fields point at the same child, so N region
// cells span 2^N root-to-leaf paths. Copying once per cell costs N and copying
// once per path costs 2^N, and the two produce the identical value, so the
// counters are the only thing that can tell them apart. `shared` rising with
// depth is the positive evidence: it counts edges that reused an existing copy,
// which is region sharing surviving into the promoted result.
#[test]
fn arena_promotion_copies_a_shared_cell_once() {
    require_cc();
    let (small, big) = (12_i64, 22_i64);
    let lo = PromoteStats::measure(PERF_ARENA_PROMOTE_SHARED, "arena_promote_shared_lo", small);
    let hi = PromoteStats::measure(PERF_ARENA_PROMOTE_SHARED, "arena_promote_shared_hi", big);
    let span = big - small;
    let (copied, nodes, shared) = (
        (hi.copied - lo.copied) / span,
        (hi.nodes - lo.nodes) / span,
        (hi.shared - lo.shared) / span,
    );
    assert!(
        copied <= 2 && nodes <= 2,
        "promoting a shared DAG out of `with_arena` copied {copied} cells and entered {nodes} \
         nodes per sharing level ({} and {} at depth {small}, {} and {} at depth {big}; \
         baseline 1 each, the single new cell each level adds); the promotion walk is \
         descending into a shared sub-DAG once per path reaching it rather than once per cell",
        lo.copied,
        lo.nodes,
        hi.copied,
        hi.nodes
    );
    assert_eq!(
        shared, 1,
        "promoting a shared DAG reused an existing copy on {shared} edges per sharing level \
         ({} at depth {small}, {} at depth {big}; baseline 1, the second field of each level \
         pointing at the child the first field already promoted); region sharing is not \
         surviving promotion",
        lo.shared, hi.shared
    );
}

// Promotion must visit a shared ordinary spine once per cell, not once per path.
// The visit counters distinguish the linear and exponential traversals.
#[test]
fn arena_promotion_descends_a_shared_ordinary_spine_once() {
    require_cc();
    let (small, big) = (12_i64, 22_i64);
    let lo = PromoteStats::measure(
        PERF_ARENA_PROMOTE_ORDINARY,
        "arena_promote_ordinary_lo",
        small,
    );
    let hi = PromoteStats::measure(
        PERF_ARENA_PROMOTE_ORDINARY,
        "arena_promote_ordinary_hi",
        big,
    );
    let span = big - small;
    let (nodes, edges) = ((hi.nodes - lo.nodes) / span, (hi.edges - lo.edges) / span);
    assert!(
        nodes <= 2 && edges <= 4,
        "promoting a `Wrap` over a shared ordinary spine entered {nodes} nodes and examined \
         {edges} edges per spine level ({} and {} at depth {small}, {} and {} at depth {big}); \
         the descent is re-walking the shared spine once per path reaching it rather than once \
         per cell",
        lo.nodes,
        lo.edges,
        hi.nodes,
        hi.edges
    );
    assert_eq!(
        (hi.copied, hi.shared),
        (1, 0),
        "promoting the ordinary spine copied {} cells and reused {} shared edges (expected the \
         lone arena `Wrap` copied once, nothing shared: the spine is ordinary, so no region cell \
         is duplicated or reused)",
        hi.copied,
        hi.shared
    );
}

// ---------------------------------------------------------------------------
// Wire/Bytes allocation ratchets. The serialization codec threads one growable
// buffer through a linear builder fold (`buf_push`/`buf_append`) instead of a
// right-nested `wire_cat` (a fresh buffer per element), and decode advances a read
// cursor instead of re-slicing. A revert to either turns a pass quadratic (bytes
// copied) or grows its per-element cell count, both silent to parity. These check the
// -O2 behavior: the incremental byte builder extends in place, the hex
// codec is flat, and Wire encode/decode stay linear, never quadratic.

// Cells the program allocates at -O2 for input size `n`, or a panic naming the
// build/run failure. The shared measurement for the ratchets below.
fn alloc_cells_o2(template: &str, tag: &str, n: i64) -> i64 {
    stat_src_o2(
        &perf_src_n(template, n),
        tag,
        "PRISM_ALLOC_STATS",
        "cells allocated",
    )
    .unwrap_or_else(|e| panic!("{e}"))
}

// A linear pass over 4x the input allocates ~4x the cells (measured ~4.05x); a
// quadratic one (a re-scan of the accumulated body, or a per-byte re-slice on
// decode) allocates ~16x. This bound sits between, so a linear pass passes with the
// constant-factor slack the generic codec carries while a quadratic blowup fails.
const LINEAR_ALLOC_RATIO_BOUND: i64 = 6;

// Encoding a list of derived records to `Bytes` is a linear pass: the derived
// per-field encoder and the container fold both accumulate into one growable buffer
// through `buf_append`, so cell count grows in proportion to the element count. The
// ratio bound fails a quadratic regression (a right-nested container concatenation
// that re-copies the accumulated body per element).
#[test]
fn wire_encode_allocation_is_linear() {
    require_cc();
    let (small, big) = (1000_i64, 4000_i64);
    let (lo, hi) = (
        alloc_cells_o2(PERF_WIRE_ENCODE, "wire encode", small),
        alloc_cells_o2(PERF_WIRE_ENCODE, "wire encode", big),
    );
    assert!(
        lo > 0 && hi < LINEAR_ALLOC_RATIO_BOUND * lo,
        r"wire encode allocation is super-linear: {lo} cells at n={small}, {hi} at n={big} (>= {LINEAR_ALLOC_RATIO_BOUND}x growth for 4x input); the buffer-builder fold regressed to a quadratic encode"
    );
}

// Decoding the same container is a linear pass: `wire_uncons` advances the read
// cursor with an O(1) offset bump and no slice, so materializing the result grows
// with the element count. A regression to slicing the remaining bytes per peel is
// quadratic; the ratio bound catches it.
#[test]
fn wire_decode_allocation_is_linear() {
    require_cc();
    let (small, big) = (1000_i64, 4000_i64);
    let (lo, hi) = (
        alloc_cells_o2(PERF_WIRE_DECODE, "wire decode", small),
        alloc_cells_o2(PERF_WIRE_DECODE, "wire decode", big),
    );
    assert!(
        lo > 0 && hi < LINEAR_ALLOC_RATIO_BOUND * lo,
        r"wire decode allocation is super-linear: {lo} cells at n={small}, {hi} at n={big} (>= {LINEAR_ALLOC_RATIO_BOUND}x growth for 4x input); the cursor decode regressed to a per-byte re-slice"
    );
}

// Threading one uniquely-owned `Bytes` through `bytes_push` extends the underlying
// buffer in place (FBIP), the amortized-doubling growth allocating O(log n)
// buffers; the only per-element allocation is the `Bytes(buf, off)` wrapper the
// push returns, a flat slope of one cell per element. A copy-on-shared regression
// (the buffer losing unique ownership and being copied every push) adds a second
// cell per element and this slope doubles.
#[test]
fn bytes_push_builder_extends_in_place() {
    require_cc();
    let (small, big) = (1000_i64, 10_000_i64);
    let (lo, hi) = (
        alloc_cells_o2(PERF_BUF_CHUNKS, "buf chunks", small),
        alloc_cells_o2(PERF_BUF_CHUNKS, "buf chunks", big),
    );
    // At most the one wrapper cell per element; a small constant slack absorbs the
    // handful of buffer doublings.
    assert!(
        hi <= lo + (big - small) + 64,
        r"bytes_push allocated ~{} cells per element ({lo} at n={small}, {hi} at n={big}); more than the one wrapper cell means the buffer is copied per push and FBIP reuse broke",
        (hi - lo) / (big - small)
    );
}

// Hex encode then decode over a single-allocation input (`buf_new`) is flat: both
// directions accumulate into one buffer builder and emit their result in a single
// `string_of_buf`/`bytes_of_buf`, so allocation is independent of length. A revert
// to per-character string concatenation would allocate one cell per element.
#[test]
fn bytes_codec_allocation_is_flat() {
    require_cc();
    let (small, big) = (1000_i64, 10_000_i64);
    let (lo, hi) = (
        alloc_cells_o2(PERF_BYTES_CODEC, "bytes codec", small),
        alloc_cells_o2(PERF_BYTES_CODEC, "bytes codec", big),
    );
    // Flat: allocation does not grow with length. A small constant slack absorbs
    // the codec's few buffer doublings.
    assert!(
        hi <= lo + 64,
        r"hex codec allocation scales with length: {lo} cells at n={small}, {hi} at n={big}; the builder regressed to per-character concatenation"
    );
}

// Bytes the program allocates at -O2 for input size `n`. Cells and bytes are not
// the same measurement: a string holds its payload inline, so a copy and a window
// onto someone else's bytes are both exactly one cell, and only the byte total
// separates them.
fn alloc_bytes_o2(template: &str, tag: &str, n: i64) -> i64 {
    stat_src_o2(
        &perf_src_n(template, n),
        tag,
        ALLOC_STATS,
        ALLOCATED_BYTES_SUFFIX,
    )
    .unwrap_or_else(|e| panic!("{e}"))
}

// Slicing a string is a window onto it, not a copy: the result holds a reference
// to the parent and reads through it, so a slice costs the same on three bytes as
// on three megabytes. The probe takes 200 long windows onto one N-byte string, so
// a copying slice would materialize the sum of their lengths (the number the probe
// prints, ~1.8 MB at n=10000 against ~180 KB at n=1000) while a window pays one
// small cell each. What remains proportional to N either way is the parent's own
// construction, one buffer plus one string, so the byte total may grow by a small
// multiple of the size increase and no more.
#[test]
fn string_slice_is_a_window_not_a_copy() {
    require_cc();
    let (small, big) = (1000_i64, 10_000_i64);
    let (lo, hi) = (
        alloc_bytes_o2(PERF_STR_SLICE_WINDOW, "str slice window", small),
        alloc_bytes_o2(PERF_STR_SLICE_WINDOW, "str slice window", big),
    );
    let grew = hi - lo;
    let scale = big - small;
    // Anti-vacuous: the parent is materialized once, so the input really did scale
    // with N and a probe that stopped building a large string would fail here
    // rather than pass the ceiling for free.
    assert!(
        grew >= scale,
        r"the window probe stopped scaling with its input ({lo} bytes at n={small}, {hi} at n={big}); its parent string is no longer proportional to N and the ceiling below would pass vacuously"
    );
    // The parent costs a buffer and a string, so three times the size increase is
    // room to spare for the aliasing path and far under the ~200x a copy pays.
    assert!(
        grew <= 3 * scale + 4096,
        r"string slicing allocates with the parent's size ({lo} bytes at n={small}, {hi} at n={big}, growth {grew} for a {scale}-byte larger parent); the slice copies its window instead of aliasing it"
    );
}

// Escaping a string is one pass over it, not one rebuild per escape. The probe
// encodes a string whose every other byte is a quote, so both the escape count
// and the output length scale with N; appending each clean run and each escape
// into one growable buffer keeps the byte total proportional to N, while an
// accumulator that rebuilds the escaped output at every escape pays the escape
// count times the length escaped so far and grows with N squared. The ceiling
// sits an order of magnitude under that square and well above the linear cost,
// so it separates the two shapes rather than pinning a constant.
#[test]
fn json_escaping_appends_runs_instead_of_rebuilding() {
    require_cc();
    let (small, big) = (200_i64, 2000_i64);
    let (lo, hi) = (
        alloc_bytes_o2(PERF_JSON_ESCAPE_RUNS, "json escape runs", small),
        alloc_bytes_o2(PERF_JSON_ESCAPE_RUNS, "json escape runs", big),
    );
    let grew = hi - lo;
    let scale = big - small;
    // Anti-vacuous: the encoded output really is proportional to N, so a probe
    // that stopped scaling would fail here instead of passing the ceiling for
    // free.
    assert!(
        grew >= scale,
        r"the escape probe stopped scaling with its input ({lo} bytes at n={small}, {hi} at n={big}); its output is no longer proportional to N and the ceiling below would pass vacuously"
    );
    assert!(
        grew <= 150 * scale,
        r"escape-heavy encoding allocates with the square of its input ({lo} bytes at n={small}, {hi} at n={big}, growth {grew} for {scale} more escapes); the escaper rebuilds the output per escape instead of appending runs to one buffer"
    );
}

// Decoding a byte payload accumulates into one buffer that is extended in place,
// not rebuilt per byte. A builder is extended in place only while it is uniquely
// owned, and an accumulator threaded through a failure row is shared at every
// step, so the same loop written inside the row copies the whole accumulation on
// each push and costs the square of N. Nothing about the program's output reveals
// which shape ran, so only the allocation slope catches the regression: the
// ceiling sits several times over the linear cost and an order of magnitude under
// the square.
#[test]
fn byte_payload_decoding_extends_one_buffer_in_place() {
    require_cc();
    let (small, big) = (1000_i64, 8000_i64);
    let (lo, hi) = (
        alloc_bytes_o2(PERF_BYTES_BODY_DECODE, "bytes body decode", small),
        alloc_bytes_o2(PERF_BYTES_BODY_DECODE, "bytes body decode", big),
    );
    let grew = hi - lo;
    let scale = big - small;
    // Anti-vacuous: the decoded payload really is proportional to N, so a probe
    // that stopped scaling would fail here instead of passing the ceiling for
    // free.
    assert!(
        grew >= scale,
        r"the byte-payload probe stopped scaling with its input ({lo} bytes at n={small}, {hi} at n={big}); its payload is no longer proportional to N and the ceiling below would pass vacuously"
    );
    assert!(
        grew <= 1200 * scale,
        r"decoding a byte payload allocates with the square of its length ({lo} bytes at n={small}, {hi} at n={big}, growth {grew} for {scale} more bytes); the reader threads its accumulator through the failure row, so every push copies what it has decoded so far"
    );
}

// The container codec's builder fold, checked statically in the elaborated Core.
// A program that encodes a list must reach `buf_append`, the linear accumulation
// primitive the element fold threads through; its presence proves the container
// encoder builds into one growable buffer rather than nesting immutable `wire_cat`
// concatenations. The runtime slope guards above measure the consequence. This checks
// the mechanism and needs no native build. (A right-nested revert is linear in
// cell count too, since each buffer is a single cell, so the slope guards alone
// only this static check catches it.)
#[test]
fn container_encoder_threads_the_builder_fold() {
    let src = perf_src_n(PERF_WIRE_ENCODE, 8);
    let core = prism::dump("core", &src).expect("wire encode compiles");
    assert!(
        core.contains("buf_append"),
        r"the derived list encoder does not reach `buf_append` in Core; the container fold regressed from the linear buffer builder to right-nested `wire_cat` concatenation"
    );
}

#[test]
fn each_update_reuses_uniquely_owned() {
    require_cc();
    // A uniquely-owned list updated through an `each` path must reuse cells in
    // place: `fmap` reuses the spine and the per-element rebuild reuses each
    // record, exactly as the hand-written `fmap(\c -> { c | v = .. }, xs)` would.
    // A path that lowered to anything fresher than that would show zero reuse.
    let hits = stat_src(
        &prism::with_prelude(PERF_EACH_UPDATE_REUSE),
        "each_reuse",
        "PRISM_REUSE_STATS",
        "cells reused",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        hits > 0,
        "a uniquely-owned `each` update reused no cells (hits=0); the path lowering broke FBIP reuse"
    );
}

const PERF_BORROWED_WALK: &str = include_str!("../cases/perf/borrowed_walk.pr");
// The probe walks a 1000-cell list 20 times; without borrowing that is one
// retain per level per pass, so half of it is a generous floor.
const BORROWED_WALK_PAIR_FLOOR: i64 = 10_000;
// Cell traffic the borrowed build may still carry: the list teardown plus
// whatever the prelude print path touches.
const BORROWED_WALK_CELL_SLACK: i64 = 8;

// Borrow inference must remove reference-count pairs, not relocate them: a
// read-only walk over a shared list threads no retains and no releases on
// cells beyond the structure's own teardown. The inference-off build keeps the
// ceiling honest: the identical program pays a pair per level per pass without
// borrowing, so a probe that stops exercising RC pressure fails the floor
// instead of passing the ceiling vacuously. Both builds pin the flag
// explicitly, so the assertion is independent of the configured default.
#[test]
fn borrowed_walk_threads_no_rc_pairs() {
    require_cc();
    let full = prism::with_prelude(PERF_BORROWED_WALK);
    let suffixes = &["rc increments on cells", "rc decrements on cells"];
    let build = |infer: bool| {
        move |src: &str, bin: &Path| {
            let mut cfg = prism::Config::from_env();
            cfg.update_flags(|flags| flags.borrow_infer = infer);
            prism::build_on(src, &prism::default_roots(Path::new(".")), bin, &cfg)
        }
    };
    let on = stat_build_many(
        &full,
        "borrowed_walk_on",
        "PRISM_RC_STATS",
        suffixes,
        build(true),
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let off = stat_build_many(
        &full,
        "borrowed_walk_off",
        "PRISM_RC_STATS",
        suffixes,
        build(false),
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        off[0] >= BORROWED_WALK_PAIR_FLOOR,
        "the walk probe lost its RC pressure ({} cell retains without borrow inference, floor {BORROWED_WALK_PAIR_FLOOR}); the borrowed ceiling would pass vacuously",
        off[0]
    );
    assert!(
        on[0] <= BORROWED_WALK_CELL_SLACK && on[1] <= BORROWED_WALK_CELL_SLACK,
        "a borrowed read-only walk still threads cell RC traffic ({} retains, {} releases, bound {BORROWED_WALK_CELL_SLACK}); borrowing is relocating pairs instead of removing them",
        on[0],
        on[1]
    );
}

#[test]
fn fbip_reuse_fires_at_runtime() {
    require_cc();
    let hits = stat(
        "examples/records_demo.pr",
        "PRISM_REUSE_STATS",
        "cells reused",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        hits > 0,
        "drop-guided in-place reuse did not fire on records_demo.pr (hits=0); the reuse pass regressed"
    );
}

// Build `full` and run it under a constrained native stack (`stack_kb`). Returns
// Ok only if it exits successfully; a constant-stack program passes a tight
// limit, an O(n)-stack one (a loop reified into the free monad, whose resumption
// is not a tail call) overflows and is killed by the OS (SIGSEGV).
fn runs_in_bounded_stack(full: &str, tag: &str, stack_kb: u32) -> Result<(), String> {
    let bin = env::temp_dir().join(format!(
        "prism_scale_{}_{}",
        std::process::id(),
        tag.replace([' ', '/', '.'], "_")
    ));
    let cleanup = || {
        for ext in ["bc", "ll"] {
            let _ = fs::remove_file(bin.with_extension(ext));
        }
        let _ = fs::remove_file(&bin);
    };
    if let Err(e) = prism::build(full, &bin) {
        cleanup();
        return Err(format!("{tag}: build failed: {e}"));
    }
    // `ulimit -s` bounds the stack for the child only; a constant-stack loop is
    // unaffected, an O(n) one cannot finish.
    let out = Command::new("sh")
        .arg("-c")
        .arg(format!("ulimit -s {stack_kb}; exec {}", bin.display()))
        .output();
    cleanup();
    let out = out.map_err(|e| format!("{tag}: spawn failed: {e}"))?;
    if out.status.success() {
        Ok(())
    } else {
        Err(format!(
            r"{tag}: did not complete in a {stack_kb}KB stack (status {:?}); it grows the native stack per iteration instead of running as a constant-stack loop",
            out.status.code()
        ))
    }
}

// Scale + bounded-stack gate. A loop must run in CONSTANT native stack, so it
// completes a million iterations under a tight stack limit. This catches the
// stack-overflow cliff (an O(n)-deep non-tail recursion) that a small-input test
// never reaches: the blind spot that let `var` loops ship overflowing at ~50k.
// The pure tail-recursion case is the harness's own sanity check (it already
// loops via `musttail`); the `var` loops must now too, via mutable-cell erasure.
#[test]
fn loops_run_in_constant_stack() {
    require_cc();
    let n = 1_000_000;
    let cases: &[(&str, &str)] = &[
        ("pure tail recursion", PERF_STACK_TAIL_RECURSION),
        ("var while-loop", PERF_STACK_VAR_WHILE),
        ("var for-loop", PERF_STACK_VAR_FOR),
    ];
    let mut fails = Vec::new();
    for (name, template) in cases {
        if let Err(e) = runs_in_bounded_stack(&perf_src_n(template, n), name, 2048) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// Imperative loops using `break`/`continue`/early `return`. Their loop control
// used to reify into the free monad, whose resumption is a first-class closure
// apply (not a tail call), so the native stack grew O(n) and they overflowed at
// scale. `erase_control` now rewrites them to direct control flow (a `ctl:Int`
// thread plus, for `break`/`return`, a `musttail` driver), so they run in constant
// stack like any `var` loop. A million iterations under a 2048KB stack proves it.
#[test]
fn free_monad_loops_run_in_constant_stack() {
    require_cc();
    let n = 1_000_000;
    let cases: &[(&str, &str)] = &[
        ("continue-heavy while loop", PERF_STACK_CONTINUE_WHILE),
        ("break while loop", PERF_STACK_BREAK_WHILE),
        ("early-return loop", PERF_STACK_EARLY_RETURN),
    ];
    let mut fails = Vec::new();
    for (name, template) in cases {
        if let Err(e) = runs_in_bounded_stack(&perf_src_n(template, n), name, 2048) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// A hand-rolled parameter-passing `State` loop: a `get`-style `rd` clause
// (`r(s)(s)`) and a `put`-style `wr` clause (`r(())(v)`) over one accumulator,
// with the answer the producer value (`return x => \_s -> x`). State fusion
// recognizes the two-op shape and threads the accumulator through `spin` as an
// explicit loop: zero `EOp` cells and constant stack, the same state-rung
// guarantee as the writer-style fold. Each iteration would otherwise leave a pending-apply
// frame on the native stack and reify a continuation cell.
#[test]
fn param_passing_effect_loop_runs_in_constant_stack() {
    require_cc();
    let n = 1_000_000;
    let full = perf_src_n(PERF_PARAM_PASSING_STATE, n);
    runs_in_bounded_stack(&full, "parameter-passing state loop", 2048)
        .unwrap_or_else(|e| panic!("{e}"));
    // State fusion allocates no `EOp` cells; routing through the `@region` driver
    // would allocate O(n) cells.
    match stat_src(&full, "param-passing state", "PRISM_EFFOP_STATS", "eff ops allocated") {
        Ok(0) => {}
        Ok(c) => panic!("parameter-passing State loop allocated {c} eff-op cell(s); want 0 (state fusion regressed)"),
        Err(e) => panic!("{e}"),
    }
}

// Asymptotic-work gate: the counter that would have caught the EBounce regression.
// A deep non-tail effectful recursion (`deep_abort`: N nested frames each holding a
// live cons cell, an abort at the bottom) is *honestly* O(N) allocation under both
// a linear and a quadratic trampoline, so allocation counts cannot tell them apart
// -- only the driver's actual work-step count does. Run at N and 4N and assert the
// growth ratio is sub-octic: a linear driver does ~4x the steps, a quadratic one
// (the EBounce re-association that re-walks the left-nested spine each bounce) does
// ~16x. The type-aligned dequeue replaced `EOp`'s nested-closure continuation
// with an O(1)-snoc queue, so `ebind` no longer re-walks the spine; this is the
// permanent ratchet that checks that in, and would catch its reintroduction (the
// re-association blowup that made `deep_abort` quadratic and had to be reverted).
#[test]
fn driver_work_is_linear_on_deep_nontail_recursion() {
    require_cc();
    let prog = |n: i64| perf_src_n(PERF_DEEP_ABORT, n);
    let small = 2000_i64;
    let big = 4 * small;
    let steps_small = stat_src(
        &prog(small),
        "drive_small",
        "PRISM_DRIVE_STATS",
        "drive steps",
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let steps_big = stat_src(&prog(big), "drive_big", "PRISM_DRIVE_STATS", "drive steps")
        .unwrap_or_else(|e| panic!("{e}"));
    // Integer ratio test (no float): linear work quadruples (4x), quadratic ~16x.
    assert!(
        steps_small > 0 && steps_big < 8 * steps_small,
        r"driver work is super-linear: {steps_small} steps at n={small}, {steps_big} at n={big}; a >= 8x growth means the trampoline re-associates quadratically (the EBounce regression)"
    );
}

// Concurrency constant-stack gate. A fiber that yields a million times drives the
// cooperative scheduler a million steps: each `yield` reifies a `Cmd`, re-enqueues
// the fiber, and the pure `drive` loop resumes it off the native stack under the
// whole-program trampoline, so the scheduler steps in constant native stack rather
// than growing a frame per yield. Both shipped policies discharge the same `Async`
// effect (FIFO `run_async` enqueues at the back, LIFO `run_lifo` at the front), so
// both must complete a million yields under a 2048KB stack; a per-yield stack frame
// would overflow well before then.
#[test]
fn scheduler_yield_loop_runs_in_constant_stack() {
    require_cc();
    let n = 1_000_000;
    let prog = |run: &str| {
        perf_src(
            PERF_SCHEDULER_YIELD,
            &[
                (N_PLACEHOLDER, n.to_string()),
                (RUN_STRATEGY_PLACEHOLDER, run.to_string()),
            ],
        )
    };
    let mut fails = Vec::new();
    for run in ["run_async", "run_lifo"] {
        if let Err(e) = runs_in_bounded_stack(&prog(run), run, 2048) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// ---------------------------------------------------------------------------
// Join points in match compilation (static Core-size ratchet).
//
// Unlike the runtime ratchets above, this one needs no native build: it checks a
// property of the elaborated Core itself. A guarded match compiles each arm to
// `if guard then body else <fallthrough>` plus a wildcard arm that also routes
// to the fallthrough. Placing the fallthrough in both positions by clone made N
// guarded arms emit 2^N copies of it (verified: the shared default body appeared
// 2, 4, 16, 64 times at N = 1, 2, 4, 6). The join-point lowering binds the
// fallthrough once as a thunk and reaches it with a `Force` from each position,
// so its body is emitted once no matter how many guarded arms precede it, and
// total Core size grows linearly rather than exponentially in N.
//
// Prelude-free (`println` is a builtin, the type is inline) so the check is a
// pure function of the match compiler, independent of stdlib state.
fn guarded_match(n: usize) -> String {
    let mut s = String::from("type T = A | B(Int)\nfn test(p : (T, Int)) : Int =\n  match p of\n");
    for i in 0..n {
        // A refutable head (`B(x)`) on each arm keeps the wildcard fallthrough
        // arm alive through match compilation, which is what triggers the
        // two-position placement the join point shares.
        writeln!(s, "    (B(x), y) if x + y == {i} => {i}").unwrap();
    }
    // A distinctive default whose occurrence count is the fallthrough copy count.
    s.push_str("    _ => 31337\n");
    s.push_str("fn main() : Unit ! {IO} =\n  println(test((B(2), 3)))\n");
    s
}

#[test]
fn guarded_match_fallthrough_is_shared_not_duplicated() {
    // The shared fallthrough body must be emitted a constant number of times,
    // regardless of how many guarded arms precede it: 2^N duplication would grow
    // this without bound.
    let copies = |n: usize| {
        prism::dump("core", &guarded_match(n))
            .expect("guarded match compiles")
            .matches("31337")
            .count()
    };
    let (c4, c16) = (copies(4), copies(16));
    assert!(
        c4 <= 2 && c16 == c4,
        r"guarded-match fallthrough duplicated: {c4} copies at 4 arms, {c16} at 16; the join point must emit the fallthrough body a constant number of times (2^N regression)"
    );

    // Total Core size must grow linearly, not exponentially: doubling the guarded
    // arm count roughly doubles the size (the 2^N form quadrupled it every two
    // arms). A 3x bound on a 2x doubling leaves slack while failing the blowup by
    // a wide margin (the pre-join form was ~29x larger at 8 arms than at 4).
    let size = |n: usize| {
        prism::dump("core", &guarded_match(n))
            .expect("guarded match compiles")
            .len()
    };
    let (s8, s16) = (size(8), size(16));
    assert!(
        s16 < 3 * s8,
        r"guarded-match Core size is super-linear: {s8} bytes at 8 arms, {s16} at 16 (a 2x arm count must stay well under the 3x bound); the fallthrough is being duplicated"
    );
}

// ---------------------------------------------------------------------------
// The tier-hit manifest (committed golden of per-program lowering tier).
//
// `tier_parity.rs` proves the cascade is observationally invisible and the
// ratchets above spot-check bespoke sources, but nothing asserts a real corpus
// program still HITS its intended tier: an elaborator refactor could defeat every
// effect-lowering fast path corpus-wide, keep byte-identical output, and pass all
// those gates as an invisible performance collapse. This manifest is the cheapest
// enforcement of the north star (the cascade stays a pure cost decision only if
// someone is watching the cost): it records the lowering tier of every corpus
// program as a committed golden and fails when one regresses onto a slower tier.
//
// The tier is the whole-program strategy the typed cascade computes, surfaced
// through `prism::effect_strategy_full` (and the `dump tier` phase). A regression
// (a move to a costlier tier in `EFFECT_TIERS` order) fails loudly and names the
// functions that lost fusion; an improvement or a corpus change also fails, with
// instructions to regenerate. Regenerate with `just tier-accept` (or
// `PRISM_ACCEPT_TIER_MANIFEST=1`), reviewing the diff exactly like a snapshot.

const TIER_MANIFEST: &str = "tests/tier_manifest.txt";
const TIER_MANIFEST_ACCEPT: &str = "PRISM_ACCEPT_TIER_MANIFEST";
const TIER_MANIFEST_HEADER: &str = r"# Effect-lowering tier manifest. One `<program>\t<tier>` line per corpus
# program, sorted. The golden pinned by tests/perf_gate.rs::tier_manifest_holds.
# A tier moving to a costlier one (see prism::EFFECT_TIERS order) is a silent
# performance regression and fails CI; regenerate after a reviewed improvement
# with `just tier-accept`. Do not hand-edit.
";

// The manifest catches per-program regressions; this separate ratchet bounds the
// total population on the costliest tier and is reseated downward only.
const TIER_RATCHET: &str = "tests/tier_ratchet.txt";
const TIER_RATCHET_HEADER: &str = r"# Aggregate decline ratchet: `<costliest-tier>\t<count>`. The number of corpus
# programs the cascade floors at the slowest rung. tier_manifest.txt fails one
# program sliding slower; this fails the sum growing. Pinned by
# tests/perf_gate.rs::tier_manifest_holds. `just tier-accept` reseats it DOWNWARD
# only: a fast-path win shrinks it, but a program joining the slowest rung is
# refused there and must be a reviewed hand-edit. Do not raise it to pass a gate.
";

// The corpus as `(dir/name.pr label, tier)` rows, sorted by label. The label is
// the path relative to the crate root, matching the parity oracles' program names.
fn corpus_tiers() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut rows: Vec<(String, String)> = crate::support::corpus()
        .into_iter()
        .map(|path| {
            let label = crate::support::label_of(&path);
            let tier = prism::effect_strategy_full(&crate::support::source(&path), root)
                .unwrap_or_else(|e| panic!("{label}: tier classification failed: {e}"));
            (label, tier.to_string())
        })
        .collect();
    rows.sort();
    rows
}

fn render_manifest(rows: &[(String, String)]) -> String {
    let mut s = String::from(TIER_MANIFEST_HEADER);
    for (label, tier) in rows {
        s.push_str(label);
        s.push('\t');
        s.push_str(tier);
        s.push('\n');
    }
    s
}

fn parse_manifest(text: &str) -> BTreeMap<String, String> {
    text.lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let (label, tier) = l
                .split_once('\t')
                .expect("tier manifest line is `label<TAB>tier`");
            (label.to_string(), tier.to_string())
        })
        .collect()
}

// The costliest tier's label, read from the one cost order so the ratchet cannot
// drift from the ladder's own vocabulary (the same source the `rank` closure and
// the manifest generator use).
const fn costliest_tier() -> &'static str {
    prism::EFFECT_TIERS
        .last()
        .expect("the effect-tier cost order is non-empty")
        .label()
}

// The labels of the corpus rows floored at the costliest tier.
fn costliest_programs(rows: &[(String, String)]) -> BTreeSet<&str> {
    let costliest = costliest_tier();
    rows.iter()
        .filter(|(_, tier)| tier == costliest)
        .map(|(label, _)| label.as_str())
        .collect()
}

// The committed baseline count, or `None` when the file is absent or unseeded.
// Keyed by the costliest-tier label so a ladder rename fails closed (the line
// stops matching) rather than silently comparing against a stale tier's count.
fn read_ratchet(path: &Path) -> Option<usize> {
    let text = fs::read_to_string(path).ok()?;
    let costliest = costliest_tier();
    text.lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .find_map(|l| {
            let (label, count) = l.split_once('\t')?;
            (label == costliest).then(|| count.trim().parse().ok())?
        })
}

fn render_ratchet(count: usize) -> String {
    format!("{TIER_RATCHET_HEADER}{}\t{count}\n", costliest_tier())
}

// Programs floored at the costliest tier now that were not in the prior manifest
// (an absent prior means every one is new). Names the arrivals when the accept
// path refuses to raise the ratchet, so the failure points at the exact programs
// that joined the slowest rung.
fn newly_costliest(
    current: &[(String, String)],
    prior: Option<&BTreeMap<String, String>>,
) -> Vec<String> {
    let costliest = costliest_tier();
    let was_slow =
        |label: &str| prior.is_some_and(|m| m.get(label).is_some_and(|tier| tier == costliest));
    current
        .iter()
        .filter(|(label, tier)| tier == costliest && !was_slow(label))
        .map(|(label, _)| label.clone())
        .collect()
}

// Refuse to regenerate from a corpus that lost programs to a broken tree.
//
// `support::corpus` keeps only programs that interpret successfully, so a tree
// that does not compile yields a short corpus (an empty one, at the limit) rather than
// an error. Writing that out would truncate the golden and report success, and
// the gate would then pass forever against the survivors. Regenerating is exactly
// when the tree is most likely to be mid-change, so the accept path is the one
// that has to be suspicious.
//
// Corpus membership has two conditions, so leaving it has two innocent
// explanations and one guilty one. A file that is gone was deleted on purpose. A
// file still on disk that now reaches a host builtin left because it went
// off-platform, which is a deliberate change to what the program is. Anything
// else still on disk stopped interpreting, and dropping it would disarm the gate
// for it. The classification below fails closed: a source the analysis cannot
// even read counts as broken.
fn went_off_platform(root: &Path, path: &Path) -> bool {
    prism::off_platform_builtins(
        &crate::support::source(path),
        &prism::resolve::default_roots(root),
    )
    .is_ok_and(|ops| !ops.is_empty())
}

fn guard_accept(
    root: &Path,
    current: &[(String, String)],
    prior: Option<&BTreeMap<String, String>>,
) {
    assert!(
        !current.is_empty(),
        "refusing to regenerate {TIER_MANIFEST} from an empty corpus: every program failed to \
         compile, which truncates the golden and disarms the gate. Fix the tree, then rerun."
    );
    let Some(prior) = prior else { return };
    let live: BTreeSet<&str> = current.iter().map(|(l, _)| l.as_str()).collect();
    let broken: Vec<&str> = prior
        .keys()
        .map(String::as_str)
        .filter(|label| {
            let path = root.join(label);
            !live.contains(label) && path.exists() && !went_off_platform(root, &path)
        })
        .collect();
    assert!(
        broken.is_empty(),
        "refusing to regenerate {TIER_MANIFEST}: {} program(s) left the corpus but are still on \
         disk and still on this platform, so they stopped interpreting rather than being deleted \
         or moved off-platform. Dropping them would disarm the gate for each. Fix or delete them, \
         then rerun:\n  {}",
        broken.len(),
        broken.join("\n  ")
    );
}

#[test]
fn tier_manifest_holds() {
    // In release the deep corpus runs on the ordinary libtest worker stack
    // now that traversals are iterative. Debug frames are several times
    // release size and overflow that budget at legal depths, so the debug
    // gate gets the public compiler's 8 MiB main-thread budget instead.
    let mut builder = std::thread::Builder::new().name("tier-manifest".into());
    if cfg!(debug_assertions) {
        builder = builder.stack_size(8 * 1024 * 1024);
    }
    let result = builder
        .spawn(tier_manifest_holds_on_compiler_stack)
        .expect("spawning tier-manifest compiler stack")
        .join();
    if let Err(payload) = result {
        std::panic::resume_unwind(payload);
    }
}

fn tier_manifest_holds_on_compiler_stack() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join(TIER_MANIFEST);
    let current = corpus_tiers();

    // Accept path: rewrite the golden and pass, the loud INSTA_UPDATE-style
    // regen a reviewed tier improvement (or corpus change) takes.
    if env::var_os(TIER_MANIFEST_ACCEPT).is_some() {
        let prior = fs::read_to_string(&path).map(|t| parse_manifest(&t)).ok();
        guard_accept(root, &current, prior.as_ref());

        // Reseat the aggregate ratchet, downward only. A grown slowest-rung
        // population is refused here so the manifest regen cannot silently drag
        // the sum up: raising it must be a reviewed hand-edit of the ratchet
        // file. Refuse before writing either golden so a rejection leaves both
        // committed artifacts untouched and internally consistent.
        let ratchet_path = root.join(TIER_RATCHET);
        let now = costliest_programs(&current);
        if let Some(baseline) = read_ratchet(&ratchet_path) {
            assert!(
                now.len() <= baseline,
                "refusing to reseat {TIER_RATCHET}: the {} population grew {baseline} -> {} \
                 while regenerating {TIER_MANIFEST}. The ratchet reseats downward only. Restore a \
                 faster tier for the program(s) that joined the slowest rung, or, if this is a \
                 reviewed and unavoidable addition, raise {TIER_RATCHET} by hand with \
                 justification first:\n  {}",
                costliest_tier(),
                now.len(),
                newly_costliest(&current, prior.as_ref()).join("\n  ")
            );
        }

        fs::write(&path, render_manifest(&current)).expect("write tier manifest");
        fs::write(&ratchet_path, render_ratchet(now.len())).expect("write tier ratchet");
        eprintln!(
            "tier manifest regenerated: {} programs ({} on {}) -> {}, {}",
            current.len(),
            now.len(),
            costliest_tier(),
            TIER_MANIFEST,
            TIER_RATCHET
        );
        return;
    }

    let golden = parse_manifest(&fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read tier manifest {TIER_MANIFEST} ({e}); regenerate with `just tier-accept`"
        )
    }));

    // Cost rank of a tier: its index in the cheapest-first `EFFECT_TIERS`. A move
    // to a higher rank is the regression this gate exists to catch.
    let rank = |t: &str| prism::EFFECT_TIERS.iter().position(|x| x.label() == t);
    let mut regressions: Vec<String> = Vec::new();
    let mut changes: Vec<String> = Vec::new();

    for (label, tier) in &current {
        match golden.get(label) {
            Some(want) if want == tier => {}
            Some(want) if matches!((rank(want), rank(tier)), (Some(a), Some(b)) if b > a) => {
                // Name the functions that lost fusion so the failure identifies
                // the handler to investigate.
                let culprits =
                    prism::effect_warnings_full(&crate::support::source(&root.join(label)), root)
                        .unwrap_or_default();
                let why = if culprits.is_empty() {
                    String::new()
                } else {
                    format!("\n      lost fusion: {}", culprits.join("; "))
                };
                regressions.push(format!(
                    "  {label}: REGRESSED {want} -> {tier} (costlier tier){why}"
                ));
            }
            Some(want) => changes.push(format!("  {label}: improved {want} -> {tier}")),
            None => changes.push(format!("  {label}: new program at tier {tier}")),
        }
    }
    for label in golden.keys() {
        if !current.iter().any(|(l, _)| l == label) {
            changes.push(format!("  {label}: was in golden, no longer in corpus"));
        }
    }

    assert!(
        regressions.is_empty(),
        r"effect-lowering tier regressed for {} program(s) (a silent performance collapse; investigate the fast-path matcher before regenerating):
{}",
        regressions.len(),
        regressions.join("\n")
    );
    assert!(
        changes.is_empty(),
        r"tier manifest is stale for {} program(s); review these (each is an improvement or a corpus change, not a regression) and regenerate with `just tier-accept`:
{}",
        changes.len(),
        changes.join("\n")
    );

    // The costliest-tier population may not exceed its committed baseline.
    let baseline = read_ratchet(&root.join(TIER_RATCHET)).unwrap_or_else(|| {
        panic!("cannot read the aggregate tier ratchet {TIER_RATCHET}; seat it with `just tier-accept`")
    });
    let now = costliest_programs(&current);
    assert!(
        now.len() <= baseline,
        r"the {} population is {}, over the ratchet baseline {baseline}: the sum on the slowest rung grew even though no single program regressed. Find the fast path that stopped firing, or, for a reviewed change, regenerate with `just tier-accept` (which reseats the ratchet downward only). Programs on {}:
  {}",
        costliest_tier(),
        now.len(),
        costliest_tier(),
        now.into_iter().collect::<Vec<_>>().join("\n  ")
    );
}
