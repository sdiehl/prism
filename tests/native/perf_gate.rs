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

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;
use std::{env, fs};

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

// Like `stat_src`, but at -O2, where stream fusion is default-on. Used by the
// pull-Sequence fusion guard, whose zero-allocation guarantee holds at the shipped
// release level, not at the plain -O1 default.
fn stat_src_o2(full: &str, tag: &str, stat_env: &str, suffix: &str) -> Result<i64, String> {
    stat_build(full, tag, stat_env, suffix, |src, bin| {
        let mut cfg = prism::Config::from_env();
        cfg.opt = prism::OptLevel::O2;
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
    let bin = env::temp_dir().join(format!(
        "prism_perf_{}_{}",
        std::process::id(),
        tag.replace(['/', '.', ' '], "_")
    ));
    let cleanup = || {
        for ext in ["bc", "ll"] {
            let _ = fs::remove_file(bin.with_extension(ext));
        }
        let _ = fs::remove_file(&bin);
    };
    if let Err(e) = build(full, &bin) {
        cleanup();
        return Err(format!("{tag}: build failed: {e}"));
    }
    let out = Command::new(&bin).env(stat_env, "1").output();
    cleanup();
    let out = out.map_err(|e| format!("{tag}: spawn failed: {e}"))?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    let line = stderr
        .lines()
        .find(|l| l.trim_end().ends_with(suffix))
        .ok_or_else(|| format!("{tag}: no `{suffix}` line in stderr: {stderr:?}"))?;
    line.split_whitespace()
        .nth(1)
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| format!("{tag}: cannot parse count from {line:?}"))
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
    "examples/stream_fuse.pr",
    "examples/stream_fold.pr",
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

// THE SEQUENCE FUSION GUARD. Drives the ACTUAL `lib/std/Sequence.pr` module through
// `import Sequence as Seq` (the shipped shape, across the import boundary, which
// is what the acceptance criterion covers) and checks the per-element allocation
// slope of each pipeline at ZERO: the stream-fusion pass (default-on at -O2)
// collapses the whole pipeline into a `%fuse$` join loop and the dead upstream
// combinator chain is eliminated, so a curated pipeline materializes no
// intermediates at all. History for the archaeologist: pre-fusion these rows
// measured a flat 2 cells/element per stage (one SMore cons plus one step thunk,
// no reuse and no inlining across the module boundary: slopes 2/4/6), and two
// inline split-form proxy gates once stood here; they were deleted when the pass
// landed, because they encoded a combinator shape (thin wrapper delegating to a
// named helper) that the shipped library does not use and the recognizer
// deliberately does not chase. A slope regression here means fusion stopped
// firing through the import boundary; that is a release blocker, not a ratchet.
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
        // Stream fusion is default-on at -O2, which is the level this guarantee
        // ships at, so measure there. A plain -O1 build still runs the pipeline
        // unfused; the check is that the shipped release level allocates nothing.
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
// Wire/Bytes allocation ratchets. The serialization codec threads one growable
// buffer through a linear builder fold (`buf_push`/`buf_append`) instead of a
// right-nested `wire_cat` (a fresh buffer per element), and decode advances a read
// cursor instead of re-slicing. A revert to either turns a pass quadratic (bytes
// copied) or grows its per-element cell count, both silent to parity. These check the
// shipped -O2 behavior: the incremental byte builder extends in place, the hex
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

// The container codec's builder fold, checked statically in the elaborated Core.
// A program that encodes a list must reach `buf_append`, the linear accumulation
// primitive the element fold threads through; its presence proves the container
// encoder builds into one growable buffer rather than nesting immutable `wire_cat`
// concatenations. The runtime slope guards above measure the consequence; this checks
// the mechanism, and needs no native build. (A right-nested revert is linear in
// cell count too, since each buffer is a single cell, so the slope guards alone
// cannot see it; this static check is what does.)
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

#[test]
fn fbip_reuse_fires_at_runtime() {
    require_cc();
    let hits = stat("examples/list.pr", "PRISM_REUSE_STATS", "cells reused")
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        hits > 0,
        "drop-guided in-place reuse did not fire on list.pr (hits=0); the reuse pass regressed"
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
// explicit loop: zero `EOp` cells and constant stack, the same tier-1 guarantee
// as the writer-style fold. Each iteration would otherwise leave a pending-apply
// frame on the native stack and reify a continuation cell.
#[test]
fn param_passing_effect_loop_runs_in_constant_stack() {
    require_cc();
    let n = 1_000_000;
    let full = perf_src_n(PERF_PARAM_PASSING_STATE, n);
    runs_in_bounded_stack(&full, "parameter-passing state loop", 2048)
        .unwrap_or_else(|e| panic!("{e}"));
    // Tier-1: the two-op State loop fuses, allocating no `EOp` cells (it ran via
    // the O(n)-cell `@region` driver before get-style fusion landed).
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
// The tier is the whole-program strategy `effect_lower` already computes,
// surfaced through `prism::effect_strategy_full` (and the `dump tier` phase). A
// regression (a move to a costlier tier in `EFFECT_TIERS` order) fails loudly and
// names the functions that lost fusion; an improvement or a corpus change also
// fails, with instructions to regenerate. Regenerate with `just tier-accept` (or
// `PRISM_ACCEPT_TIER_MANIFEST=1`), reviewing the diff exactly like a snapshot.

const TIER_MANIFEST: &str = "tests/tier_manifest.txt";
const TIER_MANIFEST_ACCEPT: &str = "PRISM_ACCEPT_TIER_MANIFEST";
const TIER_MANIFEST_HEADER: &str = r"# Effect-lowering tier manifest. One `<program>\t<tier>` line per corpus
# program, sorted. The golden pinned by tests/perf_gate.rs::tier_manifest_holds.
# A tier moving to a costlier one (see prism::EFFECT_TIERS order) is a silent
# performance regression and fails CI; regenerate after a reviewed improvement
# with `just tier-accept`. Do not hand-edit.
";

// The corpus as `(dir/name.pr label, tier)` rows, sorted by label. The label is
// the path relative to the crate root, matching the parity oracles' program names.
fn corpus_tiers() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut rows: Vec<(String, String)> = crate::support::corpus()
        .into_iter()
        .map(|path| {
            let label = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
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

#[test]
fn tier_manifest_holds() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join(TIER_MANIFEST);
    let current = corpus_tiers();

    // Accept path: rewrite the golden and pass, the loud INSTA_UPDATE-style
    // regen a reviewed tier improvement (or corpus change) takes.
    if env::var_os(TIER_MANIFEST_ACCEPT).is_some() {
        fs::write(&path, render_manifest(&current)).expect("write tier manifest");
        eprintln!(
            "tier manifest regenerated: {} programs -> {}",
            current.len(),
            TIER_MANIFEST
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
                // Name the functions that lost fusion so the failure points at the
                // handler to investigate, not just the program.
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
}
