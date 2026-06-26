// Performance ratchets that `parity.rs` cannot see. A fusion or reuse regression
// produces byte-identical output and zero leaks, so the parity/leak gate stays
// green while the language's headline optimizations silently fall back to the
// slow path. These tests pin the runtime allocation counters instead:
//
//   - evidence passing + stream fusion must allocate ZERO free-monad eff-op
//     cells on the fusion corpus (`PRISM_EFFOP_STATS`), and
//   - drop-guided in-place constructor reuse must actually fire at runtime
//     (`PRISM_REUSE_STATS`), the runtime complement to the static IR check in
//     `snapshots.rs`.
//
// Built once per program through the native backend, so they ride the same
// toolchain as the parity gate and skip cleanly when no C compiler is present.

use std::path::Path;
use std::process::Command;
use std::{env, fs};

fn cc() -> String {
    env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
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
    if let Err(e) = prism::build(full, &bin) {
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
// first-class stream fusion, fold-consumer state threading, and the full stake +
// mixed-mode showcase). Every one must allocate no `EOp` cells.
const FUSION_PROGRAMS: &[&str] = &[
    "tests/cases/run/effop_tax.pr",
    "tests/cases/run/eff_two_handlers.pr",
    "tests/cases/run/eff_fuse.pr",
    "examples/stream_fuse.pr",
    "examples/stream_fold.pr",
    "examples/streams.pr",
];

#[test]
fn effop_fast_path_allocates_nothing() {
    if !have(&cc()) {
        eprintln!(
            "skipping perf gate: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
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
    if !have(&cc()) {
        eprintln!(
            "skipping perf gate: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
    let count = |case| stat(case, "PRISM_EFFOP_STATS", "eff ops allocated");
    let escape = count("tests/cases/run/local_mono_escape.pr").unwrap_or_else(|e| panic!("{e}"));
    let combined =
        count("tests/cases/run/local_mono_combined.pr").unwrap_or_else(|e| panic!("{e}"));
    assert!(
        escape > 0,
        "the escaping Log component must itself allocate eff-op cells (got {escape}); \
         the gate would be vacuous otherwise"
    );
    assert_eq!(
        combined,
        escape,
        "adding a fused stream pipeline allocated {} extra eff-op cell(s); local \
         monadification regressed and the unrelated pipeline left the fused path",
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
    if !have(&cc()) {
        eprintln!(
            "skipping perf gate: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
    // Each program must allocate O(1) eff-op cells regardless of `{N}`.
    let flat: &[(&str, &str)] = &[
        (
            "var while-loop accumulator",
            "fn run(n : Int) : Int =\n  var s := 0\n  var i := 0\n  while i < n do\n    i += 1\n    s += i\n  s\nfn main() = println(run({N}))\n",
        ),
        (
            "var for-loop accumulator",
            "fn run(n : Int) : Int =\n  var t := 0\n  for i in srange(1, n + 1) do\n    t += i\n  t\nfn main() = println(run({N}))\n",
        ),
    ];
    let (small, big) = (1000_i64, 10_000_i64);
    let mut fails = Vec::new();
    for (name, tmpl) in flat {
        let mk = |n: i64| prism::with_prelude(&tmpl.replace("{N}", &n.to_string()));
        let lo = stat_src(&mk(small), name, "PRISM_EFFOP_STATS", "eff ops allocated");
        let hi = stat_src(&mk(big), name, "PRISM_EFFOP_STATS", "eff ops allocated");
        match (lo, hi) {
            (Ok(lo), Ok(hi)) => {
                // Flat means allocation does not grow with n; allow a tiny constant slack.
                if hi > lo + 16 {
                    let per_iter = (hi - lo) / (big - small);
                    fails.push(format!(
                        "{name}: allocation scales with n ({lo} cells at n={small}, {hi} at \
                         n={big}; ~{per_iter} eff-op cells/iteration). The optimization is \
                         not firing: this reifies into the free monad instead of an O(1) loop."
                    ));
                }
            }
            (Err(e), _) | (_, Err(e)) => fails.push(e),
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

#[test]
fn fbip_reuse_fires_at_runtime() {
    if !have(&cc()) {
        eprintln!(
            "skipping perf gate: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
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
            "{tag}: did not complete in a {stack_kb}KB stack (status {:?}); it grows the \
             native stack per iteration instead of running as a constant-stack loop",
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
    if !have(&cc()) {
        eprintln!("skipping perf gate: C compiler `{}` not found (set PRISM_CC)", cc());
        return;
    }
    let n = 1_000_000;
    let cases: &[(&str, String)] = &[
        (
            "pure tail recursion",
            format!(
                "fn go(k : Int, acc : Int) : Int =\n  if k == 0 then acc else go(k - 1, acc + 1)\n\
                 fn main() = println(go({n}, 0))\n"
            ),
        ),
        (
            "var while-loop",
            format!(
                "fn run(k : Int) : Int =\n  var s := 0\n  var i := 0\n  while i < k do\n    \
                 i += 1\n    s += i\n  s\nfn main() = println(run({n}))\n"
            ),
        ),
        (
            "var for-loop",
            format!(
                "fn run(k : Int) : Int =\n  var t := 0\n  for i in srange(1, k + 1) do\n    \
                 t += i\n  t\nfn main() = println(run({n}))\n"
            ),
        ),
    ];
    let mut fails = Vec::new();
    for (name, src) in cases {
        if let Err(e) = runs_in_bounded_stack(&prism::with_prelude(src), name, 2048) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// The companion gate for loops still on the free monad: imperative loops using
// `break`/`continue`/early `return`, and hand-rolled parameter-passing effect
// loops. Their loop control reifies into the free monad, whose resumption is a
// first-class closure apply (not a tail call), so the native stack grows O(n) and
// they overflow at scale. The fix is the free-monad trampoline (run the reified
// computation in a constant-stack driver loop); until it lands these crash at a
// million iterations. Ignored so the suite is green while the gap is documented;
// un-ignore when the trampoline lands.
#[test]
#[ignore = "needs the free-monad trampoline (break/continue/return and parameter-passing effect loops still grow the stack)"]
fn free_monad_loops_run_in_constant_stack() {
    if !have(&cc()) {
        eprintln!("skipping perf gate: C compiler `{}` not found (set PRISM_CC)", cc());
        return;
    }
    let n = 1_000_000;
    let cases: &[(&str, String)] = &[
        (
            "continue-heavy while loop",
            format!(
                "fn run(k : Int) : Int =\n  var s := 0\n  var i := 0\n  while i < k do\n    \
                 i += 1\n    if i % 2 == 1 then\n      continue\n    s += i\n  s\n\
                 fn main() = println(run({n}))\n"
            ),
        ),
        (
            "early-return loop",
            format!(
                "fn run(k : Int) : Int =\n  var i := 0\n  loop\n    if i >= k then\n      \
                 return i\n    i += 1\nfn main() = println(run({n}))\n"
            ),
        ),
        (
            "parameter-passing state loop",
            format!(
                "effect St {{\n  ctl rd(Unit) : Int,\n  ctl wr(Int) : Unit\n}}\n\
                 fn spin(k : Int) : !{{St}} Int =\n  if rd(()) < k then\n    wr(rd(()) + 1)\n    \
                 spin(k)\n  else\n    rd(())\n\
                 fn run(k : Int) : Int =\n  let f =\n    handle spin(k) with\n      \
                 rd(u, r) => \\(s) -> r(s)(s)\n      wr(v, r) => \\(_s) -> r(())(v)\n      \
                 return x => \\(_s) -> x\n  f(0)\n\
                 fn main() = println(run({n}))\n"
            ),
        ),
    ];
    let mut fails = Vec::new();
    for (name, src) in cases {
        if let Err(e) = runs_in_bounded_stack(&prism::with_prelude(src), name, 2048) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
