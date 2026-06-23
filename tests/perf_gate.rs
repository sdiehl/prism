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

fn cc() -> String {
    std::env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
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
    let src = std::fs::read_to_string(&path).map_err(|e| format!("{case}: {e}"))?;
    let full = tiny_prism::with_prelude(&src);
    let bin = std::env::temp_dir().join(format!(
        "prism_perf_{}_{}",
        std::process::id(),
        case.replace(['/', '.'], "_")
    ));
    let cleanup = || {
        for ext in ["bc", "ll"] {
            let _ = std::fs::remove_file(bin.with_extension(ext));
        }
        let _ = std::fs::remove_file(&bin);
    };
    if let Err(e) = tiny_prism::build(&full, &bin) {
        cleanup();
        return Err(format!("{case}: build failed: {e}"));
    }
    let out = Command::new(&bin).env(stat_env, "1").output();
    cleanup();
    let out = out.map_err(|e| format!("{case}: spawn failed: {e}"))?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    let line = stderr
        .lines()
        .find(|l| l.trim_end().ends_with(suffix))
        .ok_or_else(|| format!("{case}: no `{suffix}` line in stderr: {stderr:?}"))?;
    line.split_whitespace()
        .nth(1)
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| format!("{case}: cannot parse count from {line:?}"))
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
