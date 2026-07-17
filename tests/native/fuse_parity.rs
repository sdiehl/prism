// Fusion-invisibility oracle: stream fusion is a lowering tier, so compiling a
// program with the fusion pass ON must not change one byte of observable output.
// For every program whose Core the pass actually rewrites (the dedicated fusion
// corpus, where it fires, plus any general-corpus program it touches), this builds
// the fuse-ON native binary and diffs its stdout, exit code, and leak report
// against the interpreter, the same anchor `tests/parity.rs` checks the fuse-OFF
// build against. The two gates together give native(fused) == native(unfused):
// tier-vs-tier agreement, enforced rather than argued.
//
// A program whose Core is byte-identical under the pass is skipped: its fuse-ON
// build is identical to the fuse-OFF one parity.rs already diffs. A firing floor
// keeps the oracle from going vacuous if recognition silently breaks, and a
// determinism check covers the byte-stable join naming the anti-unifier promises.

use std::path::{Path, PathBuf};

use prism::{default_roots, dump_on, Config};

use crate::support::{check_native_parity, corpus, parallel_check, require_cc, source};

fn fused() -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.fuse = true;
    cfg.flags.compiler_cache = false;
    cfg
}

// The dedicated fusion corpus: pipelines that exercise the pass (and stateful or
// list-building shapes that must degrade cleanly), read directly so the oracle has
// a firing floor independent of what the general corpus happens to contain.
fn fuse_cases() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cases/fuse");
    let mut out: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("pr"))
        .collect();
    out.sort();
    out
}

// The cases the oracle exercises with fusion on: the dedicated fusion corpus
// (always, so a pipeline that must DEGRADE cleanly is natively verified too), plus
// every general-corpus program whose Core the pass actually rewrites. A general
// program the pass leaves byte-identical builds the same native binary either way,
// so parity.rs already covers it and it is skipped here.
fn touched_cases() -> Vec<PathBuf> {
    // Discovery compiles the whole corpus twice. Debug builds exceed libtest's
    // smaller worker stack even though the same scan passes on the public
    // compiler's 8 MiB main-thread stack. The selected cases still run through
    // `parallel_check`, whose workers retain their separate interpreter budget.
    let result = std::thread::Builder::new()
        .name("fusion-case-discovery".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(touched_cases_on_compiler_stack)
        .expect("spawning fusion case discovery")
        .join();
    match result {
        Ok(cases) => cases,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn touched_cases_on_compiler_stack() -> Vec<PathBuf> {
    let base = Path::new(".");
    let roots = default_roots(base);
    let mut off = Config::from_env();
    off.flags.compiler_cache = false;
    let on = fused();
    let mut cases: Vec<PathBuf> = corpus()
        .into_iter()
        .filter(|case| {
            let full = source(case);
            let a = dump_on("core", &full, &roots, &off);
            let b = dump_on("core", &full, &roots, &on);
            match (a, b) {
                (Ok(a), Ok(b)) => a != b,
                // A dump error under exactly one config is itself a divergence worth
                // surfacing through the build below.
                _ => true,
            }
        })
        .collect();
    cases.extend(fuse_cases());
    cases.sort();
    cases.dedup();
    cases
}

// Build every exercised case with fusion on via `build`, diffing against the
// interpreter. Shared by the LLVM and MLIR backends.
fn run_touched(tag: &str, build: impl Fn(&str, &Path) -> Result<(), prism::Error> + Sync) {
    require_cc();
    let cases = touched_cases();
    assert!(
        cases.len() >= 6,
        r"fusion oracle exercises only {} programs (floor 6); the fusion corpus or recognition likely broke",
        cases.len()
    );
    let fails = parallel_check(&cases, |case| check_native_parity(case, tag, &build));
    assert!(
        fails.is_empty(),
        "{} of {} fuse-on ({tag}) cases diverged from the interpreter:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}

#[test]
fn fuse_on_matches_interpreter_llvm() {
    let roots = default_roots(Path::new("."));
    let cfg = fused();
    run_touched("fuse-llvm", |full, bin| {
        prism::build_on(full, &roots, bin, &cfg)
    });
}

#[cfg(feature = "mlir")]
#[test]
fn fuse_on_matches_interpreter_mlir() {
    assert!(
        crate::support::have("mlir-translate"),
        "`mlir-translate` not found; the --features mlir fusion oracle requires it"
    );
    let roots = default_roots(Path::new("."));
    let cfg = fused();
    run_touched("fuse-mlir", |full, bin| {
        prism::build_mlir_on(full, &roots, bin, &cfg)
    });
}

// Recognition must actually fire: at least this many dedicated pipelines fuse (their
// Core gains a `%fuse$` join). Guards against a silent regression that makes the
// parity tests above vacuously pass on programs the pass no longer touches.
#[test]
fn fusion_fires_on_pipelines() {
    let roots = default_roots(Path::new("."));
    let cfg = fused();
    let fired = fuse_cases()
        .iter()
        .filter(|c| dump_on("core", &source(c), &roots, &cfg).is_ok_and(|s| s.contains("%fuse$")))
        .count();
    assert!(
        fired >= 3,
        "fusion fired on only {fired} dedicated pipelines (floor 3); recognition broke"
    );
}

// Byte-stable join naming: compiling a pipeline twice with fusion on yields
// identical Core, the deterministic hole-ordering and `%fuse$` numbering the
// anti-unifier is obliged to produce.
#[test]
fn fusion_is_deterministic() {
    let roots = default_roots(Path::new("."));
    let cfg = fused();
    for c in fuse_cases() {
        let full = source(&c);
        let a = dump_on("core", &full, &roots, &cfg).unwrap();
        let b = dump_on("core", &full, &roots, &cfg).unwrap();
        assert_eq!(a, b, "fused Core is not byte-stable for {}", c.display());
    }
}
