// Every native binary must reproduce the interpreter's printed output exactly
// AND free every heap cell, over the whole runnable corpus: each `.pr` in
// `examples/` and `tests/cases/run/` that the interpreter executes cleanly on
// empty stdin and that stays on-platform (no file/env IO). The clean-run filter
// is the corpus definition: it admits exactly the programs a native binary can
// be diffed against, excluding error cases, library files with no `main`, the
// interactive examples that block on input, and off-platform IO whose result is
// not a pure function of the source.
//
// This lifts the two deepest invariants, backend parity (interp == LLVM/MLIR
// byte-for-byte) and deterministic reference counting (zero leaked cells),
// into `cargo test`, which CI and pre-commit run.
//
// Skips cleanly when no C compiler is available; CI sets PRISM_CC. Cases build
// across cores because cargo already runs test functions (and their LLVM
// builds) concurrently, so per-case temp paths and a fresh inkwell context per
// build are the only isolation needed.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use prism::error::Error;

fn cc() -> String {
    std::env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

fn source(path: &Path) -> String {
    prism::with_prelude(&std::fs::read_to_string(path).unwrap())
}

// The interpreter's real terminal output, byte-for-byte what a native binary's
// stdout must equal. `term` (not a join over `out`) preserves the print/println
// distinction: a bare `print` adds no newline.
fn interpreted(full: &str) -> String {
    prism::interpret(full).unwrap().term
}

// The runnable corpus: every example/run-case the interpreter executes cleanly
// on empty stdin, restricted to on-platform programs. The interpret-Ok filter
// excludes error cases, no-`main` library files, and the interactive examples
// that block on input; the off-platform filter excludes file/env IO whose
// native and interpreted runs are not a pure function of the source.
fn corpus() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for dir in ["examples", "tests/cases/run"] {
        for entry in std::fs::read_dir(root.join(dir)).unwrap().flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("pr") {
                continue;
            }
            let full = source(&path);
            let on_platform =
                prism::off_platform_builtins(&full, root).is_ok_and(|ops| ops.is_empty());
            if on_platform && prism::interpret(&full).is_ok() {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

fn check_parity(
    case: &Path,
    tag: &str,
    build: impl Fn(&str, &Path) -> Result<(), Error>,
) -> Result<(), String> {
    let full = source(case);
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin =
        std::env::temp_dir().join(format!("prism_parity_{tag}_{}_{stem}", std::process::id()));
    let fail = |msg: String| {
        for ext in ["bc", "ll"] {
            let _ = std::fs::remove_file(bin.with_extension(ext));
        }
        let _ = std::fs::remove_file(&bin);
        Err(msg)
    };
    if let Err(e) = build(&full, &bin) {
        return fail(format!("{}: build failed: {e}", case.display()));
    }
    let out = match Command::new(&bin).env("PRISM_CHECK_LEAKS", "1").output() {
        Ok(o) => o,
        Err(e) => return fail(format!("{}: spawn failed: {e}", case.display())),
    };
    for ext in ["bc", "ll"] {
        let _ = std::fs::remove_file(bin.with_extension(ext));
    }
    let _ = std::fs::remove_file(&bin);
    // A program whose `main` returns a non-Unit value exits with that value as
    // its code (factorial(5) exits 120), so the exit status is not asserted; a
    // crash instead truncates stdout and is caught by the output diff below.
    let got = String::from_utf8_lossy(&out.stdout);
    let want = interpreted(&full);
    if got != want {
        return Err(format!(
            "{tag} output diverges for {}:\n  native: {got:?}\n  interp: {want:?}",
            case.display()
        ));
    }
    // Deterministic reference counting must free every cell; the runtime reports
    // the live count under PRISM_CHECK_LEAKS at exit, on stderr alone.
    let leak = String::from_utf8_lossy(&out.stderr);
    if leak.trim_end() != "prism: 0 cells leaked" {
        return Err(format!(
            "{} did not free all cells: {}",
            case.display(),
            leak.trim()
        ));
    }
    Ok(())
}

// Build and diff the whole corpus across cores, collecting every failure so one
// run reports all divergences rather than aborting at the first.
fn run_corpus(tag: &str, build: impl Fn(&str, &Path) -> Result<(), Error> + Sync) {
    let cases = corpus();
    assert!(
        cases.len() >= 30,
        "runnable corpus shrank to {} cases; discovery likely broke",
        cases.len()
    );
    let next = AtomicUsize::new(0);
    let fails: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism()
        .map_or(4, std::num::NonZeroUsize::get)
        .min(cases.len());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let Some(case) = cases.get(i) else { break };
                if let Err(e) = check_parity(case, tag, &build) {
                    fails.lock().unwrap().push(e);
                }
            });
        }
    });
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} of {} cases failed parity/leak:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}

#[test]
fn native_matches_interpreter() {
    if !have(&cc()) {
        eprintln!(
            "skipping parity: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
    run_corpus("llvm", prism::build);
}

#[cfg(feature = "mlir")]
#[test]
fn mlir_matches_interpreter() {
    if !have(&cc()) || !have("mlir-translate") {
        eprintln!("skipping mlir parity: clang or mlir-translate not found");
        return;
    }
    run_corpus("mlir", prism::build_mlir);
}
