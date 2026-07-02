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
// A missing C compiler is a hard failure, not a silent skip: a local `cargo
// test` must not pass while exercising zero native, reference-counting, or
// fusion coverage. CI sets PRISM_CC. Cases build across cores because cargo
// already runs test functions (and their LLVM builds) concurrently, so per-case
// temp paths and a fresh inkwell context per build are the only isolation needed.

use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::{env, fs, thread};

use prism::error::Error;

mod common;
#[cfg(feature = "mlir")]
use common::have;
use common::{candidate_count, corpus, interpreted, require_cc, source};

fn check_parity(
    case: &Path,
    tag: &str,
    build: impl Fn(&str, &Path) -> Result<(), Error>,
) -> Result<(), String> {
    let full = source(case);
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = env::temp_dir().join(format!("prism_parity_{tag}_{}_{stem}", std::process::id()));
    let fail = |msg: String| {
        for ext in ["bc", "ll"] {
            let _ = fs::remove_file(bin.with_extension(ext));
        }
        let _ = fs::remove_file(&bin);
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
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);
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
    // The corpus is defined by a runtime filter (interprets cleanly, stays
    // on-platform), so a regression that stops many examples interpreting would
    // silently shrink every oracle drawing on it. Tie the floor to the
    // committed file count rather than an absolute constant.
    let total = candidate_count();
    assert!(
        cases.len() * 100 >= total * 95,
        "runnable corpus shrank to {} of {} committed programs; discovery or \
         the interpreter likely broke",
        cases.len(),
        total
    );
    let next = AtomicUsize::new(0);
    let fails: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let threads = thread::available_parallelism()
        .map_or(4, std::num::NonZeroUsize::get)
        .min(cases.len());
    thread::scope(|s| {
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
    require_cc();
    run_corpus("llvm", prism::build);
}

#[cfg(feature = "mlir")]
#[test]
fn mlir_matches_interpreter() {
    require_cc();
    assert!(
        have("mlir-translate"),
        "`mlir-translate` not found. The --features mlir parity oracle requires \
         it; install LLVM/MLIR so the MLIR backend is exercised."
    );
    run_corpus("mlir", prism::build_mlir);
}

// Build `full` natively, run it on `input` over stdin with leak checking, and
// return the process output. Shared by the stdin-driven oracles below, which
// cover the seam the empty-stdin corpus cannot: `read_int`/`read_line` codegen.
fn native_on_input(tag: &str, full: &str, input: &str) -> std::process::Output {
    let bin = env::temp_dir().join(format!("prism_parity_{tag}_{}", std::process::id()));
    prism::build(full, &bin).expect("native build failed");
    let mut child = Command::new(&bin)
        .env("PRISM_CHECK_LEAKS", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn failed");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);
    out
}

// read_int must keep the full i64 range: a value in (2^62, 2^63) fits an i64
// but not the 63-bit tagged immediate, so the runtime returns it encoded (a
// bignum cell) rather than letting codegen's retag shift out bit 62. Feed both
// signs of the boundary explicitly and diff against the interpreter on the
// same input.
#[test]
fn read_int_keeps_full_i64_range() {
    require_cc();
    let src = "fn echo2() : !{IO, Console} Unit =\n  \
               println(show_int(read_int()))\n  \
               println(show_int(read_int()))\n\n\
               fn main() : !{IO} Unit = echo2()\n";
    let full = prism::with_prelude(src);
    let input = "4611686018427387905\n-4611686018427387905\n";
    let mut sink = Vec::new();
    let want = prism::interpret_io_at(&full, Path::new("."), &mut sink, &mut input.as_bytes())
        .expect("interpreter run failed")
        .term;
    let out = native_on_input("readint", &full, input);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native read_int diverges from the interpreter on 63/64-bit boundary values"
    );
}

// The interactive examples are excluded from the empty-stdin corpus, which
// leaves read_int/read_line codegen with no parity coverage there. Each has a
// committed input fixture (`examples/<name>.in`); run native and interpreter on
// the same fixture bytes and require byte-equal stdout plus zero leaked cells.
#[test]
fn io_fixtures_match_interpreter() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut ran = 0usize;
    let mut fails = Vec::new();
    for entry in fs::read_dir(root.join("examples")).unwrap().flatten() {
        let fixture = entry.path();
        if fixture.extension().and_then(|e| e.to_str()) != Some("in") {
            continue;
        }
        let case = fixture.with_extension("pr");
        let stem = case.file_stem().unwrap().to_string_lossy().into_owned();
        let input = fs::read_to_string(&fixture).unwrap();
        let full = source(&case);
        let mut sink = Vec::new();
        let want = match prism::interpret_io_at(&full, root, &mut sink, &mut input.as_bytes()) {
            Ok(run) => run.term,
            Err(e) => {
                fails.push(format!(
                    "{}: interpreter failed on fixture: {e}",
                    case.display()
                ));
                continue;
            }
        };
        let out = native_on_input(&format!("io_{stem}"), &full, &input);
        let got = String::from_utf8_lossy(&out.stdout);
        if got != want {
            fails.push(format!(
                "io fixture output diverges for {}:\n  native: {got:?}\n  interp: {want:?}",
                case.display()
            ));
            continue;
        }
        let leak = String::from_utf8_lossy(&out.stderr);
        if leak.trim_end() != "prism: 0 cells leaked" {
            fails.push(format!(
                "{} did not free all cells: {}",
                case.display(),
                leak.trim()
            ));
            continue;
        }
        ran += 1;
    }
    assert!(
        fails.is_empty(),
        "{} io fixture case(s) failed:\n{}",
        fails.len(),
        fails.join("\n")
    );
    assert!(
        ran >= 4,
        "only {ran} io fixtures ran; the committed .in fixtures likely moved"
    );
}
