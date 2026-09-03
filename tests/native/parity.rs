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

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::{env, fs};

use prism::error::Error;
use prism::{build_on, default_roots, Config};

#[cfg(feature = "mlir")]
use crate::support::have;
use crate::support::{
    check_native_parity_costed, cleanup_bin, corpus_drops, interpreted, leak_free,
    parallel_collect, require_cc, shard_by, sharded_corpus, source, temp_bin, CaseCost,
    CHECK_LEAKS, CORPUS_SKIPS,
};
#[cfg(feature = "mlir")]
use prism::build_mlir_on;

// When the corpus oracle is delegated to the sharded `parity` CI matrix, the
// umbrella `cargo test --all` run sets this so it does not also run the whole
// corpus serially in the main job. Unset (a normal local `cargo test`, and the
// sanitizer re-runs) runs the full corpus.
const CORPUS_SHARDED_ENV: &str = "PRISM_CORPUS_SHARDED";

// Corpus builds run quiet. The effect-lowering fused-path warnings are
// diagnostics for an interactive `build`; under `--nocapture` they bury the
// actual test output. These wrappers are `prism::build`/`build_mlir` with
// `flags.quiet` set, resolving imports from `.` exactly as those do.
fn quiet_cfg() -> Config {
    let mut cfg = Config::from_env();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = false);
    cfg
}

fn build_quiet(src: &str, out: &Path) -> Result<(), Error> {
    build_on(src, &default_roots(Path::new(".")), out, &quiet_cfg())
}

#[cfg(feature = "mlir")]
fn build_mlir_quiet(src: &str, out: &Path) -> Result<(), Error> {
    build_mlir_on(src, &default_roots(Path::new(".")), out, &quiet_cfg())
}

// Build and diff the whole corpus across cores, collecting every failure so one
// run reports all divergences rather than aborting at the first. The build/run/
// diff/leak path and the fan-out live in `support` and are shared with the tier
// oracle (`tests/tier_parity.rs`). Corpus shrinkage is guarded separately by
// `corpus_skip_list_is_exact`, not a percentage floor.
fn run_corpus(tag: &str, build: impl Fn(&str, &Path) -> Result<(), Error> + Sync) -> CorpusRun {
    let cases = sharded_corpus();
    let (fails, costs) =
        parallel_collect(&cases, |case| check_native_parity_costed(case, tag, &build));
    assert!(
        fails.is_empty(),
        "{} of {} cases failed parity/leak:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
    // A gate-cache hit passes without running, so it contributes no measurement;
    // `costs` covers `cases` exactly on a cold run and a subset otherwise.
    CorpusRun {
        cases: cases.len(),
        costs: costs.into_iter().flatten().collect(),
    }
}

/// One pass over the corpus: how many programs it covered, and what the ones it
/// actually ran cost.
struct CorpusRun {
    cases: usize,
    costs: Vec<CaseCost>,
}

// The runnable corpus is defined by a runtime filter, so a change that stops a
// committed program interpreting would silently remove it from every oracle
// built on the corpus. Rather than tolerate that under a percentage floor, require
// the exact set of intentionally-excluded programs: any new drop fails here by
// name, and a program that becomes runnable again flags its stale skip entry.
#[test]
fn corpus_skip_list_is_exact() {
    let drops: BTreeSet<String> = corpus_drops().into_iter().collect();
    let listed: BTreeSet<&str> = CORPUS_SKIPS.iter().map(|(f, _)| *f).collect();
    let unexpected: Vec<&String> = drops
        .iter()
        .filter(|d| !listed.contains(d.as_str()))
        .collect();
    let stale: Vec<&str> = listed
        .iter()
        .copied()
        .filter(|s| !drops.contains(*s))
        .collect();
    assert!(
        unexpected.is_empty(),
        "corpus regression: these committed programs dropped out of the runnable \
         corpus but are not listed in crate::support::CORPUS_SKIPS (a silent shrink of \
         every corpus oracle): {unexpected:?}"
    );
    assert!(
        stale.is_empty(),
        "these crate::support::CORPUS_SKIPS entries are runnable again; remove them: {stale:?}"
    );
}

#[test]
fn native_matches_interpreter() {
    // The umbrella `cargo test --all` delegates the full corpus to the sharded
    // `parity` CI matrix; a local run (env unset) exercises the whole corpus here.
    if env::var_os(CORPUS_SHARDED_ENV).is_some() {
        return;
    }
    require_cc();
    let run = run_corpus("llvm", build_quiet);
    check_cost_manifest(&run);
}

// A closure can reach a LocalPartial entry through both a static helper return
// and an ANF variable. The two-point closure-shape flow must reject that split:
// monadifying `invoke` while its argument remains a fused bare closure used to
// compile successfully and then segfault natively.
#[test]
fn hidden_local_boundary_closure_matches_interpreter() {
    require_cc();
    let full = prism::with_prelude(
        "effect Log
  log(Int) : Int

fn weight(x) = x * 3
fn invoke(f) = f()
fn make() = \\() -> 7

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f())

fn logged(f) =
  let fs = [\\() -> log(weight(1)), \\() -> log(weight(2)), \\() -> log(weight(3))]
  let n =
    handle run_all(fs, 0) with
      log(value) resume k => k(value)
      return result => result
  n + invoke(f)

fn square(n) = n * n

fn main() =
  let f = make()
  println(weight(srange(1, 100).smap(square).ssum()))
  println(logged(f))
",
    );
    let expected = interpreted(&full);
    assert_eq!(expected, "985050\n25\n");

    let bin = temp_bin("hidden-local-boundary", "closure");
    build_quiet(&full, &bin).expect("native build failed");
    let output = Command::new(&bin)
        .env("PRISM_CHECK_LEAKS", "1")
        .output()
        .expect("native run failed");
    cleanup_bin(&bin);
    assert!(
        output.status.success(),
        "native exited {:#?}",
        output.status
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), expected);
    assert!(leak_free(&String::from_utf8_lossy(&output.stderr)));
}

// Applying a callback can itself return the closure that crosses the local
// convention boundary. The interpreter and native backend must agree after the
// analysis declines that split; treating every application as scalar used to
// leave the returned closure under two incompatible calling conventions.
#[test]
fn dynamically_returned_local_boundary_closure_matches_interpreter() {
    require_cc();
    let full = prism::with_prelude(
        "effect Log
  log(Int) : Int

fn weight(x) = x * 3
fn invoke(f) = f()
fn make_through(m) = m()

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f())

fn logged(f) =
  let fs = [\\() -> log(weight(1)), \\() -> log(weight(2)), \\() -> log(weight(3))]
  let n =
    handle run_all(fs, 0) with
      log(value) resume k => k(value)
      return result => result
  n + invoke(f)

fn square(n) = n * n

fn main() =
  let f = make_through(\\() -> \\() -> 7)
  println(weight(srange(1, 100).smap(square).ssum()))
  println(logged(f))
",
    );
    let expected = interpreted(&full);
    assert_eq!(expected, "985050\n25\n");

    let bin = temp_bin("dynamic-local-boundary", "closure");
    build_quiet(&full, &bin).expect("native build failed");
    let output = Command::new(&bin)
        .env("PRISM_CHECK_LEAKS", "1")
        .output()
        .expect("native run failed");
    cleanup_bin(&bin);
    assert!(
        output.status.success(),
        "native exited {:#?}",
        output.status
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), expected);
    assert!(leak_free(&String::from_utf8_lossy(&output.stderr)));
}

// A resumption supplies the value seen at the handled operation site. When that
// value is a closure, the convention boundary must follow it through the
// continuation just as it follows an ordinary function return.
#[test]
fn resumed_local_boundary_closure_matches_interpreter() {
    require_cc();
    let full = prism::with_prelude(
        "effect Log
  log(Int) : Int

effect AskFn
  ask_fn() : (Unit) -> Int

fn invoke(f) = f(())

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f(()))

fn logged(value) =
  let fs = [\\(_u) -> log(1), \\(_u) -> log(2)]
  let n =
    handle run_all(fs, 0) with
      log(item) resume k => k(item)
      return result => result
  n + invoke(value)

fn request() = ask_fn()

fn answered() =
  handle request() with
    ask_fn() resume k => k(\\(_u) -> 40)
    return result => result

fn main() = println(logged(answered()))
",
    );
    let expected = interpreted(&full);
    assert_eq!(expected, "43\n");

    let bin = temp_bin("resumed-local-boundary", "closure");
    build_quiet(&full, &bin).expect("native build failed");
    let output = Command::new(&bin)
        .env("PRISM_CHECK_LEAKS", "1")
        .output()
        .expect("native run failed");
    cleanup_bin(&bin);
    assert!(
        output.status.success(),
        "native exited {:#?}",
        output.status
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), expected);
    assert!(leak_free(&String::from_utf8_lossy(&output.stderr)));
}

// The shards must tile the corpus: disjoint and covering every case exactly once,
// so the sharded `parity` CI matrix loses no coverage. `SHARDS` must match the
// matrix length in ci.yml.
#[test]
fn shards_tile_the_corpus() {
    const SHARDS: usize = 4;
    // A count not divisible by SHARDS, so uneven tails are exercised.
    let full: Vec<PathBuf> = (0..37)
        .map(|i| PathBuf::from(format!("case{i}.pr")))
        .collect();
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    for k in 0..SHARDS {
        for p in shard_by(full.clone(), SHARDS, k) {
            assert!(seen.insert(p), "a case landed in two shards");
        }
    }
    assert_eq!(
        seen.len(),
        full.len(),
        "shards must cover every case exactly once"
    );
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
    // The cost manifest is pinned by the LLVM run alone: both backends link the
    // same runtime and materialize the same cells, so checking it twice would
    // only make the golden's ownership ambiguous.
    run_corpus("mlir", build_mlir_quiet);
}

// Build `full` natively, run it on `input` over stdin with leak checking, and
// return the process output. Shared by the stdin-driven oracles below, which
// cover the seam the empty-stdin corpus cannot: `read_int`/`read_line` codegen.
fn native_on_input(tag: &str, full: &str, input: &str) -> std::process::Output {
    let bin = env::temp_dir().join(format!("prism_parity_{tag}_{}", std::process::id()));
    build_quiet(full, &bin).expect("native build failed");
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
    let src = "fn echo2() : Unit ! {IO, Console} =\n  \
               println(show_int(read_int()))\n  \
               println(show_int(read_int()))\n\n\
               fn main() : Unit ! {IO} = echo2()\n";
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
        if !leak_free(&leak) {
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

// File and environment IO builtins (write_file/read_file/append_file/
// remove_file/file_exists/getenv) are excluded from the empty-stdin corpus,
// because their result is not a pure function of the source, so they had no
// native parity coverage at all. Exercise them hermetically: bake an absolute
// path under a fresh per-process temp dir into the program (cwd-independent, so
// interpreter and native touch the same file), round-trip through the whole
// file surface plus a getenv, and require byte-equal stdout and zero leaked
// cells. Unix-gated: the target platforms are macOS and Linux, and an absolute
// path is spliced into source text as-is.
#[cfg(unix)]
#[test]
fn file_env_io_matches_interpreter() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dir = env::temp_dir().join(format!("prism_io_parity_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("round_trip.txt");
    // Absolute path, so neither backend depends on its cwd. getenv is read on an
    // unset variable (deterministic empty string) to avoid mutating the
    // process-global environment while other test threads read it.
    let src = format!(
        "fn main() : Unit ! {{IO}} =\n  \
         let path = \"{path}\"\n  \
         write_file(path, \"hello, os surface\")\n  \
         println(if file_exists(path) then 1 else 0)\n  \
         let a = read_file(path)\n  \
         println(str_len(a))\n  \
         println(a)\n  \
         append_file(path, \"!!\")\n  \
         println(str_len(read_file(path)))\n  \
         remove_file(path)\n  \
         println(if file_exists(path) then 1 else 0)\n  \
         println(str_len(getenv(\"PRISM_IO_PARITY_UNSET\")))\n",
        path = file.display()
    );
    let full = prism::with_prelude(&src);

    let mut sink = Vec::new();
    let want = prism::interpret_io_at(&full, root, &mut sink, &mut std::io::empty())
        .expect("interpreter IO run failed")
        .term;
    let out = native_on_input("io_parity", &full, "");
    let got = String::from_utf8_lossy(&out.stdout).into_owned();
    let leak = String::from_utf8_lossy(&out.stderr).into_owned();

    let _ = fs::remove_file(&file);
    let _ = fs::remove_dir(&dir);

    assert_eq!(
        got, want,
        "file/env IO native output diverges from the interpreter"
    );
    assert!(
        leak_free(&leak),
        "file/env IO did not free all cells: {}",
        leak.trim()
    );
}

// `show_char` on a non-scalar code point (the UTF-16 surrogate range, anything
// past U+10FFFF, a negative value) is the empty string in the interpreter, which
// routes through char::from_u32; native previously encoded such values into an
// invalid byte sequence. Diff the shown byte length at both surrogate boundaries
// and the last code point. The empty-stdin corpus never reaches this input space,
// so it hid the divergence.
#[test]
fn show_char_non_scalar_matches_interpreter() {
    require_cc();
    let src = "fn main() : Unit ! {IO} =\n  \
               println(show_int(byte_len(show_char(chr(55295)))))\n  \
               println(show_int(byte_len(show_char(chr(55296)))))\n  \
               println(show_int(byte_len(show_char(chr(57343)))))\n  \
               println(show_int(byte_len(show_char(chr(57344)))))\n  \
               println(show_int(byte_len(show_char(chr(1114111)))))\n  \
               println(show_int(byte_len(show_char(chr(1114112)))))\n";
    let full = prism::with_prelude(src);
    let want = interpreted(&full);
    let out = native_on_input("show_char", &full, "");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native show_char diverges from the interpreter on non-scalar code points \
         (U+D7FF/U+D800/U+DFFF/U+E000/U+10FFFF/U+110000)"
    );
}

// `error(n)` raises the Exn fault: the interpreter streams any prior output, then
// terminates with status 1 and a stderr diagnostic. Native previously lowered it
// to libc exit(n), terminating with status n and no diagnostic, collapsing the
// distinct `exit` builtin. The empty-stdin corpus excludes faulting programs (the
// interpreter returns Err, so they are not runnable), and the parity harness did
// not assert exit codes, so this sat in a double blind spot. Check the full
// observable: stdout flushed identically through the fault, status 1, nonempty
// stderr. Run without leak checking: a fault abandons live cells by design.
#[test]
fn error_int_faults_like_interpreter() {
    require_cc();
    let src = "fn main() : Unit ! {IO, Exn} =\n  \
               println(show_int(7))\n  \
               let _ = error(42)\n  \
               println(show_int(99))\n";
    let full = prism::with_prelude(src);
    let mut sink = Vec::new();
    let res = prism::interpret_io_at(&full, Path::new("."), &mut sink, &mut std::io::empty());
    assert!(
        res.is_err(),
        "error(42) must fault in the interpreter, not run cleanly"
    );
    let want_stdout = String::from_utf8_lossy(&sink).into_owned();

    let bin = env::temp_dir().join(format!("prism_parity_error_int_{}", std::process::id()));
    build_quiet(&full, &bin).expect("native build failed");
    let out = Command::new(&bin).output().expect("spawn failed");
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);

    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want_stdout,
        "native error(n) stdout diverges: output before the fault must flush identically"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "error(n) must terminate with status 1 (a fault), not the payload as an exit code"
    );
    assert!(
        !out.stderr.is_empty(),
        "error(n) must report the fault on stderr"
    );
}

#[test]
fn fatal_string_faults_like_interpreter() {
    require_cc();
    let src = "fn main() : Unit ! {IO, Exn} =\n  \
               println(show_int(7))\n  \
               let _ = fatal(\"kaput\")\n  \
               println(show_int(99))\n";
    let full = prism::with_prelude(src);
    let mut sink = Vec::new();
    let res = prism::interpret_io_at(&full, Path::new("."), &mut sink, &mut std::io::empty());
    assert!(
        res.as_ref().is_err_and(|e| e.to_string().contains("kaput")),
        "fatal(\"kaput\") must fault in the interpreter with its message, got: {res:?}"
    );
    let want_stdout = String::from_utf8_lossy(&sink).into_owned();

    let bin = env::temp_dir().join(format!("prism_parity_fatal_string_{}", std::process::id()));
    build_quiet(&full, &bin).expect("native build failed");
    let out = Command::new(&bin).output().expect("spawn failed");
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);

    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want_stdout,
        "native fatal(msg) stdout diverges: output before the fault must flush identically"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "fatal(msg) must terminate with status 1"
    );
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("kaput"),
        "fatal(msg) must report its message on stderr"
    );
}

// A `print`/`println` whose argument type is a free rigid variable is a polymorphic
// print: `print` carries a `Show(a)` obligation, so it compiles only where that
// obligation is satisfied and is rejected where it is not. An annotated wrapper
// (`x : a`) with an enclosing `given Show(a)` discharges the obligation and prints
// through the dictionary; without the `given` the constraint has no witness and the
// call is rejected by ordinary constraint resolution. An unannotated wrapper cannot
// acquire a constraint at all (constrained functions must be fully annotated), so it
// is rejected by the elaborator's own backstop naming the same remedy. Concrete,
// monomorphic, and provably-empty-container prints stay on the type-directed
// structural printer and need no dictionary; the raw-printer runtime trap stays in
// the C runtime as defense in depth.
#[test]
fn polymorphic_print_requires_show_constraint() {
    let rejects = |src: &str, needle: &str| {
        let err = prism::interpret(&prism::with_prelude(src))
            .expect_err("a polymorphic print with no Show witness must be rejected");
        assert!(
            err.to_string().contains(needle),
            "expected a Show-obligation rejection containing {needle:?}, got: {err}"
        );
    };
    // Annotated wrapper, no `given`: the `Show(a)` obligation has no witness, so
    // constraint resolution rejects it and names the fix.
    rejects(
        "fn echo(x : a) : Unit ! {IO} = println(x)\nfn main() : Unit ! {IO} = echo(())\n",
        "given Show(a)",
    );
    // Inferred wrapper: `foo` generalizes to `forall a. (a) -> ...` but cannot carry
    // a constraint (no annotation), so the elaborator's backstop rejects it.
    rejects(
        "fn foo(x) = print(x)\nfn main() : Unit ! {IO} = foo((1, 2))\n",
        "polymorphic type",
    );

    // The obligation is satisfiable and does not over-fire: an annotated wrapper
    // under `given Show(a)` prints through the dictionary, and a concrete,
    // monomorphic, or provably-empty-container print stays structural.
    for ok in [
        "fn echo(x : a) : Unit ! {IO} given Show(a) = println(x)\n\
         fn main() : Unit ! {IO} = echo(())\n",
        "fn echo(x : Int) : Unit ! {IO} = println(x)\nfn main() : Unit ! {IO} = echo(5)\n",
        "fn main() : Unit ! {IO} = print(())\n",
        "fn main() : Unit ! {IO} = println([])\n",
    ] {
        assert!(
            prism::interpret(&prism::with_prelude(ok)).is_ok(),
            "a Show-constrained / concrete / monomorphic / empty-container print must compile: {ok:?}"
        );
    }
}

// Inside a `given Show(a)` function, polymorphic `print` dispatches through the
// dictionary, so `a = Bool` prints
// `true`/`false` (never the raw tag integer the raw printer would emit), and every
// type routes the same way on both backends. Diff native against the interpreter on
// a wrapper exercised at several types.
#[test]
fn polymorphic_show_print_dispatches_through_dictionary() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src = "type Color = Red | Green | Blue deriving (Show)\n\
               fn shout(x : a) : Unit ! {IO} given Show(a) =\n  \
                 print(\"[\")\n  \
                 print(x)\n  \
                 println(\"]\")\n\
               fn main() : Unit ! {IO} =\n  \
                 shout(42)\n  \
                 shout(true)\n  \
                 shout(false)\n  \
                 shout(Green)\n  \
                 shout([1, 2, 3])\n";
    let full = prism::with_prelude(src);
    let mut sink = Vec::new();
    let want = prism::interpret_io_at(&full, root, &mut sink, &mut std::io::empty())
        .expect("interpreter run failed")
        .term;
    // The Bool cases must be `true`/`false`, proving the dictionary path, not `1`/`0`.
    assert!(
        want.contains("[true]") && want.contains("[false]"),
        "generic print of Bool must use the Show dictionary: {want:?}"
    );
    let out = native_on_input("show_poly_dict", &full, "");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native polymorphic Show print diverges from the interpreter"
    );
}

// `string_of_buf` must render ill-formed UTF-8 identically on both backends.
// The interpreter's `String::from_utf8_lossy` substitutes one U+FFFD per maximal
// invalid subpart (Unicode Table 3-7); the native runtime kept raw bytes, so any
// non-UTF-8 input diverged on both `byte_len` and content. Drive a battery of
// tricky sequences (lone continuation, overlong, truncated multi-byte, surrogate,
// invalid lead, bad second byte) through it and require byte-equal stdout.
#[test]
fn string_of_buf_lossy_matches_interpreter() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src = "fn push2(a, x, y) = buf_push(buf_push(a, x), y)\n\
               fn push3(a, x, y, z) = buf_push(push2(a, x, y), z)\n\
               fn e() = buf_empty()\n\
               fn show_bytes(bs) : Unit ! {IO} =\n  \
                 let s = string_of_buf(bs)\n  \
                 println(byte_len(s))\n  \
                 println(s)\n\
               fn main() : Unit ! {IO} =\n  \
                 show_bytes(push2(e(), 72, 105))\n  \
                 show_bytes(push2(e(), 195, 169))\n  \
                 show_bytes(buf_push(e(), 128))\n  \
                 show_bytes(push2(e(), 255, 65))\n  \
                 show_bytes(push2(e(), 192, 128))\n  \
                 show_bytes(buf_push(e(), 195))\n  \
                 show_bytes(push3(e(), 224, 128, 128))\n  \
                 show_bytes(push3(e(), 226, 130, 172))\n  \
                 show_bytes(push3(e(), 237, 160, 128))\n  \
                 show_bytes(push2(e(), 240, 40))\n  \
                 show_bytes(push2(e(), 240, 144))\n";
    let full = prism::with_prelude(src);
    let mut sink = Vec::new();
    let want = prism::interpret_io_at(&full, root, &mut sink, &mut std::io::empty())
        .expect("interpreter run failed")
        .term;
    let out = native_on_input("str_of_buf_lossy", &full, "");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native string_of_buf diverges from the interpreter's lossy UTF-8 decode"
    );
}

// read_int parses the whole trimmed line, so trailing non-whitespace ("123abc")
// is an error on both backends, not a 123-prefix the native strtol would accept.
// The interpreter faults (Err); the native binary exits nonzero having printed
// nothing. A lenient native read that returned 123 was the divergence.
#[test]
fn read_int_rejects_trailing_garbage() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let full = prism::with_prelude("fn main() : Unit ! {IO} = println(show_int(read_int()))\n");
    let input = "123abc\n";
    let mut sink = Vec::new();
    let interp = prism::interpret_io_at(&full, root, &mut sink, &mut input.as_bytes());
    assert!(
        interp.is_err(),
        "interpreter should reject `123abc` as a non-integer line"
    );
    let out = native_on_input("readint_garbage", &full, input);
    assert!(
        !out.status.success(),
        "native read_int must reject `123abc`, not accept the 123 prefix"
    );
    assert!(
        out.stdout.is_empty(),
        "native read_int printed before failing: {:?}",
        String::from_utf8_lossy(&out.stdout)
    );
}

// The other two read_int edges the empty-stdin corpus cannot reach: end-of-input
// (an empty line or true EOF) is a fault on both backends, not a silent 0, and
// surrounding ASCII whitespace is tolerated identically (the interpreter's
// `line.trim().parse`). Native's getline/strtol path must fault where the
// interpreter faults and accept where it accepts, on the same bytes.
#[test]
fn read_int_eof_and_whitespace_match_interpreter() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let full = prism::with_prelude("fn main() : Unit ! {IO} = println(show_int(read_int()))\n");

    // Empty line, true EOF, and an interior space all fault before any output.
    for bad in ["\n", "", "12 34\n"] {
        let mut sink = Vec::new();
        let interp = prism::interpret_io_at(&full, root, &mut sink, &mut bad.as_bytes());
        assert!(
            interp.is_err(),
            "interpreter should fault on read_int input {bad:?}"
        );
        let out = native_on_input("readint_eof", &full, bad);
        assert!(
            !out.status.success(),
            "native read_int must fault on {bad:?}, not read a default"
        );
        assert!(
            out.stdout.is_empty(),
            "native read_int printed before failing on {bad:?}: {:?}",
            String::from_utf8_lossy(&out.stdout)
        );
    }

    // A whitespace-padded integer is accepted byte-identically on both backends.
    let ok = "  42  \n";
    let mut sink = Vec::new();
    let want = prism::interpret_io_at(&full, root, &mut sink, &mut ok.as_bytes())
        .expect("interpreter should accept a whitespace-padded integer")
        .term;
    let out = native_on_input("readint_ws", &full, ok);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native read_int diverges on a whitespace-padded integer"
    );
}

// The self-hosted parser must accept every committed Prism source file. The
// bootstrap harness is compiled natively (itself a whole-stdlib build, so this
// doubles as a large-program codegen exercise), then every `.pr` under the
// stdlib and packages trees is lexed, laid out, and parsed by `Syntax.Parse`;
// any refusal fails by name. The floor on the walk's size keeps a misrooted or
// empty enumeration from passing vacuously, and the run is leak-checked like
// every other native oracle.
const SELF_PARSE_HARNESS: &str = "tests/fixtures/parser/self_parse.pr";
const SELF_PARSE_DIRS: [&str; 2] = ["lib/std", "packages"];
const SELF_PARSE_MIN_FILES: usize = 100;

fn pr_files_under(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            pr_files_under(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("pr") {
            out.push(path);
        }
    }
}

#[test]
fn self_parse_accepts_committed_sources() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for dir in SELF_PARSE_DIRS {
        pr_files_under(&root.join(dir), &mut files);
    }
    files.sort();
    assert!(
        files.len() >= SELF_PARSE_MIN_FILES,
        "self-parse corpus walk found only {} files; the enumeration is broken",
        files.len()
    );

    let full = source(&root.join(SELF_PARSE_HARNESS));
    let bin = temp_bin("selfparse", "self_parse");
    build_quiet(&full, &bin).expect("native build of the self-parse harness failed");
    let out = Command::new(&bin)
        .current_dir(root)
        .env(CHECK_LEAKS, "1")
        .args(&files)
        .output()
        .expect("self-parse harness did not run");
    cleanup_bin(&bin);

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "self-parse harness exited nonzero:\n{stderr}"
    );
    let refused: Vec<&str> = stdout
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with("ok "))
        .collect();
    assert!(
        refused.is_empty(),
        "the self-hosted parser refused committed sources:\n{}",
        refused.join("\n")
    );
    let accepted = stdout.lines().filter(|l| l.starts_with("ok ")).count();
    assert_eq!(
        accepted,
        files.len(),
        "self-parse verdict count diverges from the corpus walk"
    );
    assert!(leak_free(&stderr), "self-parse harness leaked:\n{stderr}");
}

// The System F example exercises the typechecker core end to end: its seven
// witness lines are a pinned interpreter fixture, and its silent assertions
// (substitution capture, alpha equivalence, occurs rejection, meta union then
// solve) print only on violation, so any extra output here is a regression.
#[test]
fn systemf_witnesses_pinned() {
    let full = source(Path::new("examples/systemf.pr"));
    assert_eq!(
        interpreted(&full),
        "id                 : forall a. a -> a\n\
         id[Int] 42         : Int\n\
         implicit id true   : Bool\n\
         higher rank        : (forall a. a -> a) -> Bool\n\
         union-find         : (forall a. a) -> Int\n\
         bad application    : error: application expects a function, got Int\n\
         bad branches       : error: cannot unify Int with Bool\n"
    );
}

// The DK companion uses the same surface and resolved trees as systemf.pr but
// replaces union-find unification with ordered existential contexts and the
// bidirectional checking/subtyping judgments. Its silent baselines pin scope,
// occurs, annotation, alpha-equivalence, and capture behavior.
#[test]
fn systemf_dk_witnesses_pinned() {
    let full = source(Path::new("examples/systemf_dk.pr"));
    assert_eq!(
        interpreted(&full),
        "id                 : forall a. a -> a\n\
         id[Int] 42         : Int\n\
         higher rank        : (forall a. a -> a) -> Bool\n\
         impredicative      : forall a. a -> a\n\
         bad application    : error: application expects a function, got Int\n\
         bad argument       : error: no subtype rule for Int <: Bool\n"
    );
}

// Record interpreter transitions and native heap allocations alongside output
// parity. Each counter is compared only with its own recorded baseline.
//
// The allowed band combines `COST_DRIFT_FACTOR` with `COST_DRIFT_SLACK`, avoiding
// churn on small counts while retaining a bound for every program.
//
// Increases are regressions; decreases indicate a stale baseline.

const COST_MANIFEST: &str = "tests/cost_manifest.txt";
const COST_MANIFEST_ACCEPT: &str = "PRISM_ACCEPT_COST_MANIFEST";
/// How far a count may move from its baseline, either way, before it is reported:
/// this factor plus [`COST_DRIFT_SLACK`].
const COST_DRIFT_FACTOR: i64 = 2;
/// The flat term of the band, in the counter's own units. It keeps the bound
/// meaningful on programs whose counts are small enough that a ratio alone is
/// noise.
const COST_DRIFT_SLACK: i64 = 64;
const COST_MANIFEST_HEADER: &str = r"# Resource-cost baselines for the differential parity corpus. One
# `<program>\t<interpreter steps>\t<native cells allocated>` line per corpus
# program, sorted. The golden checked by tests/parity.rs::native_matches_interpreter
# against a loose band: a count that moves further than that fails, an increase as
# a cost regression and a decrease as a stale baseline. Regenerate a reviewed
# change with PRISM_ACCEPT_COST_MANIFEST=1 from a full cold run. Do not hand-edit.
";

const COST_MANIFEST_FIELDS: usize = 3;
const COST_LABEL_FIELD: usize = 0;
const COST_STEPS_FIELD: usize = 1;
const COST_CELLS_FIELD: usize = 2;

fn render_cost_manifest(costs: &[CaseCost]) -> String {
    let mut s = String::from(COST_MANIFEST_HEADER);
    for c in costs {
        let _ = writeln!(s, "{}\t{}\t{}", c.label, c.interp_steps, c.native_cells);
    }
    s
}

fn parse_cost_manifest(text: &str) -> BTreeMap<String, (i64, i64)> {
    text.lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(
                f.len(),
                COST_MANIFEST_FIELDS,
                "cost manifest line is `label<TAB>steps<TAB>cells`: {l:?}"
            );
            let n = |i: usize| {
                f[i].parse()
                    .unwrap_or_else(|e| panic!("cost manifest count {:?}: {e}", f[i]))
            };
            (
                f[COST_LABEL_FIELD].to_string(),
                (n(COST_STEPS_FIELD), n(COST_CELLS_FIELD)),
            )
        })
        .collect()
}

/// The upper edge of the band around a baseline count.
const fn cost_ceiling(baseline: i64) -> i64 {
    baseline
        .saturating_mul(COST_DRIFT_FACTOR)
        .saturating_add(COST_DRIFT_SLACK)
}

/// How a measured count left its band, or `None` when it is inside. The band is
/// symmetric: a measurement is out of band exactly when one of the two counts
/// exceeds the other's ceiling.
fn cost_drift(unit: &str, want: i64, got: i64) -> Option<String> {
    let band = format!("outside {COST_DRIFT_FACTOR}x + {COST_DRIFT_SLACK}");
    if got > cost_ceiling(want) {
        return Some(format!("{unit} {want} -> {got}, more ({band})"));
    }
    if want > cost_ceiling(got) {
        return Some(format!("{unit} {want} -> {got}, less ({band})"));
    }
    None
}

const INTERP_STEPS_UNIT: &str = "interpreter steps";
const NATIVE_CELLS_UNIT: &str = "native cells";

fn check_cost_manifest(run: &CorpusRun) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(COST_MANIFEST);
    let mut measured = run.costs.clone();
    measured.sort_by(|a, b| a.label.cmp(&b.label));

    if env::var_os(COST_MANIFEST_ACCEPT).is_some() {
        // Only a run that measured every program may rewrite the golden. A
        // sharded or cache-warm run measures a subset, and writing that out would
        // silently drop the rest of the corpus and disarm the gate for it.
        assert_eq!(
            measured.len(),
            run.cases,
            "refusing to regenerate {COST_MANIFEST} from a partial run ({} of {} programs \
             measured). Rerun cold and unsharded, with the gate cache off.",
            measured.len(),
            run.cases
        );
        assert!(
            !measured.is_empty(),
            "refusing to regenerate {COST_MANIFEST} from an empty corpus: fix the tree, then rerun."
        );
        fs::write(&path, render_cost_manifest(&measured)).expect("write cost manifest");
        eprintln!(
            "cost manifest regenerated: {} programs -> {COST_MANIFEST}",
            measured.len()
        );
        return;
    }

    let golden = parse_cost_manifest(&fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read cost manifest {COST_MANIFEST} ({e}); regenerate with \
             PRISM_ACCEPT_COST_MANIFEST=1"
        )
    }));
    let mut drifted: Vec<String> = Vec::new();
    let mut missing: Vec<String> = Vec::new();
    for c in &measured {
        let Some(&(steps, cells)) = golden.get(&c.label) else {
            missing.push(format!(
                "  {}: no baseline ({INTERP_STEPS_UNIT} {}, {NATIVE_CELLS_UNIT} {})",
                c.label, c.interp_steps, c.native_cells
            ));
            continue;
        };
        for d in [
            cost_drift(INTERP_STEPS_UNIT, steps, c.interp_steps),
            cost_drift(NATIVE_CELLS_UNIT, cells, c.native_cells),
        ]
        .into_iter()
        .flatten()
        {
            drifted.push(format!("  {}: {d}", c.label));
        }
    }
    assert!(
        drifted.is_empty(),
        r"resource cost left its band for {} program(s). An increase is a cost regression parity cannot see (find the optimization that stopped firing); a decrease is a win the baseline has not recorded yet. Either way, investigate first, then regenerate with PRISM_ACCEPT_COST_MANIFEST=1:
{}",
        drifted.len(),
        drifted.join("\n")
    );
    assert!(
        missing.is_empty(),
        r"{} corpus program(s) have no cost baseline; regenerate with PRISM_ACCEPT_COST_MANIFEST=1:
{}",
        missing.len(),
        missing.join("\n")
    );
}
