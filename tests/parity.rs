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

use std::collections::BTreeSet;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use std::{env, fs};

use prism::error::Error;

mod common;
#[cfg(feature = "mlir")]
use common::have;
use common::{
    check_native_parity, corpus, corpus_drops, interpreted, leak_free, parallel_check, require_cc,
    source, CORPUS_SKIPS,
};

// Build and diff the whole corpus across cores, collecting every failure so one
// run reports all divergences rather than aborting at the first. The build/run/
// diff/leak path and the fan-out live in `common` and are shared with the tier
// oracle (`tests/tier_parity.rs`). Corpus shrinkage is guarded separately by
// `corpus_skip_list_is_exact`, not a percentage floor.
fn run_corpus(tag: &str, build: impl Fn(&str, &Path) -> Result<(), Error> + Sync) {
    let cases = corpus();
    let fails = parallel_check(&cases, |case| check_native_parity(case, tag, &build));
    assert!(
        fails.is_empty(),
        "{} of {} cases failed parity/leak:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}

// The runnable corpus is defined by a runtime filter, so a change that stops a
// committed program interpreting would silently remove it from every oracle
// built on the corpus. Rather than tolerate that under a percentage floor, pin
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
         corpus but are not listed in common::CORPUS_SKIPS (a silent shrink of \
         every corpus oracle): {unexpected:?}"
    );
    assert!(
        stale.is_empty(),
        "these common::CORPUS_SKIPS entries are runnable again; remove them: {stale:?}"
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
        "fn main() : !{{IO}} Unit =\n  \
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
    let src = "fn main() : !{IO} Unit =\n  \
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
// not assert exit codes, so this sat in a double blind spot. Pin the full
// observable: stdout flushed identically through the fault, status 1, nonempty
// stderr. Run without leak checking: a fault abandons live cells by design.
#[test]
fn error_int_faults_like_interpreter() {
    require_cc();
    let src = "fn main() : !{IO, Exn} Unit =\n  \
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
    prism::build(&full, &bin).expect("native build failed");
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

// A `print`/`println` whose argument type is a free rigid variable (an enclosing
// parameter, not a defaultable empty container) is rejected at compile time. No
// static type could render the value, and lowering it to the raw runtime printer
// would abort on a structural cell, so the interp/native divergence is closed at
// the source rather than at runtime. The wrapper body is elaborated once over the
// rigid variable, before any call-site instantiation, so both an annotated
// (`x : a`) and an inferred wrapper reject regardless of how the call instantiates
// it. The remedy the diagnostic names -- annotate the argument concretely, or
// `show(x)` under a `Show` constraint -- keeps every legitimate print helper
// compiling (the corpus was rewritten to the annotated form). The raw-printer
// runtime trap stays in the C runtime as defense in depth but is no longer
// reachable from compilable source.
#[test]
fn polymorphic_print_rejected_at_compile_time() {
    let rejects = |src: &str| {
        let err = prism::interpret(&prism::with_prelude(src))
            .expect_err("a polymorphic print must be rejected at compile time");
        assert!(
            err.to_string().contains("polymorphic type"),
            "expected the polymorphic-print rejection, got: {err}"
        );
    };
    // Annotated wrapper: the body prints a value of rigid type `a`, at every call.
    rejects("fn echo(x : a) : !{IO} Unit = println(x)\nfn main() : !{IO} Unit = echo(())\n");
    // Inferred wrapper: `foo` generalizes to `forall a. (a) -> ...`, so passing a
    // concrete tuple at the call does not monomorphize the already-elaborated body.
    rejects("fn foo(x) = print(x)\nfn main() : !{IO} Unit = foo((1, 2))\n");

    // The gate does not over-fire: a concretely-annotated argument (the corpus
    // remedy), a monomorphic print, and a provably-empty polymorphic container
    // all still compile.
    for ok in [
        "fn echo(x : Int) : !{IO} Unit = println(x)\nfn main() : !{IO} Unit = echo(5)\n",
        "fn main() : !{IO} Unit = print(())\n",
        "fn main() : !{IO} Unit = println([])\n",
    ] {
        assert!(
            prism::interpret(&prism::with_prelude(ok)).is_ok(),
            "annotated / monomorphic / empty-container print must still compile: {ok:?}"
        );
    }
}

// `string_of_bytes` must render ill-formed UTF-8 identically on both backends.
// The interpreter's `String::from_utf8_lossy` substitutes one U+FFFD per maximal
// invalid subpart (Unicode Table 3-7); the native runtime kept raw bytes, so any
// non-UTF-8 input diverged on both `byte_len` and content. Drive a battery of
// tricky sequences (lone continuation, overlong, truncated multi-byte, surrogate,
// invalid lead, bad second byte) through it and require byte-equal stdout.
#[test]
fn string_of_bytes_lossy_matches_interpreter() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src = "fn push2(a, x, y) = array_push(array_push(a, x), y)\n\
               fn push3(a, x, y, z) = array_push(push2(a, x, y), z)\n\
               fn e() = array_empty()\n\
               fn show_bytes(bs) : !{IO} Unit =\n  \
                 let s = string_of_bytes(bs)\n  \
                 println(byte_len(s))\n  \
                 println(s)\n\
               fn main() : !{IO} Unit =\n  \
                 show_bytes(push2(e(), 72, 105))\n  \
                 show_bytes(push2(e(), 195, 169))\n  \
                 show_bytes(array_push(e(), 128))\n  \
                 show_bytes(push2(e(), 255, 65))\n  \
                 show_bytes(push2(e(), 192, 128))\n  \
                 show_bytes(array_push(e(), 195))\n  \
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
    let out = native_on_input("str_of_bytes_lossy", &full, "");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        want,
        "native string_of_bytes diverges from the interpreter's lossy UTF-8 decode"
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
    let full = prism::with_prelude("fn main() : !{IO} Unit = println(show_int(read_int()))\n");
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
    let full = prism::with_prelude("fn main() : !{IO} Unit = println(show_int(read_int()))\n");

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
