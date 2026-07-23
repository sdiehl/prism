// Every pipeline phase (tokens, ast, types, core, llvm, run) is snapshotted per
// case. Update with: INSTA_UPDATE=always cargo test --test snapshots

#![allow(clippy::format_push_string)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

// Whole-corpus gates repeatedly invoke the in-process compiler. Debug builds
// can exceed libtest's smaller worker stack even though the same corpus passes
// in release and on the public compiler's 8 MiB main-thread stack. Match that
// finite production budget so genuine recursion regressions still fail.
const COMPILER_STACK: usize = 8 * 1024 * 1024;

fn on_compiler_stack(name: &'static str, gate: fn()) {
    let result = std::thread::Builder::new()
        .name(name.into())
        .stack_size(COMPILER_STACK)
        .spawn(gate)
        .unwrap_or_else(|error| panic!("spawning {name}: {error}"))
        .join();
    if let Err(payload) = result {
        std::panic::resume_unwind(payload);
    }
}

#[test]
fn pipeline() {
    insta::glob!("cases/*.pr", |path| {
        let src = fs::read_to_string(path).unwrap();
        insta::assert_snapshot!(normalize_pipeline_report(&prism::report(&src)));
    });
}

fn normalize_pipeline_report(report: &str) -> String {
    let mut out = String::with_capacity(report.len());
    for line in report.lines() {
        let line = line.replace(env!("PRISM_TARGET"), "aarch64-apple-darwin");
        let line = normalize_native_kont_global_len(&line);
        let line = line.replace("section \".prism_kont\"", "section \",.prism_kont\"");
        let line = line.replace(
            "section \"__DATA,__prism_kont\"",
            "section \",.prism_kont\"",
        );
        let line = line.replace("section \"llvm.metadata\"", "section \",llvm.metadata\"");
        out.push_str(&line);
        out.push('\n');
    }
    out
}

fn normalize_native_kont_global_len(line: &str) -> String {
    const CANONICAL_TARGET: &str = "aarch64-apple-darwin";
    const PREFIXES: [&str; 2] = [
        "@prism_native_kont_table = constant [",
        "@prism_native_kont_state_map = constant [",
    ];

    if !PREFIXES.iter().any(|prefix| line.starts_with(prefix)) {
        return line.to_string();
    }

    let Some(start) = line.find('[').map(|index| index + 1) else {
        return line.to_string();
    };
    let Some(relative_end) = line[start..].find(" x i8]") else {
        return line.to_string();
    };
    let end = start + relative_end;
    let Ok(len) = line[start..end].parse::<isize>() else {
        return line.to_string();
    };
    let target_delta =
        env!("PRISM_TARGET").len().cast_signed() - CANONICAL_TARGET.len().cast_signed();
    let normalized = len - target_delta;

    format!("{}{}{}", &line[..start], normalized, &line[end..])
}

// Golden shape digests for the standard library's structural surface: datatype
// and effect shapes, class interfaces, and instance identities. Committed so that
// a change to a serialization-relevant type, class, or instance shows up in
// review rather than silently. Term behavior hashes are excluded (they are
// covered by tests/stdlib_hash.rs); this checks the shapes, the frozen-format seed.
// Update with INSTA_UPDATE=always cargo test --test snapshots.
#[test]
fn stdlib_shape_digests() {
    let h = prism::stdlib_hash().unwrap();
    let mut lines = Vec::new();
    for (k, v) in &h.shapes {
        lines.push(format!("shape {}  {k}", &v[..16]));
    }
    for (k, v) in &h.classes {
        lines.push(format!("class {}  {k}", &v[..16]));
    }
    for (k, v) in &h.instances {
        lines.push(format!("inst  {}  {k}", &v[..16]));
    }
    lines.sort();
    insta::assert_snapshot!(lines.join("\n"));
}

// The per-type format-identity gate, generalized past the standard library to
// user-defined types. A representative spread (an enum, a positional product, a
// sum with arguments, a recursive parametric type, a record, and an effect)
// commits its structural shape digest. A later edit that changes the wire layout
// of any of these moves its digest and fails this golden; a cosmetic edit leaves
// it untouched. This is the copy-paste pattern a downstream project uses to guard
// its own persisted types via `shape_digests_of`. Update with
// INSTA_UPDATE=always cargo test --test snapshots.
#[test]
fn user_type_shape_digests() {
    const SRC: &str = "\
type Color = Red | Green | Blue
type Point = P(Int, Int)
type Shape = Circle(Int) | Rect(Int, Int)
type Tree(a) = Leaf(a) | Branch(Tree(a), Tree(a))
type Range = Range { lo: Int, hi: Int }
effect Log
  log(String) : Unit
";
    let all = prism::shape_digests_of(&prism::with_prelude(SRC)).expect("shape digests");
    let names = ["Color", "Point", "Shape", "Tree", "Range", "Log"];
    let mut lines: Vec<String> = names
        .iter()
        .map(|n| format!("{n}  {}", &all[*n][..16]))
        .collect();
    lines.sort();
    insta::assert_snapshot!(lines.join("\n"));
}

#[test]
fn prelude_type_checks() {
    let checked = prism::check(prism::with_prelude("").as_str()).unwrap();
    let mut lines: Vec<String> = checked
        .decls
        .iter()
        .map(|d| {
            format!(
                "{} : {}",
                d.name,
                prism::types::show_type_with_effects(&d.ty, &d.effects)
            )
        })
        .collect();
    lines.sort();
    insta::assert_snapshot!(lines.join("\n"));
}

// A real effect annotation the body never performs is sound (a pure body
// satisfies it by subsumption) but non-tight, so the checker warns rather than
// rejecting it. A performed effect is tight and stays quiet.
#[test]
fn nontight_effect_annotation_warns() {
    let warns = |src: &str| -> Vec<String> {
        prism::check(prism::with_prelude(src).as_str())
            .unwrap()
            .warnings
            .into_iter()
            .map(|w| w.msg)
            .collect()
    };
    let loose = warns("effect Eff\n  op(Unit) : Int\nfn f() : Int ! {Eff} = 1\n");
    assert!(
        loose.iter().any(|m| m.contains("never performed")),
        "expected a non-tight effect-annotation warning, got {loose:?}"
    );
    let tight = warns("effect Eff\n  op(Unit) : Int\nfn f() : Int ! {Eff} = op(())\n");
    assert!(
        tight.iter().all(|m| !m.contains("never performed")),
        "a performed effect should not warn, got {tight:?}"
    );
}

// The surface `deprecated "..."` annotation warns at use sites, carrying the
// author's suggestion. A warning, never an error; behavior is unchanged.
#[test]
fn deprecated_annotation_warns() {
    let src = prism::with_prelude(
        "deprecated \"use `+` on Float\"\n\
         fn old_add(x : Float, y : Float) : Float = plus(x, y)\n\
         fn main() : Unit = println(show(old_add(1.0, 2.0)))\n",
    );
    let msgs: Vec<String> = prism::check(&src)
        .unwrap()
        .warnings
        .into_iter()
        .map(|w| w.msg)
        .filter(|m| m.contains("deprecated"))
        .collect();
    assert_eq!(msgs, vec!["`old_add` is deprecated: use `+` on Float"]);
}

// The float dot-operators were removed: the plain operators are lane-polymorphic
// over Float. Writing one is a pointed parse error naming the plain operator.
#[test]
fn float_dot_operators_removed() {
    for (src, plain) in [
        ("fn f() : Float = 1.0 +. 2.0\n", "+"),
        ("fn f() : Float = 1.0 *. 2.0\n", "*"),
        ("fn f() : Bool = 1.0 <. 2.0\n", "<"),
        ("fn f() : Bool = 1.0 ==. 2.0\n", "=="),
    ] {
        let err = prism::check(&prism::with_prelude(src))
            .expect_err("a float dot-operator must be rejected")
            .to_string();
        assert!(err.contains("was removed") && err.contains(plain), "{err}");
    }
}

// The fixed-width arithmetic builtins and `string_of_bytes` were removed from the
// surface; the plain operators cover the arithmetic on the fixed-width lanes. A
// call to one no longer resolves.
#[test]
fn duplicate_builtins_removed() {
    for src in [
        "fn f() : I64 = i64_mul(2i64, 3i64)\n",
        "fn f() : U64 = u64_add(1u64, 2u64)\n",
        "fn f() : String = string_of_bytes(array_empty())\n",
    ] {
        prism::check(&prism::with_prelude(src)).expect_err("a removed builtin must not resolve");
    }
}

// Local `var` state must discharge: fib2 uses two vars yet keeps a pure row.
#[test]
fn var_stays_pure() {
    let root = env!("CARGO_MANIFEST_DIR");
    let src = fs::read_to_string(format!("{root}/tests/cases/run/fib_var.pr")).unwrap();
    let checked = prism::check(prism::with_prelude(&src).as_str()).unwrap();
    let d = checked.decls.iter().find(|d| d.name == "fib2").unwrap();
    assert_eq!(d.ty.show(), "(Int) -> Int");
    assert_eq!(prism::types::show_effects(&d.effects), "{}");
}

// The bounded-stack rule is scoped to `fip`. The identical non-tail recursive
// body type-checks as `fbip` (zero heap, unbounded stack is allowed) but is
// rejected as `fip`, which now also proves bounded stack. `relay` is linear
// (each binding used once), so it clears the allocation/linearity passes and the
// rejection is purely the new stack rule.
#[test]
fn bounded_stack_rule_is_fip_only() {
    let prog = |kw: &str| {
        prism::with_prelude(&format!(
            "fip fn wrap(x) = x\n{kw} fn relay(x) = wrap(relay(x))\nfn main() = println((relay(1) : Int))"
        ))
    };
    prism::dump("core", &prog("fbip")).expect("fbip may recurse non-tail");
    let err = format!("{}", prism::dump("core", &prog("fip")).unwrap_err());
    assert!(
        err.contains("non-tail position"),
        "fip relay must be rejected for non-tail recursion: {err}"
    );
}

// The promise/codegen handshake: every tail-recursive function the new
// `check_fip` accepts must be lowered to a loop by the backend, never a
// self-call frame. Both read `core::tailrec`, so an accepted `fip` self-call
// becomes a `musttail` jump and no plain self-call survives.
#[cfg(feature = "native")]
#[test]
fn fip_tail_recursion_lowers_to_a_loop() {
    let src = prism::with_prelude("fip fn spin(x) = spin(x)\nfn main() = println((spin(1) : Int))");
    let ir = prism::emit_ir(&src).expect("tail-recursive fip must be accepted");
    let spin = prism::codegen::native_symbol("spin");
    let start = ir
        .find(&format!("define i64 @{spin}("))
        .expect("spin must be emitted");
    let rest = &ir[start..];
    let block = &rest[..rest.find("\n}").map_or(rest.len(), |e| e + 2)];
    assert!(
        block.contains("musttail call"),
        "spin must loop via musttail, not recurse:\n{block}"
    );
    let total = block.matches(&format!("call i64 @{spin}")).count();
    let tail = block.matches(&format!("musttail call i64 @{spin}")).count();
    assert_eq!(
        total, tail,
        "every self-call must be a tail loop, not a stack frame:\n{block}"
    );
}

// The realistic payoff: a recursive accumulator (`rev_onto`, a tail call) and a
// spine map (`bump`, tail-modulo-constructor) both accepted as `fip` and both
// lowered to constant-stack loops. `rev_onto`'s self-call is a `musttail` jump;
// `bump` is split into a `.trmc` hole-passing loop. Neither leaves a plain
// self-call frame in its own body.
#[cfg(feature = "native")]
#[test]
fn recursive_fip_examples_lower_to_loops() {
    let src = prism::with_prelude(
        "fip fn rev_onto(xs, acc) =\n  match xs of\n    Nil => acc\n    Cons(h, t) => rev_onto(t, Cons(h, acc))\n\
         fip fn bump(xs) =\n  match xs of\n    Nil => Nil\n    Cons(h, t) => Cons(h + 1, bump(t))\n\
         fn main() = println(sum(rev_onto([1,2,3], Nil)) + sum(bump([1,2,3])))",
    );
    let ir = prism::emit_ir(&src).expect("recursive accumulator/TRMC fip must be accepted");
    let block = |sym: &str| {
        let start = ir
            .find(&format!("define i64 @{sym}("))
            .unwrap_or_else(|| panic!("{sym} must be emitted"));
        let rest = &ir[start..];
        rest[..rest.find("\n}").map_or(rest.len(), |e| e + 2)].to_string()
    };
    // rev_onto: its own body must self-call only via musttail.
    let rev_onto = prism::codegen::native_symbol("rev_onto");
    let rev = block(&rev_onto);
    let rev_total = rev.matches(&format!("call i64 @{rev_onto}")).count();
    let rev_tail = rev
        .matches(&format!("musttail call i64 @{rev_onto}"))
        .count();
    assert!(
        rev_tail >= 1 && rev_total == rev_tail,
        "rev_onto must loop:\n{rev}"
    );
    // bump: the recursion lives in the `.trmc` hole-passing helper, looping via
    // musttail; the `bump` wrapper itself does not self-recurse.
    let bump_trmc = prism::codegen::trmc_symbol("bump");
    let trmc = block(&bump_trmc);
    assert!(
        trmc.contains(&format!("musttail call i64 @{bump_trmc}")),
        "bump must lower to a TRMC loop:\n{trmc}"
    );
}

// Higher-order effect inference: a function's row must account for effects
// performed by applying its function-typed arguments. `apply` propagates its
// argument's row into its own, and an effect routed through `apply` (an opaque
// function value the set pass cannot see) surfaces in the caller's row.
#[test]
fn higher_order_effects_propagate() {
    let src = "effect Exn\n  raise(Int) : Int\n\
               fn apply(f, x) = f(x)\n\
               fn boom(n) : Int ! {Exn} = raise(n)\n\
               fn go(n) = apply(boom, n)\n";
    let checked = prism::check(prism::with_prelude(src).as_str()).unwrap();
    let apply = checked.decls.iter().find(|d| d.name == "apply").unwrap();
    assert_eq!(
        apply.ty.show(),
        "forall e0 a b. ((b) -> a ! {e0}, b) -> a ! {e0}"
    );
    // The effect launders through `apply` (a function value) yet still lands in
    // `go`'s row and reported effects, which the syntactic set pass missed.
    let go = checked.decls.iter().find(|d| d.name == "go").unwrap();
    assert_eq!(go.ty.show(), "(Int) -> Int ! {Exn}");
    assert_eq!(prism::types::show_effects(&go.effects), "{Exn}");
}

// A handler discharges the effect it names from the surrounding row, even when
// the effect arrived through an opaque function value.
#[test]
fn handler_discharges_higher_order_effect() {
    let src = "effect Exn\n  raise(Int) : Int\n\
               fn apply(f, x) = f(x)\n\
               fn boom(n) : Int ! {Exn} = raise(n)\n\
               fn attempt(n) =\n  handle apply(boom, n) with\n    raise(c) resume k => c\n    return r => r\n";
    let checked = prism::check(prism::with_prelude(src).as_str()).unwrap();
    let attempt = checked.decls.iter().find(|d| d.name == "attempt").unwrap();
    assert_eq!(attempt.ty.show(), "(Int) -> Int");
    assert_eq!(prism::types::show_effects(&attempt.effects), "{}");
}

// Purity gates read the inferred row, so an effect laundered through a function
// value can no longer slip past a `borrow` parameter's purity requirement.
#[test]
fn borrow_rejects_laundered_effect() {
    let src = "effect Exn\n  raise(Int) : Int\n\
               fn apply(f, x) = f(x)\n\
               fn boom(n) : Int ! {Exn} = raise(n)\n\
               fn use_borrow(borrow x, n) = apply(boom, n) + x\n";
    let err = prism::check(prism::with_prelude(src).as_str()).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("borrow") && msg.contains("Exn"), "got: {msg}");
}

// `mask<Eff>(e)` injects Eff into the inferred row exactly like the set pass: a
// masked op bypasses one handler, so the expression still demands an enclosing
// one. The two effect engines must agree, so a masked effect can no longer
// under-report and slip past a `borrow` parameter's purity requirement.
#[test]
fn mask_reports_effect_in_both_engines() {
    // The inferred row carries the masked effect.
    let ok = "effect Ask\n  ask() : Int\nfn m() = mask<Ask>(5)\n";
    let checked = prism::check(prism::with_prelude(ok).as_str()).unwrap();
    let m = checked.decls.iter().find(|d| d.name == "m").unwrap();
    assert_eq!(prism::types::show_effects(&m.effects), "{Ask}");
    // And the purity gate (which reads that row) rejects a masked effect under a
    // `borrow` parameter, just as it does an ordinary one.
    let bad = "effect Ask\n  ask() : Int\nfn g(borrow x) = mask<Ask>(x)\n";
    let err = prism::check(prism::with_prelude(bad).as_str()).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("borrow") && msg.contains("Ask"), "got: {msg}");
}

// `exit` ends the process mid-program: in-process snapshotting would kill the
// test runner and the `=> ...` trailer never prints, so the run-snapshot and
// parity oracles cannot hold it. Assert stdout and the exit code via the CLI.
#[test]
fn exit_code_and_stdout() {
    let path = env::temp_dir().join("prism_exit_case.pr");
    fs::write(
        &path,
        "fn main() =\n  println(1)\n  exit(7)\n  println(2)\n",
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "1\n");
    assert_eq!(out.status.code(), Some(7));
}

// Local monadification partitions the lowered program: the escaping Log
// component reifies into the free monad (EOp cells threaded by `ebind`), while
// the unrelated stream pipeline stays fused (its producers thread evidence/state
// and build no EOp cell). Checks the split so a regression that re-globalizes
// monadification, dragging the pipeline monadic, surfaces here.
#[test]
fn local_monadification_partition() {
    let root = env!("CARGO_MANIFEST_DIR");
    let src = fs::read_to_string(format!("{root}/tests/cases/run/local_mono_combined.pr")).unwrap();
    let lowered = prism::dump("lowered", &prism::with_prelude(&src)).unwrap();
    // Extract a top-level function body (from `fn name(` to the next `\nfn `).
    let fn_body = |name: &str| -> String {
        let start = lowered
            .find(&format!("fn {name}("))
            .unwrap_or_else(|| panic!("`{name}` missing from lowered dump"));
        let rest = &lowered[start..];
        let end = rest[1..].find("\nfn ").map_or(rest.len(), |e| e + 1);
        rest[..end].to_string()
    };
    // The region is monadic: the free monad and its binder appear.
    assert!(
        lowered.contains("EOp") && lowered.contains("ebind"),
        "the escaping Log component must reify into the free monad"
    );
    assert!(
        fn_body("run_all").contains("ebind"),
        "the dynamically-applied region function must be monadified"
    );
    // The stream pipeline stays fused: its producers thread evidence/state and
    // build no EOp cell.
    for f in ["srange_go", "smap_go"] {
        let body = fn_body(f);
        assert!(
            !body.contains("EOp") && !body.contains("ebind"),
            "fused pipeline function `{f}` must not reify into the free monad:\n{body}"
        );
        assert!(
            body.contains("st@") || body.contains("ev@"),
            "fused pipeline function `{f}` must thread fusion evidence/state:\n{body}"
        );
    }
    // `weight` is a pure helper called from both the region (the escaping
    // closures) and the rest (`main`). A closure-inert function stays shared in
    // the rest rather than being pulled into the monadic region, so it neither
    // reifies nor gains fusion parameters: a plain bare function called from both
    // conventions. A regression that pulled it in would force a whole-program bail.
    let weight = fn_body("weight");
    assert!(
        weight.starts_with("fn weight(x) =")
            && !weight.contains("EPure")
            && !weight.contains("EOp")
            && !weight.contains("ev@")
            && !weight.contains("st@"),
        "the shared inert helper `weight` must stay a plain bare function (no monadic \
         EPure/EOp, no appended fusion parameters):\n{weight}"
    );
}

// The free-monad fallback warning is off by default, opt-in via `--verbose`, then
// proportionate and free of false positives. A fully fused program is silent; a
// program with one escaping effectful closure warns exactly once, naming the
// entangled functions and the cause, never the unrelated fused pipeline beside it.
// Spawned via the CLI so the compile-time stderr is observable.
#[test]
fn free_monad_warning_is_opt_in_and_proportionate() {
    let root = env!("CARGO_MANIFEST_DIR");
    let stderr = |case: &str| {
        let out = Command::new(env!("CARGO_BIN_EXE_prism"))
            .arg("run")
            .arg("--verbose")
            .arg(format!("{root}/{case}"))
            .output()
            .unwrap();
        String::from_utf8_lossy(&out.stderr).into_owned()
    };
    // Off by default: the escaping program stays silent without `--verbose`.
    let quiet = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(format!("{root}/tests/cases/run/local_mono_combined.pr"))
        .output()
        .unwrap();
    assert!(
        !String::from_utf8_lossy(&quiet.stderr).contains("fell off the fused path"),
        "the fusion warning must be silent without --verbose"
    );
    // Zero false positives: a fully fused stream program says nothing.
    let fused = stderr("examples/stream_fold.pr");
    assert!(
        !fused.contains("fell off the fused path"),
        "a fully fused program must emit no free-monad warning, got: {fused}"
    );
    // Exactly one warning, naming the escaping component and its cause.
    let escaping = stderr("tests/cases/run/local_mono_combined.pr");
    assert_eq!(
        escaping.matches("fell off the fused path").count(),
        1,
        "an escaping program must warn exactly once: {escaping}"
    );
    assert!(
        escaping.contains("`logged`")
            && escaping.contains("run_all")
            && escaping.contains("captures an effectful computation"),
        "the warning must name the entangled functions and the cause: {escaping}"
    );
    // Proportionate: the unrelated fused pipeline is never blamed.
    assert!(
        !escaping.contains("smap_go") && !escaping.contains("srange_go"),
        "the warning must not name the fused pipeline: {escaping}"
    );
}

// read_file on a missing path must fail loudly, never return "" silently.
// Spawned like the exit test so the nonzero exit code is observable.
#[test]
fn read_file_missing_fails_loudly() {
    let missing = env::temp_dir().join("prism_no_such_file.txt");
    let _ = fs::remove_file(&missing);
    let prog = env::temp_dir().join("prism_read_missing.pr");
    let src = format!(
        "fn main() =\n  print(read_file(\"{}\"))\n",
        missing.display()
    );
    fs::write(&prog, src).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&prog)
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("read_file"));
}

// An effect that escapes every handler must trap on BOTH backends, never
// silently succeed. The interpreter raises `unhandled effect`; the native
// backend must too (it once let the escaped `EOp` flow out of a selective-mode
// `main` as a bare value, exiting 0 with wrong output). Spawned like the exit
// test: assert the nonzero exit and the named effect on each backend that runs.
#[test]
fn unhandled_effect_traps_both_backends() {
    let prog = env::temp_dir().join("prism_unhandled_eff.pr");
    fs::write(
        &prog,
        "effect Ask\n  ask() : Int\nfn f() = ask()\nfn main() = println(f())\n",
    )
    .unwrap();
    let bin = env!("CARGO_BIN_EXE_prism");

    let run = Command::new(bin).arg("run").arg(&prog).output().unwrap();
    assert!(
        !run.status.success(),
        "interp must trap an unhandled effect"
    );
    let run_msg = format!(
        "{}{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(run_msg.contains("unhandled effect"), "interp: {run_msg}");

    // Native: build then run. Skip only if the toolchain to produce a binary is
    // absent (mirrors the gate's tool-gating); never treat absence as a pass.
    let nbin = env::temp_dir().join("prism_unhandled_eff.bin");
    // Bare `prism <file>` compiles a single file to a native binary; `-o` sets
    // the output path (`prism build` is the project-only verb).
    let built = Command::new(bin)
        .arg(&prog)
        .arg("-o")
        .arg(&nbin)
        .output()
        .unwrap();
    if built.status.success() {
        let nat = Command::new(&nbin).output().unwrap();
        assert!(
            !nat.status.success(),
            "native must trap an unhandled effect, not exit 0"
        );
        let nat_msg = format!(
            "{}{}",
            String::from_utf8_lossy(&nat.stdout),
            String::from_utf8_lossy(&nat.stderr)
        );
        assert!(nat_msg.contains("unhandled effect"), "native: {nat_msg}");
    }
}

fn interp_output(path: &Path) -> String {
    let src = fs::read_to_string(path).unwrap();
    let full = prism::with_prelude(&src);
    match prism::interpret(&full) {
        Ok(run) => format!("{}=> {}", run.term, run.value.show()),
        Err(e) => format!("ERROR: {e}"),
    }
}

#[test]
fn interpreter() {
    // A whole-corpus in-process gate, so run it on the compiler stack: debug
    // builds can exceed libtest's smaller worker stack on the deepest corpus
    // programs (stream fusion) even though the production 8 MiB binary runs them.
    on_compiler_stack("interpreter", || {
        insta::glob!("cases/run/*.pr", |path| insta::assert_snapshot!(
            interp_output(path)
        ));
    });
}

// Terminal-printer coverage. `print` dispatches by type into three native
// terminal printers (integer, float, string); every other shape is shown to a
// string first, so the only runtime kinds that can reach a terminal printer
// (and thus appear in `run.out`) are Int, Big, Float, Str. Recording all four as
// exercised keeps each native terminal printer inside the parity net. The
// structural shapes (ADTs, tuples, I64/U64/Bool/Unit) are covered the other
// way: `print_structural.pr` prints one of each directly so the gate's
// native-parity loop verifies the type-directed printer per shape, instead of
// hiding it behind `print(show(x))` (the original blind spot).
#[test]
fn print_kind_coverage() {
    on_compiler_stack("print-kind-coverage", print_kind_coverage_on_compiler_stack);
}

fn print_kind_coverage_on_compiler_stack() {
    let root = env!("CARGO_MANIFEST_DIR");
    let mut seen = std::collections::BTreeSet::new();
    for dir in ["tests/cases/run", "examples"] {
        for e in fs::read_dir(format!("{root}/{dir}")).unwrap().flatten() {
            let path = e.path();
            if path.extension().and_then(|s| s.to_str()) != Some("pr") {
                continue;
            }
            let src = fs::read_to_string(&path).unwrap();
            if let Ok(run) = prism::interpret(&prism::with_prelude(&src)) {
                seen.extend(run.out.iter().map(prism::eval::Rv::kind));
            }
        }
    }
    let missing: Vec<_> = ["Int", "Big", "Float", "Str"]
        .iter()
        .filter(|k| !seen.contains(*k))
        .collect();
    assert!(
        missing.is_empty(),
        "no corpus case prints these terminal runtime kinds: {missing:?}. \
         Add a direct `print(x)` case so the native-parity gate covers it."
    );
}

// Direct-print consistency over a shape matrix. `print(x)` and `print(show(x))`
// must agree for every printable shape: the print path renders non-primitives
// in the same canonical format the `Show` instances produce, so any divergence
// between the two spellings is a drift between the print-site generator and the
// typeclass. This is the systematic guard for the blind spot (a corpus that
// only ever writes `print(show(x))`): it exercises bare `print(x)` for each
// shape rather than growing the corpus one example at a time. Native parity for
// the same shapes rides `print_structural.pr`.
//
// A bare `String` is deliberately excluded: `print` writes it raw (as a
// message), while `show` renders the canonical quoted-and-escaped literal, so
// the two legitimately differ for that one shape.
#[test]
fn print_show_consistency() {
    let cases = [
        "5",
        "1000000000000000000000",
        "3i64",
        "7u64",
        "true",
        "()",
        "Green",
        "Node(Leaf, 5, Leaf)",
        "[1, 2, 3]",
        "(7, false)",
        "[(1, true), (2, false)]",
    ];
    let prelude = "type Color = Red | Green | Blue deriving (Show)\n\
                   type Tree = Leaf | Node(Tree, Int, Tree) deriving (Show)\n";
    for c in cases {
        let direct = run_out(&format!("{prelude}fn main() =\n  print({c})\n"));
        let shown = run_out(&format!("{prelude}fn main() =\n  print(show({c}))\n"));
        assert_eq!(direct, shown, "print({c}) != print(show({c}))");
    }
}

fn run_out(src: &str) -> String {
    prism::interpret(&prism::with_prelude(src)).unwrap().term
}

// The CBPV showcase lives in examples/, outside the cases/run glob. Its
// run snapshot is named like the glob ones so the gate's native-parity
// loop picks it up, and its core dump (no prelude) keeps the CBPV
// thunk/force/bind structure visible.
#[test]
fn cbpv_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/cbpv.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@cbpv.pr", out);
    let src = fs::read_to_string(&path).unwrap();
    insta::assert_snapshot!("cbpv_core", prism::dump("core", &src).unwrap());
}

// Effect polymorphism showcase, also in examples/. The snapshot name keeps
// the glob convention so the gate's native-parity loop picks it up.
#[test]
fn eff_poly_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/eff_poly.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@eff_poly.pr", out);
}

// Local-mutation showcase, also in examples/. Same naming trick, and the
// purity claim in the example is checked: fib_iter mutates two vars yet
// infers an empty effect row.
#[test]
fn var_pure_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/var_pure.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@var_pure.pr", out);
    let src = fs::read_to_string(&path).unwrap();
    let checked = prism::check(prism::with_prelude(&src).as_str()).unwrap();
    let d = checked.decls.iter().find(|d| d.name == "fib_iter").unwrap();
    assert_eq!(d.ty.show(), "(Int) -> Int");
    assert_eq!(prism::types::show_effects(&d.effects), "{}");
}

// Deconstructors showcase, also in examples/. Same naming trick so the
// gate's native-parity loop covers it; the fbip assertion checks constructor
// reuse on a nested update path (no prelude, so the only reuse is main's).
#[test]
fn lenses_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/lenses.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@lenses.pr", out);
    let src = "type A = A { x: Int }\ntype B = B { a: A }\n\
               fn main() =\n  let b = B { a = A { x = 1 } }\n  print({ b | a.x = 2 }.a.x)\n";
    let fbip = prism::dump("fbip", src).unwrap();
    assert!(fbip.contains("reuse#"), "nested update path must reuse");
}

// `deriving (Lens)` showcase, also in examples/. Same naming trick so the
// gate's native-parity loop covers it; the fbip assertion checks that the
// synthesized `with_<f>` setter reuses the constructor on a unique value.
#[test]
fn lens_derive_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/lens_derive.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@lens_derive.pr", out);
    let src = "type P = P { x: Int, y: Int } deriving (Lens)\n\
               fn main() =\n  print(with_x(P { x = 1, y = 2 }, 9).x)\n";
    let fbip = prism::dump("fbip", src).unwrap();
    assert!(fbip.contains("reuse#"), "derived setter must reuse");
}

// Class-dispatched pattern showcase, also in examples/. Same naming trick so
// the gate's native-parity loop covers it; one `pattern .. for <class>` view
// deconstructs every instance type by dictionary dispatch.
#[test]
fn class_pattern_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/class_pattern.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@class_pattern.pr", out);
}

// Full stream fusion showcase, also in examples/. Same naming trick so the
// gate's native-parity loop covers it. The lowered assertion checks that the
// producer -> smap -> skeep -> consumer chain threads emit evidence into each
// stream thunk and fuses to direct forced calls: no `do`, no handle, no EOp
// constructor survives.
#[test]
fn stream_fuse_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/stream_fuse.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@stream_fuse.pr", out);
    let src = fs::read_to_string(&path).unwrap();
    let lowered = prism::dump("lowered", &prism::with_prelude(&src)).unwrap();
    assert!(
        !lowered.contains("EOp") && !lowered.contains("ebind"),
        "stream chain must fuse away the free monad (no EOp cells, no ebind)"
    );
    assert!(
        !lowered.contains("handle"),
        "stream chain must inline its handlers"
    );
}

// Fold-consumer fusion (Blocker B): a fold handler is parameter-passing, not
// tail-resumptive, so state threading drives it. The lowered assertion checks
// that producer -> smap -> skeep -> fold threads the accumulator into each
// stream thunk and leaves no `do`, handle, or EOp constructor behind.
#[test]
fn stream_fold_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/stream_fold.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@stream_fold.pr", out);
    let src = fs::read_to_string(&path).unwrap();
    let lowered = prism::dump("lowered", &prism::with_prelude(&src)).unwrap();
    assert!(
        !lowered.contains("EOp") && !lowered.contains("ebind"),
        "fold chain must fuse away the free monad (no EOp cells, no ebind)"
    );
    assert!(
        !lowered.contains("handle"),
        "fold chain must inline its handlers"
    );
}

// Full stream-fusion showcase: `stake` early termination (the Step protocol) plus a fold
// chain and for-loop consumers over a second stream, all in one program. The
// lowered assertion checks that the whole program fuses with no `do`, handle, or
// EOp cell left, only the threaded Step state.
#[test]
fn streams_example() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path = format!("{root}/examples/streams.pr");
    let out = interp_output(Path::new(&path));
    insta::assert_snapshot!("interpreter@streams.pr", out);
    let src = fs::read_to_string(&path).unwrap();
    let lowered = prism::dump("lowered", &prism::with_prelude(&src)).unwrap();
    assert!(
        !lowered.contains("EOp") && !lowered.contains("ebind"),
        "streams must fuse away the free monad (no EOp cells, no ebind)"
    );
    assert!(
        !lowered.contains("handle"),
        "streams must inline its handlers"
    );
}

#[test]
fn rc_balanced() {
    on_compiler_stack("rc-balanced", rc_balanced_on_compiler_stack);
}

fn rc_balanced_on_compiler_stack() {
    let root = env!("CARGO_MANIFEST_DIR");
    for dir in ["tests/cases", "tests/cases/run", "examples"] {
        let entries = fs::read_dir(format!("{root}/{dir}")).unwrap();
        for e in entries.flatten() {
            let path = e.path();
            if path.extension().and_then(|s| s.to_str()) != Some("pr") {
                continue;
            }
            let src = fs::read_to_string(&path).unwrap();
            let full = prism::with_prelude(&src);
            if prism::dump("core", &full).is_err() {
                continue;
            }
            if let Err(err) = prism::rc_balanced(&full) {
                panic!("{}: {err}", path.display());
            }
        }
    }
}

// Every successfully checked corpus program crosses the typed elaboration
// boundary. The boundary itself compares the erased tree with its raw
// compatibility input before hashing; this named corpus gate makes that exact
// (and therefore hash) neutrality invariant a permanent test obligation.
#[test]
fn typed_core_erasure_is_corpus_hash_neutral() {
    on_compiler_stack(
        "typed-core-corpus-hash",
        typed_core_erasure_is_corpus_hash_neutral_on_compiler_stack,
    );
}

fn typed_core_erasure_is_corpus_hash_neutral_on_compiler_stack() {
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let full = prism::with_prelude(&src);
        if prism::check(&full).is_err() {
            continue;
        }
        if let Err(error) = prism::dump("core-hash", &full) {
            if matches!(
                error,
                prism::error::Error::TypedCoreEnvironment(_)
                    | prism::error::Error::TypedCoreConstruction(_)
                    | prism::error::Error::TypedCoreVerification(_)
                    | prism::error::Error::TypedCoreErasure(_)
                    | prism::error::Error::TypedCoreSpecialization(_)
            ) {
                panic!("{}: {error}", path.display());
            }
            // Some type-correct negative fixtures intentionally fail a later raw
            // elaboration or backend precondition. They never reach typed Core
            // and therefore have no erasure-neutrality judgment to check.
        }
    }
}

// Singleton list patterns live only here: the formatter prints list patterns
// in Cons form, so the sugar cannot appear in a canonical .pr case.
#[test]
fn singleton_list_pattern() {
    let src = "fn main() =\n  match [7] of\n    [x] => print(x)\n    _ => print(0)\n";
    let run = prism::interpret(&prism::with_prelude(src)).unwrap();
    assert_eq!(run.out.len(), 1);
    assert_eq!(run.out[0].show(), "7");
}

fn corpus_files() -> impl Iterator<Item = PathBuf> {
    let root = env!("CARGO_MANIFEST_DIR");
    ["tests/cases", "tests/cases/run", "examples", "lib"]
        .into_iter()
        .flat_map(move |dir| fs::read_dir(format!("{root}/{dir}")).unwrap())
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("pr"))
}

// Strategy classification snapshot: record which effect-lowering strategy every
// effectful corpus program takes, so a regression that drops a program from a
// fused path onto the free monad (or an improvement that lifts it off) is a
// reviewable diff. The classification is the SAME decision the compiler makes
// (`prism::effect_strategy_full` shares `lower`'s single code path), so it can
// never drift from reality. This is the principled answer to the blind spot that
// let `var` loops ship silently on the whole-program free monad: their slow path
// is now spelled out here for review. Pure (effect-free) programs are omitted to
// keep the manifest about the programs whose fusion actually matters.
#[test]
fn effect_strategy_manifest() {
    on_compiler_stack(
        "effect-strategy-manifest",
        effect_strategy_manifest_on_compiler_stack,
    );
}

fn effect_strategy_manifest_on_compiler_stack() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut lines: Vec<String> = Vec::new();
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let full = prism::with_prelude(&src);
        let Ok(strat) = prism::effect_strategy_full(&full, Path::new(".")) else {
            continue;
        };
        if strat == prism::EffectStrategy::Pure {
            continue;
        }
        let key = path.strip_prefix(root).unwrap_or(&path).display();
        lines.push(format!("{key}: {strat}"));
    }
    lines.sort();
    insta::assert_snapshot!("effect_strategy_manifest", lines.join("\n"));
}

// A program that drops onto the free monad must say so, not fall back silently.
// Here `apply` passes the effectful `risky` as a first-class value and the
// handler does not resume in tail position, so the continuation reifies into EOp
// cells. `effect_warnings_full` shares `lower`'s single code path, so the warning
// it returns is exactly the one a build/run surfaces through the standard
// renderer. This locks both that the fallback warns and the text naming the cause.
#[test]
fn free_monad_fallback_warns() {
    let src = prism::with_prelude(
        "effect Boom\n  boom(Int) : Int\n\
         fn apply(f : (Int) -> Int ! {Boom}, x : Int) : Int ! {Boom} = f(x)\n\
         fn risky(x) =\n  if x == 0 then boom(1) else x\n\
         fn main() =\n  handle apply(risky, 0) with\n    boom(v) resume k => 0 - v\n    return r => r\n",
    );
    let warnings = prism::effect_warnings_full(&src, Path::new(".")).unwrap();
    insta::assert_snapshot!(warnings.join("\n"));
}

// Optimization coverage requirement. Two guarantees the per-program snapshot
// cannot give on its own: (1) breadth -- every named fast path keeps at least one
// live witness in the corpus, so silently losing a whole optimization fails here,
// not just shifts a snapshot line; and (2) the basic-loop invariant -- a canonical
// `var` while-loop must NOT classify as a free-monad strategy, because imperative
// loops have to compile to constant-stack, allocation-free loops. (2) is the
// requirement whose absence let the var-loop regression ship; it fails until the
// var/loop optimization fires and stays a permanent ratchet after.
#[test]
fn optimization_coverage() {
    on_compiler_stack(
        "optimization-coverage",
        optimization_coverage_on_compiler_stack,
    );
}

fn optimization_coverage_on_compiler_stack() {
    let mut seen = std::collections::BTreeSet::new();
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        if let Ok(s) = prism::effect_strategy_full(&prism::with_prelude(&src), Path::new(".")) {
            seen.insert(s);
        }
    }
    for strategy in [
        prism::EffectStrategy::Evidence,
        prism::EffectStrategy::StateFusion,
        prism::EffectStrategy::LocalPartial,
    ] {
        assert!(
            seen.contains(&strategy),
            "no corpus program exercises the `{strategy}` fast path; its gate has no live witness"
        );
    }
    // A basic imperative loop must compile to a loop, never the free monad.
    let loop_prog = prism::with_prelude(
        "fn run(n : Int) : Int =\n  var s := 0\n  var i := 0\n  while i < n do\n    \
         i += 1\n    s += i\n  s\nfn main() = println(run(10))\n",
    );
    let strat = prism::effect_strategy_full(&loop_prog, Path::new(".")).unwrap();
    assert!(
        !matches!(
            strat,
            prism::EffectStrategy::SelectiveFreeMonad
                | prism::EffectStrategy::WholeProgramFreeMonad
        ),
        "a basic `var` while-loop classifies as `{strat}`: imperative loops must not reify \
         into the free monad (O(n) heap allocation and stack overflow)"
    );
}

#[test]
fn fmt_idempotent() {
    on_compiler_stack("fmt-idempotent", fmt_idempotent_on_compiler_stack);
}

fn fmt_idempotent_on_compiler_stack() {
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let Ok(once) = prism::format(&src) else {
            continue;
        };
        let twice = prism::format(&once).unwrap();
        assert_eq!(once, twice, "fmt not idempotent: {}", path.display());
    }
}

// Formatting must preserve meaning, not just be a fixpoint: the desugared core
// of the formatted source has to match the original's. This is what catches a
// sugar marker that round-trips to the wrong tree, which idempotency cannot see.
#[test]
fn fmt_preserves_core() {
    on_compiler_stack("fmt-preserves-core", fmt_preserves_core_on_compiler_stack);
}

fn fmt_preserves_core_on_compiler_stack() {
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let Ok(core) = prism::dump("core", &prism::with_prelude(&src)) else {
            continue;
        };
        let once = prism::format(&src)
            .unwrap_or_else(|e| panic!("{} parses but won't format: {e}", path.display()));
        let formatted_core = prism::dump("core", &prism::with_prelude(&once))
            .unwrap_or_else(|e| panic!("{} lost typeability after fmt: {e}", path.display()));
        assert_eq!(core, formatted_core, "fmt changed core: {}", path.display());
    }
}
