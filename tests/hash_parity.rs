// The content-hash parity gate: the load-bearing invariant behind
// content-addressed Core. A definition's hash is meant to commit to everything
// its compilation reads, so *equal hash implies a byte-identical compiled
// artifact*, and any codegen-visible change must move the hash. That is the
// content-addressed analogue of the interpreter/native parity oracle: there the
// claim is "same Core, same output on every backend"; here it is "same hash, same
// emitted artifact," together with its dual "different artifact, different hash."
//
// The artifact compared is the emitted LLVM IR text (`emit_ir`), which is finer
// than stdout: it reflects codegen choices (rc insertion, lowering) that never
// reach the terminal, so it catches a hash that agrees on behavior but disagrees
// on compiled form. Without this coupling the hash is only asserted-correct
// against itself (`core_hash.rs`); here it is checked against the thing it claims
// to name.
//
// Three properties. Soundness over real programs: emission is deterministic and
// reformatting (a semantics- and name-preserving reprint) moves neither the
// artifact nor the hash. Soundness with teeth: two programs differing only in a
// local binder name hash identically, so their compiled artifact must be
// byte-identical too. Completeness with teeth: a codegen-visible edit must move
// the hash. The metadata inputs fip/borrow are committed at the hash level in
// `core_hash.rs`; on the current backend they are conservatively folded even
// where they do not move the IR, so they are not re-tested here.
//
// Gated on `feature = "native"` because `emit_ir` is; no C compiler is needed
// (the textual emitter produces IR without invoking clang), so this runs wherever
// the native backend is compiled in. A small fixed set of committed examples
// gives breadth without the per-program interpreter filtering the runnable-corpus
// oracle pays; the curated tables carry the teeth and are cheap.
#![cfg(feature = "native")]

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use prism::{emit_ir, format, with_prelude};

// A spread of committed examples: arithmetic recursion, higher-order functions,
// dictionary-passing type classes, algebraic-effect handlers, list
// comprehensions. Enough shape variety that reformatting exercises real codegen,
// not just a toy.
const EXAMPLES: &[&str] = &["collatz", "curry", "classes", "eff_state", "comprehension"];

// The emitted LLVM IR for a full (prelude-included) program: the compiled
// artifact this gate holds the hash against.
fn ir(full: &str) -> String {
    emit_ir(full).unwrap_or_else(|e| panic!("emit_ir failed: {e}"))
}

// The per-definition content hashes, keyed by name, over a full program.
fn hashes(full: &str) -> BTreeMap<String, String> {
    prism::dump("core-hash", full)
        .expect("core-hash dump")
        .lines()
        .filter_map(|l| {
            l.split_once("  ")
                .map(|(h, n)| (n.to_string(), h.to_string()))
        })
        .collect()
}

fn example(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("examples/{name}.pr"));
    with_prelude(&fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {name}: {e}")))
}

// Soundness over real programs. Emission is deterministic (the same source yields
// byte-identical IR twice, without which content addressing is impossible), and
// a reformat moves neither the artifact nor the hash. So trivia reaches neither
// the compiled form nor the identity, checked end to end against real codegen.
#[test]
fn emission_is_deterministic_and_reformatting_is_invisible() {
    for name in EXAMPLES {
        let full = example(name);
        let base = ir(&full);
        assert_eq!(base, ir(&full), "{name}: IR emission is nondeterministic");

        let reflowed = format(&full).unwrap_or_else(|e| panic!("{name}: format: {e}"));
        assert_eq!(
            base,
            ir(&reflowed),
            "{name}: reformatting moved the emitted IR"
        );
        assert_eq!(
            hashes(&full),
            hashes(&reflowed),
            "{name}: reformatting moved a content hash"
        );
    }
}

// Soundness with teeth: two programs whose only difference is the spelling of a
// local binder hash identically (the scheme alpha-normalizes binders), so the
// invariant demands their compiled artifact be byte-identical too. If the hash
// claimed these equal while the IR differed, it would be unsound, naming a
// behavior it does not actually pin.
#[test]
fn renaming_a_local_preserves_hash_and_artifact() {
    let pairs = [
        (
            "fn k(n) =\n  let x = n + 1\n  x * x\nfn main() = println(k(3))",
            "fn k(n) =\n  let y = n + 1\n  y * y\nfn main() = println(k(3))",
            "k",
        ),
        (
            "fn g(a, b) =\n  let s = a + b\n  s * s\nfn main() = println(g(2, 3))",
            "fn g(a, b) =\n  let total = a + b\n  total * total\nfn main() = println(g(2, 3))",
            "g",
        ),
    ];
    for (a, b, def) in pairs {
        let (fa, fb) = (with_prelude(a), with_prelude(b));
        assert_eq!(
            hashes(&fa)[def],
            hashes(&fb)[def],
            "renaming a local moved the hash of `{def}`"
        );
        assert_eq!(
            ir(&fa),
            ir(&fb),
            "equal hash but the emitted IR differs for `{def}`; the hash is unsound"
        );
    }
}

// Completeness with teeth: a codegen-visible edit must move the hash. Each pair
// holds every top-level name fixed and changes only the body, so the hash maps
// are compared key-for-key. The IR-inequality assertion is a guard on the test
// itself (it proves the edit really is visible to codegen), and the
// hash-inequality assertion is the invariant: an artifact change the hash failed
// to notice would be a silent-miscompile hole, exactly the class content
// addressing must never admit.
#[test]
fn a_codegen_visible_edit_moves_the_hash() {
    const BASE: &str = "fn f(n) = n + 1\nfn main() = println(f(3))";
    let edits = [
        ("constant", "fn f(n) = n + 2\nfn main() = println(f(3))"),
        ("operator", "fn f(n) = n - 1\nfn main() = println(f(3))"),
        (
            "structure",
            "fn f(n) = (n + 1) * 2\nfn main() = println(f(3))",
        ),
        (
            "control flow",
            "fn f(n) = if n == 0 then 1 else n + 1\nfn main() = println(f(3))",
        ),
    ];
    let base = with_prelude(BASE);
    let (base_ir, base_hashes) = (ir(&base), hashes(&base));
    for (what, edited) in edits {
        let fe = with_prelude(edited);
        assert_ne!(
            base_ir,
            ir(&fe),
            "the {what} edit is not visible to codegen; the test guard is stale"
        );
        assert_ne!(
            base_hashes["f"],
            hashes(&fe)["f"],
            "the {what} edit changed the artifact but not the hash of `f`; a silent-miscompile hole"
        );
    }
}
