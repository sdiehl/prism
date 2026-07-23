// Deep-nesting regression: a long statement block parses into a right-nested
// `Let` chain, so each front-end pass recurses once per statement. The guarded
// recursions (desugar's rewrite, the checker's per-node walk, elaboration, the
// typed-Core builder, its zonker, and the typed verifier) grow stack segments
// on demand, so a generated file of a few thousand sequential `let`s compiles
// instead of overflowing the stack; this pins that. Release-only: debug frames
// are several times fatter and some unguarded analysis walks still bound depth
// there, which is the remaining bounded-traversal work, so the debug profile
// asserts nothing.
#![cfg(not(debug_assertions))]

use std::fmt::Write as _;

// Comfortably past the old release cliff (~1000 binders overflowed) while
// keeping the known-quadratic elaboration cost to well under a second.
const DEEP_LETS: usize = 2000;

fn deep_program(n: usize) -> String {
    let mut src = String::from("fn main() : Int =\n");
    for i in 0..n {
        let _ = writeln!(src, "  let x{i} = {i}");
    }
    let _ = writeln!(src, "  x0 + x{}", n - 1);
    src
}

#[test]
fn thousands_of_sequential_lets_compile() {
    let src = deep_program(DEEP_LETS);
    // `check` drives lex through elaboration (including typed-Core construction
    // and verification), which covers every guarded recursion.
    prism::check(&src).expect("a deep statement block compiles without overflowing");
}
