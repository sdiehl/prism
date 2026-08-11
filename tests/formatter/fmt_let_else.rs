// Canonical layout for the early-return binding. The fallback shares the
// binding's line while it fits, because the whole point of the form is that the
// failure case is small enough not to interrupt the reading; past that it lays
// out offside under its own `else`, the shape `transact` already uses for the
// same keyword. Both spellings are accepted on input and only one is printed, so
// the choice is the formatter's and not the author's.
//
// Each case asserts the exact layout plus the two invariants a reformat rests
// on: formatting is idempotent, and the output reparses to the same span-stripped
// meaning.

use prism::parse::parse;
use prism::syntax::ast::{Expr, Pattern};

use super::assert_format_semantics;

const INLINE: &str = "fn f(o : Option(Int)) : Int =\n  let Some(x) = o else 0\n  x + 1\n";

const OFFSIDE: &str = "fn f(o : Option(Int)) : Int =\n  let Some(x) = o\n  else\n    let d = 100\n    d * 2\n  x + 1\n";

// A short fallback stays on the binding's line whichever way it was written.
#[test]
fn short_fallback_stays_inline() {
    assert_format_semantics(INLINE, INLINE);
}

#[test]
fn offside_short_fallback_collapses() {
    assert_format_semantics(
        "fn f(o : Option(Int)) : Int =\n  let Some(x) = o\n  else\n    0\n  x + 1\n",
        INLINE,
    );
}

// A fallback that is itself a block cannot share the line, and prints under its
// own `else` whichever way it was written.
#[test]
fn block_fallback_lays_out_offside() {
    assert_format_semantics(OFFSIDE, OFFSIDE);
}

#[test]
fn trailing_else_block_is_reseated() {
    assert_format_semantics(
        "fn f(o : Option(Int)) : Int =\n  let Some(x) = o else\n    let d = 100\n    d * 2\n  x + 1\n",
        OFFSIDE,
    );
}

// A comment inside the fallback is why the inline form is guarded at all:
// collapsing onto the binding's line has nowhere to put it, so the presence of a
// comment keeps the fallback offside rather than relocating the comment.
#[test]
fn a_comment_in_the_fallback_keeps_it_offside() {
    let src = "fn f(o : Option(Int)) : Int =\n  let Some(x) = o\n  else\n    -- the pattern did not match\n    0\n  x + 1\n";
    assert_format_semantics(src, src);
}

// The restored surface is a binding, not the two-arm match it expands to: the
// formatter has to recognize the wildcard fallback arm to tell the form apart
// from the `?` expansion, whose second arm is an `Err` constructor.
#[test]
fn the_wildcard_arm_is_what_distinguishes_the_form() {
    let ast = prism::dump("ast", INLINE).expect("must parse");
    assert!(ast.contains("synth: true"), "{ast}");
    let program = parse(INLINE).expect("must parse").program;
    let body = &program.fns[0].body;
    let Expr::Match(_, arms) = &body.node else {
        panic!("expected the binding to expand to a match, got: {body:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(arms[1].pat.node, Pattern::Wild), "{arms:?}");
}
