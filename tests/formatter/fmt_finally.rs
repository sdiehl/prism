// Canonical layout for a handler's cleanup clause. `finally` is a contextual
// word: it is a clause head only directly under `with`, so an ordinary binding
// or call spelled `finally` elsewhere keeps its meaning. The clause binds
// nothing and prints last among the clauses, in both the offside and the
// braced handler shape.
//
// Each case asserts the exact layout plus the two invariants a reformat rests
// on: formatting is idempotent, and the output reparses to the same span-stripped
// meaning.

use prism::parse::parse;
use prism::syntax::ast::{Expr, HandlerArm};

use super::{assert_format, assert_format_semantics, ast_no_spans};

const OFFSIDE: &str = r#"effect Ask
  ask() : Int

fn go() =
  handle ask() + 1 with
    return x => x
    ask() resume k => k(41)
    finally => println("cleanup")
"#;

const BRACED: &str = r#"fn go() = handle ask() with { ask() resume k => k(1), finally => println("cleanup") }
"#;

const BRACED_CANONICAL: &str = r#"fn go() =
  handle ask() with
    ask() resume k => k(1)
    finally => println("cleanup")
"#;

#[test]
fn offside_cleanup_clause_is_a_fixpoint() {
    assert_format_semantics(OFFSIDE, OFFSIDE);
}

// Written first, with a comment above it, the clause moves last and keeps the
// comment. Arm order is the one thing the move changes, so only the layout and
// idempotence are asserted.
#[test]
fn cleanup_clause_prints_last() {
    let src = r#"fn go() =
  handle ask() with
    -- release
    finally => println("cleanup")
    return x => x
    ask() resume k => k(1)
"#;
    let want = r#"fn go() =
  handle ask() with
    return x => x
    ask() resume k => k(1)
    -- release
    finally => println("cleanup")
"#;
    assert_format(src, want);
}

// The braced spelling is accepted on input and printed offside, the one layout
// every handler gets.
#[test]
fn braced_cleanup_clause_lays_out_offside() {
    assert_format_semantics(BRACED, BRACED_CANONICAL);
}

// A cleanup clause whose body is a block lays out offside under its own head.
#[test]
fn block_cleanup_body_lays_out_offside() {
    let src = r#"fn go() =
  handle ask() with
    ask() resume k => k(1)
    finally =>
      println("a")
      println("b")
"#;
    assert_format_semantics(src, src);
}

// The parser produces the dedicated clause, not an operation clause named
// `finally`, and only under `with`.
#[test]
fn cleanup_clause_parses_as_its_own_arm() {
    let parsed = parse(BRACED).expect("must parse");
    let body = parsed.program.fns[0].body.node.clone();
    let Expr::Handle(_, arms, _) = body else {
        panic!("expected a handler body");
    };
    assert!(matches!(arms[1], HandlerArm::Finally(_)));
    assert!(!matches!(arms[0], HandlerArm::Finally(_)));

    let plain = r"fn finally() = 1
fn go() = finally()
";
    assert_eq!(
        ast_no_spans(plain),
        ast_no_spans(&prism::format(plain).unwrap())
    );
}
