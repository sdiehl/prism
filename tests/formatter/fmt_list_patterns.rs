// Known limitation, pinned deliberately so it cannot change unnoticed.
//
// `[]` and `[x, y]` are list *pattern* sugar that the grammar expands into
// `Nil`/`Cons` while building the surface tree. `Pattern` has no `List`
// variant, so by the time the printer runs the sugar is gone and there is
// nothing to print it back from. Expression position is unaffected: `Expr` does
// have a `List` variant, so `[1, 2]` survives a format there.
//
// The result is that formatting rewrites list patterns into constructor
// patterns. That reparses and means the same thing, so it does not break the
// round-trip law the formatter is held to, but it is a source rewrite rather
// than a layout change: a file cannot both be `prism fmt --check` clean and
// spell a list pattern. That is why the parser corpus no longer carries one.
//
// These tests assert the current behavior, not the desired one. Giving
// `Pattern` a `List` variant is what fixes it, and when that lands these
// assertions fail and must be inverted.

fn formatted(src: &str) -> String {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
    once
}

#[test]
fn list_patterns_are_rewritten_into_constructor_patterns() {
    let out = formatted("fn f(v) =\n  match v of\n    [] => 0\n    [x, y] => 1\n    _ => 2\n");
    assert!(
        out.contains("Nil => 0"),
        "expected the empty-list pattern to print as `Nil`:\n{out}"
    );
    assert!(
        out.contains("Cons(x, Cons(y, Nil)) => 1"),
        "expected the list pattern to print as nested `Cons`:\n{out}"
    );
    assert!(
        !out.contains("[]") && !out.contains("[x, y]"),
        "list pattern sugar unexpectedly survived formatting:\n{out}"
    );
}

// The counterpart that must keep working: list *expressions* have a surface
// representation, so formatting leaves them spelled as written.
#[test]
fn list_expressions_keep_their_sugar() {
    let out = formatted("fn f() = [1, 2, 3]\n");
    assert!(
        out.contains("[1, 2, 3]"),
        "list expression sugar was lost:\n{out}"
    );
}
