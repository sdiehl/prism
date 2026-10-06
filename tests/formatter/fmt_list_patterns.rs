// List patterns print as list sugar. The grammar expands `[]`, `[x, y]`, and
// `h :: t` into `Nil`/`Cons` while building the surface tree, so the printer
// recovers the sugar from the constructor spine: `Nil` prints as `[]`, a spine
// ending in `Nil` prints in brackets, and any other spine prints with `::`.
// Patterns have no grouping parens, so a cons cell whose operand would need
// them keeps the explicit constructor rather than change meaning.

fn formatted(src: &str) -> String {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
    once
}

fn arms(pats: &[&str]) -> String {
    use std::fmt::Write;
    let mut src = String::from("fn f(v) =\n  match v of\n");
    for (i, p) in pats.iter().enumerate() {
        let _ = writeln!(src, "    {p} => {i}");
    }
    src
}

#[test]
fn list_constructor_patterns_print_as_sugar() {
    let out = formatted(&arms(&[
        "Nil",
        "Cons(x, Nil)",
        "Cons(x, Cons(y, rest))",
        "Cons(Cons(a, Nil), _)",
    ]));
    for want in [
        "[] => 0",
        "[x] => 1",
        "x :: y :: rest => 2",
        "[a] :: _ => 3",
    ] {
        assert!(out.contains(want), "missing `{want}`:\n{out}");
    }
}

#[test]
fn cells_that_would_need_parens_keep_the_constructor() {
    let out = formatted(&arms(&["Cons(a :: _, r)", "Cons(x, A | B)", "[1 | 2]"]));
    for want in [
        "Cons(a :: _, r) => 0",
        "Cons(x, A | B) => 1",
        "[1 | 2] => 2",
    ] {
        assert!(out.contains(want), "missing `{want}`:\n{out}");
    }
}

// List expressions keep the author's spelling; only patterns canonicalize.
#[test]
fn list_expressions_keep_their_spelling() {
    let out = formatted("fn f(xs) = (Cons(1, xs), 1 :: xs, [1, 2, 3])\n");
    assert!(
        out.contains("(Cons(1, xs), 1 :: xs, [1, 2, 3])"),
        "list expression spelling was changed:\n{out}"
    );
}
