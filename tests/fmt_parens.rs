// Paren-preservation across operator precedence and associativity. The grammar
// makes every comparison operator one non-associative level (`Cmp: Add CmpOp
// Add`) and `-`/`/`/`%` non-associative on the right, so the formatter must keep
// the parens these constructs require or its output stops parsing. `format`
// reparses its own output, so a dropped-but-required paren surfaces as an Err
// here. Each case also pins idempotence.
fn roundtrips(src: &str) {
    let once = tiny_prism::format(src).expect("input must parse");
    let twice = tiny_prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
}

#[test]
fn nested_comparisons_keep_parens() {
    // Comparisons never associate; both operand positions must stay wrapped.
    for src in [
        "fn f(a, b, c) = a == (b == c)\n",
        "fn f(a, b, c) = (a == b) == c\n",
        "fn f(a, b, c) = a < (b < c)\n",
        "fn f(a, b, c) = a == (b < c)\n",
        "fn f(a, b, c) = (a < b) == c\n",
        "fn f(a, b, c) = a /= (b >= c)\n",
        "fn f(a, b, c) = a ==. (b <. c)\n",
    ] {
        roundtrips(src);
    }
}

#[test]
fn right_nested_non_associative_arith_keeps_parens() {
    // `-`/`/`/`%` are non-associative on the right: dropping these parens would
    // reparse to a different (left-nested) tree.
    for src in [
        "fn f(a, b, c) = a - (b - c)\n",
        "fn f(a, b, c) = a - (b + c)\n",
        "fn f(a, b, c) = a / (b / c)\n",
        "fn f(a, b, c) = a % (b % c)\n",
        "fn f(a, b, c) = a *. (b +. c)\n",
    ] {
        roundtrips(src);
    }
}
