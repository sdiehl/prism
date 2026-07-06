// Paren-preservation across operator precedence and associativity. The grammar
// makes every comparison operator one non-associative level (`Cmp: Add CmpOp
// Add`) and `-`/`/`/`%` non-associative on the right, so the formatter must keep
// the parens these constructs require or its output stops parsing. `format`
// reparses its own output, so a dropped-but-required paren surfaces as an Err
// here. Each case also pins idempotence.
use rstest::rstest;

fn roundtrips(src: &str) {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
}

#[derive(Clone, Copy, Debug)]
enum ParensCase {
    EqRightEq,
    EqLeftEq,
    LtRightLt,
    EqRightLt,
    LtLeftEq,
    NeqRightGe,
    FloatEqRightLt,
    SubRightSub,
    SubRightAdd,
    DivRightDiv,
    RemRightRem,
    FloatMulRightAdd,
    UnaryVariable,
    UnaryCall,
    UnaryProjection,
    UnaryUnary,
    UnaryBinaryOperand,
    UnaryTimes,
    BinaryMinusUnary,
    NegativeInt,
    NegativeFloat,
    IntSeparators,
    FloatSeparators,
    ExponentSign,
}

impl ParensCase {
    const fn src(self) -> &'static str {
        match self {
            Self::EqRightEq => "fn f(a, b, c) = a == (b == c)\n",
            Self::EqLeftEq => "fn f(a, b, c) = (a == b) == c\n",
            Self::LtRightLt => "fn f(a, b, c) = a < (b < c)\n",
            Self::EqRightLt => "fn f(a, b, c) = a == (b < c)\n",
            Self::LtLeftEq => "fn f(a, b, c) = (a < b) == c\n",
            Self::NeqRightGe => "fn f(a, b, c) = a /= (b >= c)\n",
            Self::FloatEqRightLt => "fn f(a, b, c) = a ==. (b <. c)\n",
            Self::SubRightSub => "fn f(a, b, c) = a - (b - c)\n",
            Self::SubRightAdd => "fn f(a, b, c) = a - (b + c)\n",
            Self::DivRightDiv => "fn f(a, b, c) = a / (b / c)\n",
            Self::RemRightRem => "fn f(a, b, c) = a % (b % c)\n",
            Self::FloatMulRightAdd => "fn f(a, b, c) = a *. (b +. c)\n",
            Self::UnaryVariable => "fn f(x) = -x\n",
            Self::UnaryCall => "fn f(g, x) = -g(x)\n",
            Self::UnaryProjection => "fn f(p) = -p.field\n",
            Self::UnaryUnary => "fn f(x) = - -x\n",
            Self::UnaryBinaryOperand => "fn f(a, b) = -(a + b)\n",
            Self::UnaryTimes => "fn f(x) = -x * 3\n",
            Self::BinaryMinusUnary => "fn f(a, b) = a - -b\n",
            Self::NegativeInt => "fn f() = -5\n",
            Self::NegativeFloat => "fn f() = -1.5\n",
            Self::IntSeparators => "fn f() = 1_000_000\n",
            Self::FloatSeparators => "fn f() = 1_000.000_5\n",
            Self::ExponentSign => "fn f() = 1e-25\n",
        }
    }
}

#[rstest]
fn parens_and_unary_cases_roundtrip(
    #[values(
        ParensCase::EqRightEq,
        ParensCase::EqLeftEq,
        ParensCase::LtRightLt,
        ParensCase::EqRightLt,
        ParensCase::LtLeftEq,
        ParensCase::NeqRightGe,
        ParensCase::FloatEqRightLt,
        ParensCase::SubRightSub,
        ParensCase::SubRightAdd,
        ParensCase::DivRightDiv,
        ParensCase::RemRightRem,
        ParensCase::FloatMulRightAdd,
        ParensCase::UnaryVariable,
        ParensCase::UnaryCall,
        ParensCase::UnaryProjection,
        ParensCase::UnaryUnary,
        ParensCase::UnaryBinaryOperand,
        ParensCase::UnaryTimes,
        ParensCase::BinaryMinusUnary,
        ParensCase::NegativeInt,
        ParensCase::NegativeFloat,
        ParensCase::IntSeparators,
        ParensCase::FloatSeparators,
        ParensCase::ExponentSign
    )]
    case: ParensCase,
) {
    roundtrips(case.src());
}

#[test]
fn unary_minus_spacing_and_separator_grouping_are_exact() {
    assert_eq!(
        prism::format("fn f(x) = - -x\n").unwrap(),
        "fn f(x) = - -x\n"
    );
    assert_eq!(
        prism::format("fn f() = 1_000_000\n").unwrap(),
        "fn f() = 1_000_000\n"
    );
}

#[test]
fn path_update_modify_restores_tilde() {
    // The `~` modify operator, on its own and mixed with `=`, must survive
    // formatting: both sigils restored and the whole form idempotent.
    let src = "fn f(p) = { p | hp ~ heal, name = \"x\" }\n";
    let out = prism::format(src).expect("input must parse");
    assert!(out.contains('~'), "modify sigil lost: {out:?}");
    assert!(out.contains(" = "), "set sigil lost: {out:?}");
    roundtrips(src);
}

#[test]
fn path_update_prism_restores() {
    // The `?Ctor` prism step survives formatting, with its field tail and mixed
    // with `each`, and the form is idempotent.
    let src =
        "fn f(s, xs) =\n  ({ s | ?Circle.radius ~ double }, { xs | each.?Square.side = 0 })\n";
    let out = prism::format(src).expect("input must parse");
    assert!(out.contains("?Circle.radius"), "prism step lost: {out:?}");
    assert!(
        out.contains("each.?Square.side"),
        "each+prism lost: {out:?}"
    );
    roundtrips(src);
}

#[test]
fn read_path_restores() {
    // The `s.[ path ]` read form survives formatting across the step vocabulary,
    // and the form is idempotent.
    let src = "fn f(ps, s) =\n  (ps.[(each where alive).hp], s.[each.?Circle.radius])\n";
    let out = prism::format(src).expect("input must parse");
    assert!(
        out.contains(".[(each where alive).hp]"),
        "read fold lost: {out:?}"
    );
    assert!(
        out.contains(".[each.?Circle.radius]"),
        "read prism lost: {out:?}"
    );
    roundtrips(src);
}

#[test]
fn path_update_where_restores() {
    // The `(each where p)` filter survives formatting, on its own and composed
    // deep in a path, and the form is idempotent.
    let src = "fn f(ps, w) =\n  ({ ps | (each where alive).hp ~ heal }, { w | party.(each where alive).bag.each.count = 0 })\n";
    let out = prism::format(src).expect("input must parse");
    assert!(
        out.contains("(each where alive)"),
        "where filter lost: {out:?}"
    );
    assert!(
        out.contains("party.(each where alive).bag"),
        "composed where lost: {out:?}"
    );
    roundtrips(src);
}

#[test]
fn path_update_index_restores() {
    // The `[i]` index step survives formatting: postfix with no dot, leading, and
    // composed with field and `each` steps, and the form is idempotent.
    let src = "fn f(xs, w) =\n  ({ xs | [0].x = 1, [i].y ~ g }, { w | party[0].each.hp = 0 })\n";
    let out = prism::format(src).expect("input must parse");
    assert!(out.contains("[0].x"), "index step lost: {out:?}");
    assert!(out.contains("party[0].each.hp"), "index+each lost: {out:?}");
    roundtrips(src);
}

#[test]
fn path_update_each_restores() {
    // The `each` step survives formatting at every depth, mixed with fields and
    // both operators, and the form is idempotent.
    let src = "fn f(w) = { w | party.each.hp ~ heal, party.each.bag.each.count = 0, turn = 2 }\n";
    let out = prism::format(src).expect("input must parse");
    assert!(out.contains("party.each.hp"), "each step lost: {out:?}");
    assert!(out.contains("bag.each.count"), "nested each lost: {out:?}");
    roundtrips(src);
}
