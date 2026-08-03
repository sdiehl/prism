// Paren-preservation across operator precedence and associativity. The grammar
// makes every comparison operator one non-associative level (`Cmp: Add CmpOp
// Add`) and `-`/`/`/`%` non-associative on the right, so the formatter must keep
// the parens these constructs require or its output stops parsing. `format`
// reparses its own output, so a dropped-but-required paren surfaces as an Err
// here. Each case also checks idempotence.
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
    SubRightSub,
    SubRightAdd,
    DivRightDiv,
    RemRightRem,
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
            Self::SubRightSub => "fn f(a, b, c) = a - (b - c)\n",
            Self::SubRightAdd => "fn f(a, b, c) = a - (b + c)\n",
            Self::DivRightDiv => "fn f(a, b, c) = a / (b / c)\n",
            Self::RemRightRem => "fn f(a, b, c) = a % (b % c)\n",
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
        ParensCase::SubRightSub,
        ParensCase::SubRightAdd,
        ParensCase::DivRightDiv,
        ParensCase::RemRightRem,
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

#[test]
fn typed_hole_restores_and_roundtrips() {
    let src = "fn main() : Int = ?todo\n";
    let out = prism::format(src).expect("typed hole must format");
    assert!(out.contains("?todo"), "typed hole spelling lost: {out:?}");
    roundtrips(src);
}

// The three loosest levels of the grammar, tightest last: `??` (right
// associative), `|>` (left associative), and `>>`/`<<` (left associative), each
// admitting only the next tighter level as an operand. Idempotence and reparsing
// cannot see a mistake here, because dropping a required paren yields output that
// still parses and still formats to itself; it just parses to a different tree.
// So each case pins the exact text, and the pairs are chosen so that one member
// must keep its parens and the other must drop them.
#[derive(Clone, Copy, Debug)]
enum PrecCase {
    DefaultLeftNested,
    DefaultRightNested,
    PipeLeftNested,
    PipeRightNested,
    ComposeLeftNested,
    ComposeRightNested,
    DefaultUnderPipe,
    DefaultInPipeStage,
    ComposeUnderDefault,
    ComposeInPipeStage,
}

impl PrecCase {
    const fn src(self) -> &'static str {
        match self {
            Self::DefaultLeftNested => "fn f(a, b, c) = (a ?? b) ?? c\n",
            Self::DefaultRightNested => "fn f(a, b, c) = a ?? (b ?? c)\n",
            Self::PipeLeftNested => "fn f(x, k, m) = (x |> k) |> m\n",
            Self::PipeRightNested => "fn f(x, k, m) = x |> (k |> m)\n",
            Self::ComposeLeftNested => "fn f(p, q, r) = (p >> q) >> r\n",
            Self::ComposeRightNested => "fn f(p, q, r) = p >> (q >> r)\n",
            Self::DefaultUnderPipe => "fn f(a, b, k) = (a ?? b) |> k\n",
            Self::DefaultInPipeStage => "fn f(a, b, k) = a |> (b ?? k)\n",
            Self::ComposeUnderDefault => "fn f(p, q, r) = (p >> q) ?? r\n",
            Self::ComposeInPipeStage => "fn f(x, k, m) = x |> (k >> m)\n",
        }
    }

    // The parens the meaning depends on stay; the ones associativity already
    // implies go away.
    const fn expect(self) -> &'static str {
        match self {
            Self::DefaultLeftNested => "fn f(a, b, c) = (a ?? b) ?? c\n",
            Self::DefaultRightNested => "fn f(a, b, c) = a ?? b ?? c\n",
            Self::PipeLeftNested => "fn f(x, k, m) = x |> k |> m\n",
            Self::PipeRightNested => "fn f(x, k, m) = x |> (k |> m)\n",
            Self::ComposeLeftNested => "fn f(p, q, r) = p >> q >> r\n",
            Self::ComposeRightNested => "fn f(p, q, r) = p >> (q >> r)\n",
            Self::DefaultUnderPipe => "fn f(a, b, k) = (a ?? b) |> k\n",
            Self::DefaultInPipeStage => "fn f(a, b, k) = a |> (b ?? k)\n",
            Self::ComposeUnderDefault => "fn f(p, q, r) = p >> q ?? r\n",
            Self::ComposeInPipeStage => "fn f(x, k, m) = x |> k >> m\n",
        }
    }
}

#[rstest]
fn low_precedence_operands_keep_their_meaning(
    #[values(
        PrecCase::DefaultLeftNested,
        PrecCase::DefaultRightNested,
        PrecCase::PipeLeftNested,
        PrecCase::PipeRightNested,
        PrecCase::ComposeLeftNested,
        PrecCase::ComposeRightNested,
        PrecCase::DefaultUnderPipe,
        PrecCase::DefaultInPipeStage,
        PrecCase::ComposeUnderDefault,
        PrecCase::ComposeInPipeStage
    )]
    case: PrecCase,
) {
    let out = prism::format(case.src()).expect("input must parse");
    assert_eq!(out, case.expect(), "from {:?}", case.src());
    roundtrips(case.src());
}

// Equal-precedence nesting inside the binary ladder. Reparsing and idempotence
// are both blind here for the same reason as above: dropping a required paren
// yields output that parses, formats to itself, and simply denotes a different
// tree. Over Float that different tree is a different number, since neither
// addition nor multiplication reassociates, so the operands are float literals
// and each case pins the exact text. The pairs are chosen so one member must
// keep its parens (right-nesting, which the reparse would regroup) and the other
// must drop them (left-nesting, which is what the reparse already yields), with
// `^` reversed because it is the one right-associative level.
#[derive(Clone, Copy, Debug)]
enum AssocCase {
    AddOfSub,
    AddOfAdd,
    SubOfSub,
    MulOfMul,
    MulOfDiv,
    DivOfMul,
    AddLeftNested,
    MulLeftNested,
    PowRightNested,
    PowLeftNested,
}

impl AssocCase {
    const fn src(self) -> &'static str {
        match self {
            Self::AddOfSub => "fn f() = 1.0 + (2.0 - 3.0)\n",
            Self::AddOfAdd => "fn f() = 1.0 + (2.0 + 3.0)\n",
            Self::SubOfSub => "fn f() = 1.0 - (2.0 - 3.0)\n",
            Self::MulOfMul => "fn f() = 1.0 * (2.0 * 3.0)\n",
            Self::MulOfDiv => "fn f() = 1.0 * (2.0 / 3.0)\n",
            Self::DivOfMul => "fn f() = 1.0 / (2.0 * 3.0)\n",
            Self::AddLeftNested => "fn f() = (1.0 + 2.0) + 3.0\n",
            Self::MulLeftNested => "fn f() = (1.0 * 2.0) * 3.0\n",
            Self::PowRightNested => "fn f() = 2.0 ^ (3.0 ^ 4.0)\n",
            Self::PowLeftNested => "fn f() = (2.0 ^ 3.0) ^ 4.0\n",
        }
    }

    const fn expect(self) -> &'static str {
        match self {
            Self::AddOfSub => "fn f() = 1.0 + (2.0 - 3.0)\n",
            Self::AddOfAdd => "fn f() = 1.0 + (2.0 + 3.0)\n",
            Self::SubOfSub => "fn f() = 1.0 - (2.0 - 3.0)\n",
            Self::MulOfMul => "fn f() = 1.0 * (2.0 * 3.0)\n",
            Self::MulOfDiv => "fn f() = 1.0 * (2.0 / 3.0)\n",
            Self::DivOfMul => "fn f() = 1.0 / (2.0 * 3.0)\n",
            Self::AddLeftNested => "fn f() = 1.0 + 2.0 + 3.0\n",
            Self::MulLeftNested => "fn f() = 1.0 * 2.0 * 3.0\n",
            Self::PowRightNested => "fn f() = 2.0 ^ 3.0 ^ 4.0\n",
            Self::PowLeftNested => "fn f() = (2.0 ^ 3.0) ^ 4.0\n",
        }
    }
}

#[rstest]
fn equal_precedence_nesting_keeps_its_tree(
    #[values(
        AssocCase::AddOfSub,
        AssocCase::AddOfAdd,
        AssocCase::SubOfSub,
        AssocCase::MulOfMul,
        AssocCase::MulOfDiv,
        AssocCase::DivOfMul,
        AssocCase::AddLeftNested,
        AssocCase::MulLeftNested,
        AssocCase::PowRightNested,
        AssocCase::PowLeftNested
    )]
    case: AssocCase,
) {
    let out = prism::format(case.src()).expect("input must parse");
    assert_eq!(out, case.expect(), "from {:?}", case.src());
    roundtrips(case.src());
}
