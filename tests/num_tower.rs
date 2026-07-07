// The numerical tower: one operator spelling per operation, the
// lane chosen by the type and resolved entirely at compile time. These pin the
// two contracts that make the tower pleasant rather than Perl: the polymorphic
// surface (generic `Num`/`Div` code, `Float` on the plain operators, literals
// that adopt their context) accepts what it should, and the error surface reads
// as a lane story, never as an unresolved-dictionary dump. Runtime behavior is
// pinned by the parity oracle; these are the typing-side gates.

use prism::{check, interpret, with_prelude};
use rstest::rstest;

fn accepts(src: &str) {
    let full = with_prelude(src);
    check(&full).unwrap_or_else(|e| panic!("should type-check, got: {e}\n---\n{src}"));
}

fn rejection(src: &str) -> String {
    let full = with_prelude(src);
    check(&full).expect_err("should be rejected").to_string()
}

fn output(src: &str) -> String {
    let full = with_prelude(src);
    interpret(&full).expect("should run").term
}

#[derive(Clone, Copy, Debug)]
enum AcceptCase {
    FloatLerp,
    GenericNum,
    GenericDiv,
    GenericNegate,
    FloatPlainArithmetic,
    FloatPlainRemainder,
    I64LiteralContext,
    I64ListLiteralContext,
}

impl AcceptCase {
    const fn src(self) -> &'static str {
        match self {
            Self::FloatLerp => {
                "fn lerp(a : Float, b : Float, t : Float) : Float = a + (b - a) * t\n"
            }
            Self::GenericNum => "fn dbl(x : a) : a given Num(a) = x + x\n",
            Self::GenericDiv => "fn quot(x : a, y : a) : a given Div(a) = x / y\n",
            Self::GenericNegate => "fn flip_sign(x : a) : a given Num(a) = -x\n",
            Self::FloatPlainArithmetic => {
                "fn f(a : Float, b : Float) : Float = a + b - a * b / b\n"
            }
            Self::FloatPlainRemainder => "fn g(a : Float, b : Float) : Float = a % b\n",
            Self::I64LiteralContext => "fn f(x : I64) : I64 = x\nfn main() = println(show(f(7)))\n",
            Self::I64ListLiteralContext => {
                "fn sums(xs : List(I64)) : I64 = foldl(\\(a, x) -> a + x, 0i64, xs)\n\
                 fn main() = println(show(sums(([1, 2, 3] : List(I64)))))\n"
            }
        }
    }
}

#[rstest]
fn numerical_tower_accepts_expected_programs(
    #[values(
        AcceptCase::FloatLerp,
        AcceptCase::GenericNum,
        AcceptCase::GenericDiv,
        AcceptCase::GenericNegate,
        AcceptCase::FloatPlainArithmetic,
        AcceptCase::FloatPlainRemainder,
        AcceptCase::I64LiteralContext,
        AcceptCase::I64ListLiteralContext
    )]
    case: AcceptCase,
) {
    accepts(case.src());
}

// `Float` comparisons join the plain operator tower too; the old dot spellings
// stay byte-equivalent deprecated aliases, not the only float comparison path.
#[test]
fn float_takes_the_plain_comparisons() {
    let prog = "fn main() =\n  \
                println(show(1.0 < 2.0))\n  \
                println(show(2.0 <= 2.0))\n  \
                println(show(3.0 > 2.0))\n  \
                println(show(3.0 >= 3.0))\n";
    assert_eq!(output(prog), "true\ntrue\ntrue\ntrue\n");
}

// A polymorphic `Ord` body uses the same surface comparison spelling for
// primitive and dictionary-backed lanes.
#[test]
fn generic_ord_comparisons_check_at_every_lane() {
    let prog = "fn lt(x : a, y : a) : Bool given Ord(a) = x < y\n\
                fn main() =\n  \
                println(show(lt(1, 2)))\n  \
                println(show(lt(1.0, 2.0)))\n  \
                println(show(lt(\"b\", \"a\")))\n";
    assert_eq!(output(prog), "true\ntrue\nfalse\n");
}

// A bare integer literal adopts a `Float` context with no suffix; an unconstrained
// literal still defaults to `Int`. Resolution is compile time, so the elaborated
// constant is the lane's own value.
#[test]
fn literals_adopt_context_and_default_to_int() {
    assert_eq!(
        output("fn main() = println(show((1 : Float) + 2.5))\n"),
        "3.5\n"
    );
    assert_eq!(output("fn main() = println(show(5 + 3))\n"), "8\n");
}

// The polymorphic body resolves to the right lane at each call, one source.
#[test]
fn one_source_runs_at_two_lanes() {
    let prog = "fn dbl(x : a) : a given Num(a) = x + x\n\
                fn main() =\n  println(show(dbl(21)))\n  println(show(dbl(1.5)))\n";
    assert_eq!(output(prog), "42\n3\n");
}

// A bare literal combined with a `Num`-polymorphic variable works: the literal
// injects at the call's lane through `from_int`, so `x + 1` reads the same at
// `Int` and `Float`. A literal at an unconstrained rigid variable stays a
// mismatch (the signature promised nothing numeric), preserving the rigid-variable
// contract.
#[test]
fn literal_adopts_a_num_polymorphic_variable() {
    let prog = "fn scale2(x : a) : a given Num(a) = x * 2 + 1\n\
                fn main() =\n  println(show(scale2(10)))\n  println(show(scale2(2.5)))\n";
    assert_eq!(output(prog), "21\n6\n");
    let msg = rejection("fn f(x : a) : a = x + 1\n");
    assert!(
        msg.contains("mismatch"),
        "a literal at an unconstrained rigid variable stays a mismatch, got: {msg}"
    );
}

// The adoption path includes a leading unary minus. This used to default `-1`
// to `Int` before checking it against rigid `a`, so generic `Num` code could
// write `x + 1` but not `x + -1`.
#[test]
fn negated_literal_adopts_a_num_polymorphic_variable() {
    let prog = "fn dec(x : a) : a given Num(a) = x + -1\n\
                fn main() =\n  println(show(dec(10)))\n  println(show(dec(2.5)))\n";
    assert_eq!(output(prog), "9\n1.5\n");
}

// No implicit coercion: a variable never adapts its lane. `n + 2.5` with `n : Int`
// is a type error naming both lanes, not a promotion. The literal adapts; the
// variable does not.
#[test]
fn no_implicit_coercion_names_both_lanes() {
    let msg = rejection("fn main() =\n  let n = 3\n  println(show(n + 2.5))\n");
    assert!(
        msg.contains("Int") && msg.contains("Float") && msg.contains("mismatch"),
        "a lane mismatch must name both lanes, got: {msg}"
    );
    let cross = rejection("fn f(a : I64, b : U64) : I64 = a + b\n");
    assert!(
        cross.contains("I64") && cross.contains("U64"),
        "a fixed-width mismatch must name both lanes, got: {cross}"
    );
}

#[derive(Clone, Copy, Debug)]
enum NonNumericCase {
    StringAddition,
    UserTypeAddition,
}

impl NonNumericCase {
    const fn src(self) -> &'static str {
        match self {
            Self::StringAddition => "fn main() = println(show(\"a\" + \"b\"))\n",
            Self::UserTypeAddition => "type V = V(Int)\nfn f(a : V, b : V) : V = a + b\n",
        }
    }
}

// A non-numeric operand is rejected as a missing instance on the operand's own
// type, a clean lane story rather than an unresolved-dictionary dump. Crucially
// the message names the lane (`Num(String)`), never a raw `_D`-mangled cell.
#[rstest]
fn non_numeric_operand_reads_as_a_lane_not_a_dict_dump(
    #[values(NonNumericCase::StringAddition, NonNumericCase::UserTypeAddition)]
    case: NonNumericCase,
) {
    let msg = rejection(case.src());
    assert!(
        msg.contains("Num("),
        "a non-numeric operand must name its missing `Num` instance, got: {msg}"
    );
    assert!(
        !msg.contains("_D") && !msg.contains("dict"),
        "an operator error must never surface a dictionary cell, got: {msg}"
    );
}

// Unary minus is not a surface operation on unsigned `U64`; the message names the
// signed lanes it is defined on rather than dumping a constraint.
#[test]
fn unsigned_negation_is_rejected_by_name() {
    let msg = rejection("fn f(a : U64) : U64 = -a\n");
    assert!(
        msg.contains("U64") && msg.contains("negate"),
        "negating a U64 must be rejected by name, got: {msg}"
    );
}
