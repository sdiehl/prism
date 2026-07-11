// Explicit instance selection (`f(args, using I)`) must survive formatting on
// every layout path. The flat/break printer and the inline printer decode a
// call head through one shared classifier; when they drifted, a call wide enough
// to break re-emitted `f(a, using I)` as `f(using I)(a)` -- a fixpoint, so it
// slipped past plain idempotence. These cases check AST-level round-trip (meaning
// preserved), not just `format(format(x)) == format(x)`.

// The parse AST with span offsets stripped, so it is invariant under the
// whitespace reflow a reformat performs. Reflow shifts only spans; a structural
// change (the `using`-drift adds a Call node) survives the strip and shows up.
use rstest::rstest;

fn ast_no_spans(src: &str) -> String {
    prism::dump("ast", src)
        .expect("must parse")
        .lines()
        .filter(|l| !l.trim_start().starts_with("span:"))
        .collect::<Vec<_>>()
        .join("\n")
}

// Format `src`, then assert: the output reparses, formatting is idempotent, and
// the parsed meaning is unchanged (same span-stripped AST as the input).
fn preserves_meaning(src: &str) {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(&once),
        "formatting changed the parsed meaning:\n{src}\n-->\n{once}"
    );
}

// A long value name forces the `let` value onto its own line, routing the call
// through the break path where the drift lived.
const WIDE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

#[derive(Clone, Copy, Debug)]
enum UsingCase {
    InlineValueArg,
    BreakValueArg,
    InlineZeroArg,
    BreakZeroArg,
    SeveralArgs,
}

impl UsingCase {
    fn src(self) -> String {
        match self {
            Self::InlineValueArg => {
                "fn f(x : Int) : Int given Ord(Int) = x\nfn g() : Int = f(1, using ordInt)\n"
                    .to_string()
            }
            Self::BreakValueArg => {
                format!(
                    "fn f(x : Int) : Int given Ord(Int) = x\nfn g() : Int = f({WIDE}, using ordInt)\n"
                )
            }
            Self::InlineZeroArg => {
                "fn f() : Int given Ord(Int) = 0\nfn g() : Int = f(using ordInt)\n".to_string()
            }
            Self::BreakZeroArg => {
                format!(
                    "fn {WIDE}() : Int given Ord(Int) = 0\nfn g() : Int = {WIDE}(using ordInt)\n"
                )
            }
            Self::SeveralArgs => {
                format!(
                    "fn f(x : Int, y : Int) : Int given Ord(Int) = x\nfn g() : Int = f({WIDE}, 2, using ordInt)\n"
                )
            }
        }
    }
}

#[rstest]
fn using_calls_preserve_meaning(
    #[values(
        UsingCase::InlineValueArg,
        UsingCase::BreakValueArg,
        UsingCase::InlineZeroArg,
        UsingCase::BreakZeroArg,
        UsingCase::SeveralArgs
    )]
    case: UsingCase,
) {
    preserves_meaning(&case.src());
}

#[test]
fn using_call_break_path_keeps_value_arg_before_using_clause() {
    let src =
        format!("fn f(x : Int) : Int given Ord(Int) = x\nfn g() : Int = f({WIDE}, using ordInt)\n");
    let out = prism::format(&src).unwrap();
    let arg = out.find(WIDE).expect("value arg kept");
    let using = out.find("using").expect("using clause kept");
    assert!(arg < using, "value arg moved out of the call: {out:?}");
}

// Neighboring call-head shapes the same classifier decodes: a UFCS dot call and
// a `?`-receiver, each wide enough to break, must round-trip too.
#[derive(Clone, Copy, Debug)]
enum NeighborCallCase {
    Dot,
    Try,
}

impl NeighborCallCase {
    fn src(self) -> String {
        match self {
            Self::Dot => format!("fn g(xs : List(Int)) : Int = xs.foldl(0, {WIDE})\n"),
            Self::Try => format!("fn g(r : Result(Int, Int)) : Int ! {{Throw}} = f({WIDE}, r?)\n"),
        }
    }
}

#[rstest]
fn neighboring_call_heads_survive_the_break_path(
    #[values(NeighborCallCase::Dot, NeighborCallCase::Try)] case: NeighborCallCase,
) {
    let src = case.src();
    // Reparse + idempotence; these never used the Inst arm but share the decoder.
    let once = prism::format(&src).expect("input must parse");
    let twice = prism::format(&once).expect("output must reparse");
    assert_eq!(once, twice, "not idempotent: {src:?}");
}
