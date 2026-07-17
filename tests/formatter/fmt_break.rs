// Expression-level line breaking. An over-width value expression breaks through
// the document engine into the expected house style:
// argument lists and collection literals go one element per line with a trailing
// comma (elements two indent units in, the closing delimiter one unit in), a
// call whose final argument is a delimited aggregate hugs, and an operator or
// `|>` chain breaks before each operator at the lowest precedence present. Each
// case checks the exact layout and asserts the three invariants the reflow rests
// on: the output reparses, formatting is idempotent, and the parsed meaning
// (span-stripped AST) is unchanged.

use rstest::rstest;

// The parse AST with span offsets stripped, invariant under the whitespace
// reflow a reformat performs (reflow shifts only spans; a structural change
// survives the strip).
fn ast_no_spans(src: &str) -> String {
    prism::dump("ast", src)
        .expect("must parse")
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            !t.starts_with("span:") && !is_span_range(t)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

// A bare `start..end,` line, the `Debug` rendering of a `Span` field value.
fn is_span_range(t: &str) -> bool {
    let t = t.trim_end_matches(',');
    matches!(t.split_once(".."), Some((a, b)) if !a.is_empty()
        && a.bytes().all(|c| c.is_ascii_digit())
        && b.bytes().all(|c| c.is_ascii_digit()))
}

// Format, assert the output equals `want`, then assert reparse + idempotence +
// meaning preservation.
fn pin(src: &str, want: &str) {
    let once = prism::format(src).expect("input must parse");
    assert_eq!(once, want, "layout drift:\n{once}");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "not idempotent:\n{once}\n-->\n{twice}");
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(&once),
        "formatting changed the parsed meaning:\n{src}\n-->\n{once}"
    );
}

#[derive(Clone, Copy, Debug)]
enum BreakCase {
    AggregateHug,
    NestedCallsNoStaircase,
    ListLiteral,
    TupleLiteral,
    OperatorChain,
    PipelineColumn,
    LowestPrecedenceChain,
    FittingCall,
}

impl BreakCase {
    const fn src(self) -> &'static str {
        match self {
            Self::AggregateHug => {
                "fn main() : Unit =\n  let x = input(map_from_list([(\"neo\", 3), (\"trinity\", 7), (\"morpheus\", 5), (\"cypher\", 2), (\"tank\", 9)]))\n  ()\n"
            }
            Self::NestedCallsNoStaircase => {
                "fn f() =\n  process_frame(update_positions(apply_forces(compute_neighbors(w, r, n), g, d), dt), fi)\n"
            }
            Self::ListLiteral => {
                "fn main() : List(Int) =\n  [alpha_one, bravo_two, charlie_three, delta_four, echo_five, foxtrot_six, golf_seven_x]\n"
            }
            Self::TupleLiteral => {
                "fn f() : Bool =\n  (alpha_one_value, bravo_two_value, charlie_three_value, delta_four_value, echo_five_value)\n"
            }
            Self::OperatorChain => {
                "fn f() : Int =\n  base_score(player) + bonus_for_streak(streak, multiplier) + penalty_for_time(elapsed_ms)\n"
            }
            Self::PipelineColumn => {
                "fn f() : World =\n  world |> compute_neighbors(radius) |> apply_forces(gravity, damping) |> integrate(delta_t)\n"
            }
            Self::LowestPrecedenceChain => {
                "fn f() : Bool =\n  length(xs) == length(ys) && length(ys) == length(zs) && length(zs) == length(final_ws)\n"
            }
            Self::FittingCall => "fn f() : Int = process(a, b, c)\n",
        }
    }

    const fn want(self) -> &'static str {
        match self {
            Self::AggregateHug => {
                "fn main() : Unit =\n  let x = input(map_from_list([\n      (\"neo\", 3),\n      (\"trinity\", 7),\n      (\"morpheus\", 5),\n      (\"cypher\", 2),\n      (\"tank\", 9),\n    ]))\n  ()\n"
            }
            Self::NestedCallsNoStaircase => {
                "fn f() =\n  process_frame(\n      update_positions(apply_forces(compute_neighbors(w, r, n), g, d), dt),\n      fi,\n    )\n"
            }
            Self::ListLiteral => {
                "fn main() : List(Int) =\n  [\n      alpha_one,\n      bravo_two,\n      charlie_three,\n      delta_four,\n      echo_five,\n      foxtrot_six,\n      golf_seven_x,\n    ]\n"
            }
            Self::TupleLiteral => {
                "fn f() : Bool =\n  (\n      alpha_one_value,\n      bravo_two_value,\n      charlie_three_value,\n      delta_four_value,\n      echo_five_value,\n    )\n"
            }
            Self::OperatorChain => {
                "fn f() : Int =\n  base_score(player)\n    + bonus_for_streak(streak, multiplier)\n    + penalty_for_time(elapsed_ms)\n"
            }
            Self::PipelineColumn => {
                "fn f() : World =\n  world\n    |> compute_neighbors(radius)\n    |> apply_forces(gravity, damping)\n    |> integrate(delta_t)\n"
            }
            Self::LowestPrecedenceChain => {
                "fn f() : Bool =\n  length(xs) == length(ys)\n    && length(ys) == length(zs)\n    && length(zs) == length(final_ws)\n"
            }
            Self::FittingCall => "fn f() : Int = process(a, b, c)\n",
        }
    }
}

#[rstest]
fn expression_breaking_matches_pinned_layout(
    #[values(
        BreakCase::AggregateHug,
        BreakCase::NestedCallsNoStaircase,
        BreakCase::ListLiteral,
        BreakCase::TupleLiteral,
        BreakCase::OperatorChain,
        BreakCase::PipelineColumn,
        BreakCase::LowestPrecedenceChain,
        BreakCase::FittingCall
    )]
    case: BreakCase,
) {
    pin(case.src(), case.want());
}

#[test]
fn partial_handler_keeps_braces_and_roundtrips() {
    let source = "effect E\n  one() : Int\n  two() : Int\n\nfn run() : Int ! {E} =\n  handle one() + two() with partial {\n    one() resume k => k(1),\n    return r => r\n  }\n";
    pin(source, source);
}

#[test]
fn transact_uses_layout_when_bound() {
    let src = "fn main() =\n  let r = transact let _ = balance -= 40 in let _ = stock -= 1 in let _ = guard(balance >= 0) in 1 else 0\n  r\n";
    let want = "fn main() =\n  let r =\n    transact\n      balance -= 40\n      stock -= 1\n      guard(balance >= 0)\n      1\n    else\n      0\n  r\n";
    pin(src, want);
}
