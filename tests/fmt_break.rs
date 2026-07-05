// Expression-level line breaking (FMT.md / V07.md H5). An over-width value
// expression breaks through the document engine into the pinned house style:
// argument lists and collection literals go one element per line with a trailing
// comma (elements two indent units in, the closing delimiter one unit in), a
// call whose final argument is a delimited aggregate hugs, and an operator or
// `|>` chain breaks before each operator at the lowest precedence present. Each
// case pins the exact layout and asserts the three invariants the reflow rests
// on: the output reparses, formatting is idempotent, and the parsed meaning
// (span-stripped AST) is unchanged.

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

// Rule 2: a call whose final argument is a list hugs, and hugging chains through
// the nested sole-argument call, so the wrapper costs no indentation.
#[test]
fn aggregate_hug() {
    pin(
        "fn main() : Unit =\n  let x = input(map_from_list([(\"neo\", 3), (\"trinity\", 7), (\"morpheus\", 5), (\"cypher\", 2), (\"tank\", 9)]))\n  ()\n",
        "fn main() : Unit =\n  let x = input(map_from_list([\n      (\"neo\", 3),\n      (\"trinity\", 7),\n      (\"morpheus\", 5),\n      (\"cypher\", 2),\n      (\"tank\", 9),\n    ]))\n  ()\n",
    );
}

// Rule 1: nested calls break outermost-first; an inner call that fits at its new
// indent stays flat (no staircase).
#[test]
fn nested_calls_no_staircase() {
    pin(
        "fn f() =\n  process_frame(update_positions(apply_forces(compute_neighbors(w, r, n), g, d), dt), fi)\n",
        "fn f() =\n  process_frame(\n      update_positions(apply_forces(compute_neighbors(w, r, n), g, d), dt),\n      fi,\n    )\n",
    );
}

// Rule 3: a list literal breaks to one element per line with a trailing comma.
#[test]
fn list_literal_breaks() {
    pin(
        "fn main() : List(Int) =\n  [alpha_one, bravo_two, charlie_three, delta_four, echo_five, foxtrot_six, golf_seven_x]\n",
        "fn main() : List(Int) =\n  [\n      alpha_one,\n      bravo_two,\n      charlie_three,\n      delta_four,\n      echo_five,\n      foxtrot_six,\n      golf_seven_x,\n    ]\n",
    );
}

// Rule 3: a tuple literal has the same broken shape.
#[test]
fn tuple_literal_breaks() {
    pin(
        "fn f() : Bool =\n  (alpha_one_value, bravo_two_value, charlie_three_value, delta_four_value, echo_five_value)\n",
        "fn f() : Bool =\n  (\n      alpha_one_value,\n      bravo_two_value,\n      charlie_three_value,\n      delta_four_value,\n      echo_five_value,\n    )\n",
    );
}

// Rule 4: an over-width operator chain breaks before each operator at one indent.
#[test]
fn operator_chain_leads() {
    pin(
        "fn f() : Int =\n  base_score(player) + bonus_for_streak(streak, multiplier) + penalty_for_time(elapsed_ms)\n",
        "fn f() : Int =\n  base_score(player)\n    + bonus_for_streak(streak, multiplier)\n    + penalty_for_time(elapsed_ms)\n",
    );
}

// Rule 4: a `|>` pipeline reads as a column of stages.
#[test]
fn pipeline_column() {
    pin(
        "fn f() : World =\n  world |> compute_neighbors(radius) |> apply_forces(gravity, damping) |> integrate(delta_t)\n",
        "fn f() : World =\n  world\n    |> compute_neighbors(radius)\n    |> apply_forces(gravity, damping)\n    |> integrate(delta_t)\n",
    );
}

// Rule 4: precedence-aware. Only the lowest-precedence operators break; the
// higher-precedence comparison operands stay flat on each line.
#[test]
fn chain_breaks_lowest_precedence() {
    pin(
        "fn f() : Bool =\n  length(xs) == length(ys) && length(ys) == length(zs) && length(zs) == length(final_ws)\n",
        "fn f() : Bool =\n  length(xs) == length(ys)\n    && length(ys) == length(zs)\n    && length(zs) == length(final_ws)\n",
    );
}

// A call whose arguments fit stays flat: the doc path must not disturb an
// expression that was already within budget (no churn on the common case).
#[test]
fn fitting_call_stays_flat() {
    pin(
        "fn f() : Int = process(a, b, c)\n",
        "fn f() : Int = process(a, b, c)\n",
    );
}
