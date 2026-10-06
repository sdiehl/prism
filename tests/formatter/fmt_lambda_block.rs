// Canonical layout for a lambda whose body is a block (a `handle`, a `match`):
// the head stays on the line that introduces the lambda and the body lays out
// offside one level below it. The body used to be reprinted from source at its
// written columns, which put it level with the lambda when the formatter moved
// the lambda to its own line, and the result no longer parsed.
//
// Each case asserts the exact layout plus the two invariants a reformat rests
// on: formatting is idempotent, and the output reparses to the same span-stripped
// meaning.

use super::assert_format_semantics;

const LET_BOUND: &str = r"fn main() : Unit ! {IO} =
  let f = \(x) ->
    handle x() with
      ask() resume k => k(1)
  println(show(f(\() -> ask() + 1)))
";

const RESULT: &str = r"fn runner() =
  \(x) ->
    handle x() with
      ask() resume k => k(1)
";

#[test]
fn let_bound_lambda_keeps_its_head_on_the_binding_line() {
    assert_format_semantics(LET_BOUND, LET_BOUND);
}

#[test]
fn lambda_in_result_position_is_a_fixpoint() {
    assert_format_semantics(RESULT, RESULT);
}

// Written with the lambda on its own line under `let`, it moves up beside the
// binding.
#[test]
fn lambda_under_its_binding_moves_up() {
    let src = r"fn main() : Unit ! {IO} =
  let f =
    \(x) ->
      handle x() with
        ask() resume k => k(1)
  println(show(f(\() -> ask() + 1)))
";
    assert_format_semantics(src, LET_BOUND);
}
