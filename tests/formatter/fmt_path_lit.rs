// The path literal has exactly one printed spelling: the sigil, the word, one
// space, and the field steps joined by dots. The literal expands to a call
// before the formatter ever sees it, so printing it back is a restoration, and
// the restoration has to be exact in both directions or a reformat would turn a
// literal into the two lambdas it stands for. That is the failure this file
// exists to catch: a printer that loses the surface still round-trips the
// meaning, and only the layout assertion notices.

use super::assert_format;

const ONE_STEP: &str = "fn f() =\n  let a = #path hp\n  a\n";

const MANY_STEPS: &str = "fn f() =\n  let a = #path pos.x\n  a\n";

#[test]
fn a_one_step_literal_prints_as_written() {
    assert_format(ONE_STEP, ONE_STEP);
}

#[test]
fn a_multi_step_literal_keeps_its_dots() {
    assert_format(MANY_STEPS, MANY_STEPS);
}

// Nested in an argument the literal is still a literal. The formatter reaches
// the printed form through the same call classifier that decides every other
// call's layout, so an argument position exercises the path the classifier is
// consulted on rather than the statement path.
#[test]
fn a_literal_survives_an_argument_position() {
    let src = "fn f() =\n  let c = compose_lens(#path pos, #path x)\n  c\n";
    assert_format(src, src);
}

// Extra spacing around the sigil and the steps is the author's, not the
// language's, and normalizing it is the whole reason the form has one spelling.
#[test]
fn spacing_is_normalized() {
    assert_format("fn f() =\n  let a = #path   pos . x\n  a\n", MANY_STEPS);
}

// The restored surface must not leak the expansion. A printer that dropped the
// literal would emit the two lambdas, which still reparses and still means the
// same thing, so the text is the only witness.
#[test]
fn the_expansion_is_never_printed() {
    let out = prism::format(MANY_STEPS).expect("must parse");
    assert!(!out.contains("lens("), "the expansion leaked:\n{out}");
    assert!(!out.contains('\\'), "the expansion leaked:\n{out}");
}

// An anchored literal (`#path Type.field...`) carries its root type in the
// spelling, and the restoration must carry it back: dropping the anchor would
// reparse to an unanchored literal whose binders lose their annotation, which
// is a different program to the checker.
#[test]
fn an_anchored_literal_keeps_its_anchor() {
    let src = "fn f() =\n  let a = #path Solver.metas.next\n  a\n";
    assert_format(src, src);
}

#[test]
fn an_anchored_one_field_literal_prints_as_written() {
    let src = "fn f() =\n  let a = #path Player.hp\n  a\n";
    assert_format(src, src);
}
