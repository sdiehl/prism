// The compound path terminals and the statement lvalues have exactly one
// printed spelling each, and every one expands before the formatter sees it:
// `p += e` in a brace is a synth modifier lambda, `x.a.b := e` is a synth brace
// assignment, `get().a.b += e` is a synth `put` call. Printing each back is a
// restoration keyed on those synth shapes, so these pins are the witness that
// the surface and the expansion stay two spellings of one program rather than
// drifting into two programs.

use super::assert_format;

#[test]
fn a_brace_compound_prints_as_written() {
    let src = "fn f(s : S) : S = { s | hp += 1 }\n";
    assert_format(src, src);
}

#[test]
fn brace_compounds_mix_with_the_other_terminals() {
    let src = "fn f(s : S) : S = { s | hp -= 2, name = \"x\", forest ~ grow, next *= 3 }\n";
    assert_format(src, src);
}

// A hand-written modifier lambda means the same thing as a compound terminal
// but is not one, and must keep its explicit spelling.
#[test]
fn a_hand_written_modifier_keeps_its_lambda() {
    let src = "fn f(s : S) : S = { s | hp ~ \\(k) -> k + 1 }\n";
    assert_format(src, src);
}

#[test]
fn a_compound_survives_an_each_step() {
    let src = "fn f(s : S) : S = { s | cells.each *= 2 }\n";
    assert_format(src, src);
}

#[test]
fn a_statement_field_path_prints_as_written() {
    let src = "fn f() : Int =\n  var b : Board := start()\n  b.score += 7\n  b.origin.x := 9\n  b.score\n";
    assert_format(src, src);
}

#[test]
fn a_statement_path_through_an_index_keeps_its_brackets() {
    let src = "fn f() : Int =\n  var cs : List(Cell) := start()\n  cs[0].hp -= 4\n  0\n";
    assert_format(src, src);
}

// The statement abbreviates the brace update; a hand-written brace assignment
// is not the statement and keeps its explicit form.
#[test]
fn a_hand_written_brace_assignment_keeps_its_braces() {
    let src = "fn f() : Int =\n  var b : Board := start()\n  b := { b | score = 1 }\n  b.score\n";
    assert_format(src, src);
}

#[test]
fn a_var_annotation_prints_in_its_slot() {
    let src = "fn f() : Int =\n  var n : Int := 0\n  n += 5\n  n\n";
    assert_format(src, src);
}

#[test]
fn an_unannotated_var_stays_bare() {
    let src = "fn f() : Int =\n  var n := 0\n  n += 5\n  n\n";
    assert_format(src, src);
}

#[test]
fn an_ambient_state_statement_prints_as_written() {
    let src = "fn f() : Unit ! {State(Solver)} =\n  get().metas.next += 1\n  get().metas.forest := grow()\n";
    assert_format(src, src);
}

// A hand-written `put({ get() | ... })` means what the statement means but is
// not synth, so it keeps its explicit spelling.
#[test]
fn a_hand_written_put_get_keeps_its_call() {
    let src = "fn f() : Unit ! {State(S)} = put({ get() | hp = 1 })\n";
    assert_format(src, src);
}
