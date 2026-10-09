// A list literal constructs a shape-indexed type. Its length comes from the
// literal's own element count rather than from a construction function, so
// `[1, 2, 3]` fills a `Vec(Int, 3)` position and a literal whose count disagrees
// is refused naming both lengths.
//
// The rule is the arithmetic of three the tower already had: a bare `1` adopting
// a `Float` context, a list literal pushing its lane into `List(T)`, and a tuple
// taking its arity from its own shape. It is checked here beside them, and the
// runtime case is kept as a test rather than a probe because the property it
// exercises — that the literal builds the constructor the type declares — is the
// one a checking-only change would quietly get wrong.

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

/// The literal spelling `n` elements, `[0, 1, ...]`.
fn literal_of(n: usize) -> String {
    let elems: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!("[{}]", elems.join(", "))
}

/// A program that passes a literal of `n` elements where a length-`n` vector is
/// wanted, so the expected type is what gives the literal its length.
fn literal_at(n: usize) -> String {
    format!(
        r"import Data.Vec (..)

fn takes(v : Vec(Int, {n})) : Int = 0
fn use() : Int = takes({})
",
        literal_of(n)
    )
}

// Every length is reached the same way, including the two the module's own
// constructors pin and the ones nothing could build before.
#[rstest]
fn a_literal_constructs_the_length_it_spells(#[values(0, 1, 2, 3, 12)] n: usize) {
    accepts(&literal_at(n));
}

// The count is checked against the dimension, and the refusal names both so the
// reader is not left comparing two whole shape types.
#[test]
fn a_literal_of_the_wrong_length_is_refused_naming_both() {
    let msg = rejection(
        r"import Data.Vec (..)

fn takes3(v : Vec(Int, 3)) : Int = 0
fn use() : Int = takes3([1, 2])
",
    );
    assert!(
        msg.contains("expected length 3") && msg.contains("got length 2"),
        "a length clash should name both lengths, got: {msg}"
    );
}

// A literal against a variable length is not a clash: the count solves the
// variable, which is what lets a caller pass a literal to a polymorphic
// function.
#[test]
fn a_variable_length_is_solved_from_the_count() {
    accepts(
        r"import Data.Vec (..)

fn takes(v : Vec(Int, n)) : Int = 0
fn use() : Int = takes([1, 2, 3])
",
    );
}

// A length the caller's own signature fixed is rigid, so a literal cannot decide
// it: the count is evidence about the literal, not about `n`.
#[test]
fn a_rigid_length_cannot_be_satisfied_by_a_literal() {
    let msg = rejection(
        r"import Data.Vec (..)

fn f(v : Vec(Int, n)) : Vec(Int, n) = [1, 2, 3]
",
    );
    assert!(
        msg.contains("mismatch"),
        "a literal against a rigid length should be refused, got: {msg}"
    );
}

// The element lane is adopted through the rule exactly as it is through
// `List(T)`, so a vector of a fixed-width lane needs no per-element suffix.
#[test]
fn the_element_lane_is_adopted_through_the_rule() {
    accepts(
        r"import Data.Vec (..)

fn takes(v : Vec(I64, 3)) : Int = 0
fn use() : Int = takes([1, 2, 3])
",
    );
}

// The literal form admits a shape-indexed type where it is wanted and nowhere
// else: a list is still not a vector, and a vector is still not a list.
#[test]
fn a_list_is_still_refused_where_a_shape_indexed_type_is_wanted() {
    let msg = rejection(
        r"import Data.Vec (..)

fn takes3(v : Vec(Int, 3)) : Int = 0
fn use(xs : List(Int)) : Int = takes3(xs)
",
    );
    assert!(
        msg.contains("mismatch"),
        "a list should not pass for a vector, got: {msg}"
    );
}

#[test]
fn a_shape_indexed_value_is_still_refused_where_a_list_is_wanted() {
    let msg = rejection(
        r"import Data.Vec (..)

fn wants(xs : List(Int)) : Int = 0
fn use(v : Vec(Int, 3)) : Int = wants(v)
",
    );
    assert!(
        msg.contains("mismatch"),
        "a vector should not pass for a list, got: {msg}"
    );
}

// The runtime half, and the reason it is worth keeping. `vto_list` destructures
// the vector's own constructor to reach the list underneath, so it returns one
// only if the literal really built that constructor; a bare list would fail to
// match instead of quietly looking like the same value.
#[test]
fn a_literal_builds_the_constructor_the_type_declares() {
    let prog = r"import Data.Vec (..)

fn main() =
  println(show(vto_list(([1, 2, 3] : Vec(Int, 3)))))
  println(show(vto_list(([] : Vec(Int, 0)))))
";
    assert_eq!(output(prog), "[1, 2, 3]\n[]\n");
}

// The same at a named position, so the constructor is built for a value that
// travels through a declaration rather than only at the literal's own site.
#[test]
fn a_named_vector_carries_its_constructor() {
    let prog = r"import Data.Vec (..)

fn three() : Vec(Int, 3) = [1, 2, 3]

fn main() = println(show(vto_list(three())))
";
    assert_eq!(output(prog), "[1, 2, 3]\n");
}

// But the rule is about `Vec` and nothing else. A user's own `Grid(a, n : Nat)` has
// exactly the same shape, and its `Nat` is equally untied to the list — so offering
// it the form would promise a check that does not exist: `MkGrid` stays visible, so
// `MkGrid([1])` passes for a `Grid(Int, 3)` with or without the rule. `Vec` is the
// one type where the offer is worth making, because sealing its constructor is what
// makes the literal the only route and the count the only check.
#[test]
fn a_user_declared_type_is_not_offered_the_form() {
    let msg = rejection(
        r"type Grid(a, n : Nat) = MkGrid(List(a))

fn takes(v : Grid(Int, 3)) : Int = 0
fn use() : Int = takes([1, 2, 3])
",
    );
    assert!(
        msg.contains("mismatch"),
        "a user's own type should not be offered the form, got: {msg}"
    );
}

// But the field has to be a list of the element parameter itself, not a list of
// anything. Otherwise a declaration whose lone field is `List(Int)` under a phantom
// element parameter would let a literal of booleans check in a `Foo(Bool, n)`
// position, and elaboration would then build a value whose field holds integers —
// a representation the type does not describe.
#[test]
fn a_field_listing_something_other_than_the_element_is_not_shape_indexed() {
    let msg = rejection(
        r"type Foo(a, n : Nat) = MkFoo(List(Int))

fn takes(v : Foo(Bool, 3)) : Int = 0
fn use() : Int = takes([true, false, true])
",
    );
    assert!(
        msg.contains("mismatch"),
        "a field listing another type should not make a type shape-indexed, got: {msg}"
    );
}
