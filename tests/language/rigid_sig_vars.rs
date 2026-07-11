// A bare type variable in a top-level function signature is an implicit
// `forall a`: it is universally quantified and rigid, so the body may not narrow
// it to a concrete type or equate two distinct signature variables. This is the
// contract that makes a signature a promise rather than a hint. These check both
// halves: the narrowing that must now be rejected, and the genuine polymorphism
// that must still be accepted and exported with the declared scheme.

use prism::check;

fn scheme_of(src: &str, name: &str) -> String {
    let full = prism::with_prelude(src);
    let checked = check(&full).expect("program should type-check");
    checked
        .decls
        .iter()
        .find(|d| d.name == name)
        .unwrap_or_else(|| panic!("no declaration named `{name}`"))
        .ty
        .show()
}

fn rejection(src: &str) -> String {
    let full = prism::with_prelude(src);
    check(&full)
        .expect_err("narrowing a rigid signature variable must be rejected")
        .to_string()
}

// `x : a` promises the body works for every `a`, so `x + 1` (which demands
// `Int`) is a type error naming the variable and the type the body forced.
#[test]
fn body_may_not_narrow_a_signature_variable() {
    let msg = rejection("fn f(x : a) : a = x + 1\n");
    assert!(
        msg.contains("type mismatch") && msg.contains("Int") && msg.contains('a'),
        "the rejection must name the rigid variable and the demanded type, got: {msg}"
    );
}

// Returning `x : a` where the signature promises `Int` narrows `a := Int`, and
// is likewise rejected (the mirror of the arithmetic case: here the annotation,
// not an operator, supplies the concrete type).
#[test]
fn return_annotation_may_not_narrow_a_signature_variable() {
    let msg = rejection("fn g(x : a) : Int = x\n");
    assert!(
        msg.contains("type mismatch") && msg.contains("Int"),
        "expected a narrowing mismatch against `Int`, got: {msg}"
    );
}

// Two distinct signature variables are two distinct universals: `merge2` claims
// to return an `a` but returns its `b` argument, equating `a` with `b`.
#[test]
fn distinct_signature_variables_may_not_be_equated() {
    let msg = rejection("fn merge2(x : a, y : b) : a = y\n");
    assert!(
        msg.contains("type mismatch"),
        "equating two rigid variables must be a mismatch, got: {msg}"
    );
}

// The identity function is the canonical use that must still check: the body
// only passes `a` through, narrowing nothing, and the exported scheme is exactly
// the declared `forall a. (a) -> a`.
#[test]
fn identity_still_checks_and_exports_its_scheme() {
    assert_eq!(
        scheme_of("fn poly_id(x : a) : a = x\n", "poly_id"),
        "forall a. (a) -> a"
    );
}

// A genuinely polymorphic, map-shaped helper checks and exports its declared
// scheme (canonically named), proving rigidity rejects narrowing without
// rejecting real parametric polymorphism. The source names its variables `t` and
// `u`; the exported scheme is canonicalized to `a` and `b`, as an all-existential
// signature would have been.
#[test]
fn a_polymorphic_helper_still_checks_and_exports_its_scheme() {
    let src = r"fn my_map(f : (t) -> u, xs : List(t)) : List(u) =
  match xs of
    Nil => Nil
    Cons(h, r) => Cons(f(h), my_map(f, r))
";
    assert_eq!(
        scheme_of(src, "my_map"),
        "forall a b. ((a) -> b, List(a)) -> List(b)"
    );
}

#[test]
fn higher_rank_binder_does_not_capture_outer_scheme_variable() {
    assert_eq!(
        scheme_of("fn leak(body : forall a. (a) -> r) : r = body(0)\n", "leak"),
        "forall a. (forall b. (b) -> a) -> a"
    );
}
