// Checks the current, deliberate limit on local `let` generalization:
// `generalize` quantifies free type/row existentials but never class
// constraints, and there is no surface syntax for a constraint on a `let`. So a
// local binding whose body incurs a dictionary obligation over a variable it
// would generalize cannot carry that obligation, and the orphaned constraint
// surfaces as the standard unresolved-constraint diagnostic. This is not a bug
// to fix here (constraint generalization is out of scope); the test exists so a
// future change that alters the behavior is noticed and re-decided on purpose.

use prism::Error;

// A local lambda that calls a class method (`show`) on its parameter incurs a
// `Show` obligation the local binding cannot carry. Rejected at constraint
// resolution, not silently accepted (which would drop the dictionary).
const CONSTRAINED_LOCAL: &str = r"fn main() =
  let f = \(x) -> show(x)
  println(f(1))
";

#[test]
fn constrained_local_binding_is_rejected() {
    let src = prism::with_prelude(CONSTRAINED_LOCAL);
    let err = prism::check(&src).expect_err("a constrained local binding must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    // The orphaned obligation surfaces as the structured "cannot infer
    // constraint" diagnostic (E3014), naming the `Show` class it could not carry.
    assert_eq!(
        ty.code(),
        Some("E3014"),
        "expected the unresolved-constraint diagnostic (E3014), got: {err}"
    );
    assert!(
        err.to_string().contains("constraint Show"),
        "the rejection must name the orphaned `Show` obligation, got: {err}"
    );
}

// The obligation is orphaned by generalization, not by a missing annotation:
// annotating the parameter's type does not rescue the binding. Checking this
// guards against a future reader "fixing" the test with an annotation and
// concluding the limitation is gone.
const ANNOTATED_LOCAL: &str = r"fn main() =
  let f = \(x : Int) -> show(x)
  println(f(1))
";

#[test]
fn annotation_does_not_rescue_constrained_local() {
    let src = prism::with_prelude(ANNOTATED_LOCAL);
    assert!(
        prism::check(&src).is_err(),
        "annotating the parameter must not make a constrained local binding check"
    );
}

// The contrast: a fully applied class method (no local generalized function)
// resolves its dictionary at the use site and checks. This bounds the
// limitation to generalized local bindings, so the test cannot be read as
// "class methods do not work locally".
const APPLIED_DIRECTLY: &str = r"fn main() =
  let s = show(1)
  println(s)
";

#[test]
fn applied_class_method_checks_locally() {
    let src = prism::with_prelude(APPLIED_DIRECTLY);
    assert!(
        prism::check(&src).is_ok(),
        "a fully applied class method in a local `let` should check"
    );
}
