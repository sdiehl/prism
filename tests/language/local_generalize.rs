// Checks the local `let` generalization policy for class constraints:
// `generalize_local` quantifies free type/row existentials but keeps any
// existential still mentioned by a pending dictionary obligation monomorphic,
// so the obligation floats to the declaration boundary where a use site
// grounds it or the enclosing `given` context discharges it. There is no
// surface syntax for a constraint on a `let`, so a binding that is never
// grounded still fails with the standard unresolved-constraint diagnostic,
// and one used at two constrained types is a plain mismatch. These pins keep
// both edges of the policy from drifting silently.

use prism::Error;

// A local lambda that calls a class method (`show`) on its parameter incurs a
// `Show` obligation over the parameter's existential. The binding stays
// monomorphic in that variable, and the later `f(1)` grounds it to `Int`, so
// the obligation resolves at the declaration boundary and the program checks.
const GROUNDED_LOCAL: &str = r"fn main() =
  let f = \(x) -> show(x)
  println(f(1))
";

#[test]
fn grounded_local_constraint_is_accepted() {
    let src = prism::with_prelude(GROUNDED_LOCAL);
    prism::check(&src).expect("a use-site-grounded local obligation must check");
}

// The same binding with no grounding use: nothing ever fixes the constrained
// existential, so resolution still fails with the structured "cannot infer
// constraint" diagnostic. This is the surviving rejection edge; acceptance
// here would silently drop the dictionary.
const UNGROUNDED_LOCAL: &str = r#"fn main() =
  let f = \(x) -> show(x)
  println("done")
"#;

#[test]
fn ungrounded_local_constraint_is_rejected() {
    let src = prism::with_prelude(UNGROUNDED_LOCAL);
    let err = prism::check(&src).expect_err("an ungrounded local obligation must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
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

// Inside a declaration that carries `given Show(a)`, the local obligation
// unifies with the declaration's rigid variable and the given context
// discharges it, so the helper works at the signature's full generality.
const GIVEN_DISCHARGES: &str = r#"fn describe(x : a) : String given Show(a) =
  let render = \(v) -> show(v)
  render(x)

fn main() =
  println(describe(42))
  println(describe("hi"))
"#;

#[test]
fn given_context_discharges_local_constraint() {
    let src = prism::with_prelude(GIVEN_DISCHARGES);
    prism::check(&src).expect("the enclosing given context must discharge the local obligation");
}

// A constrained binding stays monomorphic, so using it at two different types
// is a type mismatch, not polymorphism. A binding needed at several
// constrained types still lifts to a top-level `fn ... given C(a)`.
const TWO_TYPES: &str = r#"fn main() =
  let f = \(x) -> show(x)
  println(f(1))
  println(f("hi"))
"#;

#[test]
fn constrained_binding_stays_monomorphic() {
    let src = prism::with_prelude(TWO_TYPES);
    let err = prism::check(&src).expect_err("two constrained use types must not unify");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(
        ty.code(),
        Some("E1022"),
        "expected a plain type mismatch, got: {err}"
    );
}

// Re-decided when lambda parameter annotations began feeding inference: with
// `x : Int` honored, the obligation is the ground `Show Int`, discharged at the
// binding like the fully applied case below. (Before that change the
// annotation was silently dropped, so this program pinned the accident rather
// than a policy.)
const ANNOTATED_LOCAL: &str = r"fn main() =
  let f = \(x : Int) -> show(x)
  println(f(1))
";

#[test]
fn annotation_grounds_the_local_constraint() {
    let src = prism::with_prelude(ANNOTATED_LOCAL);
    prism::check(&src).expect("a ground annotated obligation must discharge at the binding");
}

// The contrast: a fully applied class method (no local generalized function)
// resolves its dictionary at the use site and checks. This bounds the policy
// to generalized local bindings, so the tests cannot be read as "class
// methods do not work locally".
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
