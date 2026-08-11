// Two rules about where a lambda's parameter type comes from, and the pins that
// keep them from drifting into each other.
//
// The first is that a written annotation on a parameter is the author's word
// about that binding, so the body sees the annotation. Ignoring it is not a
// harmless simplification: a parameter silently bound at something wider than
// what was written accepts uses the annotation forbids, and the annotation stops
// meaning anything. When an expected domain is in hand as well, the two are
// reconciled contravariantly, because the caller supplies the domain's values
// while the body reads them at the annotation.
//
// The second is that a saturated call solves its result against the surrounding
// expectation before its arguments are checked. A callee's type arguments occur
// in its result as well as its domains, so a declared result fixes them, and an
// annotation-free lambda argument then checks against a domain that is known
// rather than against an existential nothing later can solve. This only ever
// adds information and only ever earlier; where there is no expectation to
// consult, inference is exactly what it was.

use prism::{check, interpret, with_prelude};

// The rendered error of a program expected not to type-check.
fn check_err(src: &str) -> String {
    match check(&with_prelude(src)) {
        Ok(_) => panic!("expected a type error, but the program checked"),
        Err(e) => format!("{e}"),
    }
}

fn check_ok(src: &str) {
    if let Err(e) = check(&with_prelude(src)) {
        panic!("expected the program to check, got: {e}");
    }
}

fn run(src: &str) -> String {
    interpret(&with_prelude(src))
        .unwrap_or_else(|e| panic!("interpret failed: {e}"))
        .term
}

// A callback whose argument is polymorphic. Annotating the parameter at one
// instance is legal, and it is also a commitment: inside the body the parameter
// is that instance and nothing wider.
const POLY_CALLBACK: &str = "fn use_poly(k : (forall a. (a) -> a) -> Int) : Int = k(\\(x) -> x)\n";

// The same lambda body, once with the parameter annotated and once without. The
// annotated one is rejected because `f` was written at `(Int) -> Int` and is
// applied to a string; the unannotated one is accepted because `f` binds at the
// polymorphic domain the callback declares. One annotation is the only
// difference between them, so the annotation is what the body is reading.
#[test]
fn an_annotation_binds_the_body_not_the_expected_domain() {
    let annotated = format!(
        "{POLY_CALLBACK}fn main() = println(use_poly(\\(f : (Int) -> Int) -> str_len(f(\"hi\"))))\n"
    );
    let err = check_err(&annotated);
    assert!(
        err.contains("String") && err.contains("Int"),
        "the annotation must restrict the body's use of `f`: {err}"
    );

    check_ok(&format!(
        "{POLY_CALLBACK}fn main() = println(use_poly(\\(f) -> str_len(f(\"hi\"))))\n"
    ));
}

// The obligation between an expected domain and an annotation runs one way:
// every value the caller can supply must be usable as the annotation. A
// polymorphic domain annotated at an instance satisfies that and is accepted; a
// monomorphic domain annotated polymorphically does not and is refused, because
// the body would be reading a general function out of a slot that only ever
// holds a specific one. Written backwards, this pair swaps its answers, which is
// what makes it a test of the direction rather than of the check's existence.
#[test]
fn the_expected_domain_is_held_to_the_annotation_not_the_reverse() {
    check_ok(&format!(
        "{POLY_CALLBACK}fn main() = println(use_poly(\\(f : (Int) -> Int) -> f(1)))\n"
    ));

    let err = check_err(
        "fn use_mono(k : ((Int) -> Int) -> Int) : Int = k(\\(x) -> x)\n\
         fn main() = println(use_mono(\\(f : forall a. (a) -> a) -> f(1)))\n",
    );
    assert!(
        err.contains("forall a. (a) -> a") && err.contains("(Int) -> Int"),
        "the refusal must name the annotation and the domain it was held to: {err}"
    );
}

// A wrapper whose type argument appears only under a function, so the argument
// lambda's parameter type is reachable from the result and from nowhere else.
const WRAP: &str = "\
type Wrap(s) = MkWrap((s) -> Int)

fn wrap(g) = MkWrap(g)

type Pt = Pt { x : Int, y : Int }
";

// With the result declared, `s` is fixed before the lambda is looked at, and the
// field access inside it has a record to resolve against.
#[test]
fn a_declared_result_solves_the_callee_before_its_arguments() {
    let src = format!(
        "{WRAP}
fn get_x() : Wrap(Pt) = wrap(\\(p) -> p.x)

fn main() =
  match get_x() of
    MkWrap(g) => println(g(Pt {{ x = 5, y = 6 }}))
"
    );
    assert_eq!(run(&src), "5\n");
}

// The same call with the result undeclared. Nothing expects anything of it, so
// there is nothing to solve `s` from and the field access is left with an
// unsolved parameter, exactly as before the result was ever consulted. The rule
// adds information where the context has some and changes nothing where it does
// not.
#[test]
fn with_no_expectation_the_argument_is_inferred_alone() {
    let err = check_err(&format!(
        "{WRAP}
fn get_x() = wrap(\\(p) -> p.x)

fn main() = println(1)
"
    ));
    assert!(
        err.contains("field access on non-record type"),
        "an unsolved parameter must still be reported: {err}"
    );
}
