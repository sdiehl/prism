// Source-soundness regression tests. Each program below isolates an
// effect, handler, or coeffect shape
// that must be rejected because accepting it would let a program observe which
// lowering tier fired (a duplicate arm silently shadowing, a partial handler
// leaving an operation undischarged, a borrow leaking through an open row, a
// `once` continuation resumed off the tail). These cases prevent silent
// regressions into acceptance: every negative test asserts both
// rejection and the exact structured diagnostic code, and one positive control
// proves the coverage rule does not over-reject a fully covered handler.

use std::io::Write;
use std::process::{Command, Stdio};

use prism::error::{ErrKind, Frame, TypeError};
use prism::Error;

// Two arms for the same operation `pick`. The second silently shadows the first
// under one lowering and not another, so it must be a duplicate-arm error.
const DUPLICATE_HANDLER_ARM: &str =
    include_str!("../fixtures/language/soundness/duplicate_handler_arm.pr");

#[test]
fn duplicate_handler_arm_is_rejected() {
    let src = prism::with_prelude(DUPLICATE_HANDLER_ARM);
    let err = prism::check(&src).expect_err("a duplicate handler arm must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E5008"), "got: {err}");
}

// Two `return` arms in one handler. The second is unreachable dead code under
// one tier and a redefinition under another, so it must be a duplicate-return
// error.
const DUPLICATE_RETURN_ARM: &str =
    include_str!("../fixtures/language/soundness/duplicate_return_arm.pr");

#[test]
fn duplicate_return_arm_is_rejected() {
    let src = prism::with_prelude(DUPLICATE_RETURN_ARM);
    let err = prism::check(&src).expect_err("a duplicate return arm must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E5009"), "got: {err}");
}

// The arm binds `put(a, b, k)` but `put` takes one argument. The arm's operation
// parameters plus continuation do not match the operation's declared arity.
const HANDLER_ARITY_MISMATCH: &str =
    include_str!("../fixtures/language/soundness/handler_arity_mismatch.pr");

#[test]
fn handler_arity_mismatch_is_rejected() {
    let src = prism::with_prelude(HANDLER_ARITY_MISMATCH);
    let err = prism::check(&src).expect_err("a handler arity mismatch must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E5010"), "got: {err}");
}

// One named `Cell(a)` instance fixes `a` at its first directed call. A later
// directed call through the same instance cannot silently instantiate another
// `a`, or the handler's operation and label evidence would disagree.
const NAMED_INSTANCE_ARGUMENT_MISMATCH: &str =
    include_str!("../fixtures/language/soundness/named_instance_argument_mismatch.pr");

#[test]
fn named_instance_reuses_one_effect_argument_vector() {
    let src = prism::with_prelude(NAMED_INSTANCE_ARGUMENT_MISMATCH);
    let err = prism::check(&src)
        .expect_err("one named effect instance cannot be both Cell(Int) and Cell(String)");
    let Error::Type(TypeError::Kind(diag)) = err else {
        panic!("expected a structured type mismatch, got: {err}");
    };
    assert_eq!(diag.kind.code(), "E1022", "got: {diag}");
    let ErrKind::TypeMismatch { expected, found } = &diag.kind else {
        panic!("expected the structured type-mismatch payload, got: {diag}");
    };
    assert_eq!((expected.as_str(), found.as_str()), ("Int", "String"));
    assert!(
        matches!(diag.context.as_slice(), [Frame::InFn(name)] if name == "main"),
        "the mismatch must retain its declaration context: {diag}"
    );
}

// The mirror direction: `pair` declares two operation parameters, the clause
// binds one. Too few is a compile error just as too many is.
const HANDLER_ARITY_TOO_FEW: &str =
    include_str!("../fixtures/language/soundness/handler_arity_too_few.pr");

#[test]
fn handler_arity_too_few_is_rejected() {
    let src = prism::with_prelude(HANDLER_ARITY_TOO_FEW);
    let err = prism::check(&src).expect_err("a handler binding too few op params must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E5010"), "got: {err}");
}

// The handled action raises both `one` and `two` but the handler only covers
// `one`, leaving `two` undischarged. A partial handler must be rejected.
const PARTIAL_HANDLER: &str = include_str!("../fixtures/language/soundness/partial_handler.pr");

#[test]
fn partial_handler_is_rejected() {
    let src = prism::with_prelude(PARTIAL_HANDLER);
    let err = prism::check(&src).expect_err("a partial handler must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(
        ty.code(),
        Some(prism::error::INCOMPLETE_HANDLER.as_str()),
        "got: {err}"
    );
}

// A `borrow` parameter cannot escape through a callback whose effect row is open
// (`! {| e}`): the open row could smuggle the borrowed value out past its scope.
const BORROW_OPEN_ROW: &str = include_str!("../fixtures/language/soundness/borrow_open_row.pr");

#[test]
fn borrow_open_row_is_rejected() {
    let src = prism::with_prelude(BORROW_OPEN_ROW);
    let err =
        prism::check(&src).expect_err("a borrow leaking through an open row must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E5012"), "got: {err}");
}

// `ask` is graded `once`, so its continuation may be resumed at most once and
// only in tail position. `k(1) + 1` resumes off the tail, exceeding the grade.
const ONCE_NONTAIL_RESUME: &str =
    include_str!("../fixtures/language/soundness/once_nontail_resume.pr");

#[test]
fn once_nontail_resume_is_rejected() {
    let src = prism::with_prelude(ONCE_NONTAIL_RESUME);
    let err = prism::check(&src).expect_err("a non-tail resume of a `once` op must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    // HandlerGradeExceeded in src/error/mod.rs maps to E6028.
    assert_eq!(ty.code(), Some("E6028"), "got: {err}");
}

// Positive control: a handler that covers every raised operation plus a return
// arm must check. This bounds the coverage rule so the partial-handler check
// cannot be read as "handlers over-reject".
const FULL_COVERAGE_HANDLER: &str =
    include_str!("../fixtures/language/soundness/full_coverage_handler.pr");

#[test]
fn full_coverage_handler_checks() {
    let src = prism::with_prelude(FULL_COVERAGE_HANDLER);
    assert!(
        prism::check(&src).is_ok(),
        "a fully covered handler with a return arm must check"
    );
}

// An effect-polymorphic class method (`method : (a) -> a ! {| e}`) obligates the
// instance to be parametric in the row. Performing a concrete `Leak` is not
// forwarding an effect through the row variable, it is choosing a new effect,
// and must be rejected at check. Previously the method's effect row was
// discarded during instance checking and the leak surfaced only at run time.
const INSTANCE_METHOD_LEAK: &str =
    include_str!("../fixtures/language/soundness/instance_method_leak.pr");

#[test]
fn effect_polymorphic_instance_method_cannot_leak() {
    let src = prism::with_prelude(INSTANCE_METHOD_LEAK);
    let err = prism::check(&src)
        .expect_err("an instance method performing an undeclared effect must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E3006"), "got: {err}");
}

// Positive control: an instance of the same effect-polymorphic class whose body
// only forwards effects through the row variable (here, performs none) checks.
// The forwarded effect stays as the row variable and never appears as a concrete
// label, so the parametricity rule does not over-reject legitimate instances.
const INSTANCE_METHOD_FORWARDS: &str =
    include_str!("../fixtures/language/soundness/instance_method_forwards.pr");

#[test]
fn effect_polymorphic_instance_method_forwarding_checks() {
    let src = prism::with_prelude(INSTANCE_METHOD_FORWARDS);
    assert!(
        prism::check(&src).is_ok(),
        "an effect-polymorphic instance method that adds no concrete effect must check"
    );
}

// Alpha-renaming invariance: nested `forall` binders that share a source
// spelling must not alias in the checker's context. Before rigid binders carried
// a fresh identity, the same-name form hit a `solve_row: not in context` ICE
// while the renamed form type-checked; now both produce the identical, correct
// diagnostic. The pair is checked to agree, so a regression that reintroduces
// spelling-based binder identity is caught.
const NESTED_FORALL_SAME_NAME: &str = r"fn apply(g : forall a. (a, forall a. (a) -> a) -> Int) : Int = g(1, \(x) -> x)
fn main() = println(apply(\(v, id) -> v))
";

const NESTED_FORALL_RENAMED: &str = r"fn apply(g : forall a. (a, forall b. (b) -> b) -> Int) : Int = g(1, \(x) -> x)
fn main() = println(apply(\(v, id) -> v))
";

#[test]
fn nested_same_name_forall_matches_alpha_renamed() {
    let same = prism::check(&prism::with_prelude(NESTED_FORALL_SAME_NAME));
    let renamed = prism::check(&prism::with_prelude(NESTED_FORALL_RENAMED));
    // Neither is an internal compiler error, and both reach the same verdict.
    for r in [&same, &renamed] {
        if let Err(Error::Type(ty)) = r {
            assert_ne!(
                ty.kind(),
                "Internal Error",
                "nested forall must not ICE: {r:?}"
            );
        }
    }
    assert_eq!(
        same.as_ref().err().map(ToString::to_string),
        renamed.as_ref().err().map(ToString::to_string),
        "a nested same-name `forall` must check identically to its alpha-renamed form"
    );
}

// An application in a `Row`-kinded parameter position has no row representation
// and was silently erased to the empty row before kinds were checked there. It
// is now a kind mismatch (E1003). A row variable in the same position stays
// legal, so row-polymorphic uses are unaffected.
const ROW_POSITION_APP: &str = r"type Cmd(a, e : Row) = MkCmd(Int)
fn f(x : Cmd(Int, g(Int))) : Int = 0
fn main() = println(0)
";

const ROW_POSITION_VAR: &str = r"type Cmd(a, e : Row) = MkCmd(Int)
fn f(x : Cmd(Int, e)) : Int = 0
fn main() = println(0)
";

#[test]
fn application_in_row_position_is_rejected() {
    let err = prism::check(&prism::with_prelude(ROW_POSITION_APP))
        .expect_err("an application in a Row position must be a kind mismatch");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E1003"), "got: {err}");
}

#[test]
fn row_variable_in_row_position_checks() {
    assert!(
        prism::check(&prism::with_prelude(ROW_POSITION_VAR)).is_ok(),
        "a row variable in a Row position must still check"
    );
}

// `OrNull(Unit)` would let `This(())` (the zero word) collide with `Null`, so the
// element rule rejects it at the annotation.
const OR_NULL_UNIT_ANNOT: &str = r"fn m() : OrNull(Unit) = Null
fn main() = println(0)
";

// The same rule must fire on an inferred (unannotated) `This(())`, or inference
// would be a hole around the annotation check.
const OR_NULL_UNIT_INFERRED: &str = r"fn m() = This(())
fn main() = println(0)
";

// A polymorphic `This(x)` whose element is never pinned could later be `Unit`, so
// an un-inferred element is rejected too.
const OR_NULL_UNINFERRED: &str = r"fn wrap(x) = This(x)
fn main() = println(0)
";

// `OrNull(OrNull(a))` is rejected: the null word would be ambiguous.
const OR_NULL_NESTED: &str = r"fn m() : OrNull(OrNull(Int)) = Null
fn main() = println(0)
";

// A transparent newtype can erase to the zero word even though its source type
// is nominal, so it needs declaration-aware representation proof.
const OR_NULL_ZERO_NEWTYPE: &str = r"newtype Zero = Zero(Unit)
fn m() : OrNull(Zero) = This(Zero(()))
fn main() = println(0)
";

// Constructor shape is not newtype evidence: an ordinary unary datatype keeps
// its allocated, non-zero wrapper and is a sound nullable element.
const OR_NULL_ORDINARY_UNARY: &str = r"type Box(a) = Box(a)
fn annotated(x : Box(Int)) : OrNull(Box(Int)) = This(x)
fn inferred(x : Box(Int)) = This(x)
fn main() = println(0)
";

// A well-formed nullable over a heap element must still check.
const OR_NULL_OK: &str = r#"fn m(b : Bool) : OrNull(String) =
  match b of
    true => This("x")
    false => Null
fn main() = println(0)
"#;

fn or_null_rejected(src: &str, what: &str) {
    let err =
        prism::check(&prism::with_prelude(src)).expect_err(&format!("{what} must be rejected"));
    let Error::Type(ty) = &err else {
        panic!("expected a type error for {what}, got: {err}");
    };
    assert_eq!(ty.code(), Some("E1019"), "{what}: got {err}");
}

#[test]
fn or_null_zero_word_element_is_rejected() {
    or_null_rejected(OR_NULL_UNIT_ANNOT, "OrNull(Unit) annotation");
    or_null_rejected(OR_NULL_UNIT_INFERRED, "inferred OrNull(Unit)");
    or_null_rejected(OR_NULL_UNINFERRED, "un-inferred OrNull element");
    or_null_rejected(OR_NULL_NESTED, "nested OrNull");
    or_null_rejected(OR_NULL_ZERO_NEWTYPE, "zero-represented newtype element");
}

#[test]
fn or_null_over_heap_element_checks() {
    assert!(
        prism::check(&prism::with_prelude(OR_NULL_OK)).is_ok(),
        "OrNull(String) with Null/This arms must check"
    );
    assert!(
        prism::check(&prism::with_prelude(OR_NULL_ORDINARY_UNARY)).is_ok(),
        "an ordinary unary datatype keeps its boxed wrapper"
    );
}

// `@ once` on a closure parameter is a sound, type-carried multiplicity contract.
// A single direct use checks; the type checker's contravariant subsumption catches
// handing the closure to a `@ many` context (E1998), and the linear-use pass
// catches direct reuse, aliasing, and capture under a lambda (E6059).

const ONCE_SINGLE_USE: &str = r"fn apply1(g : ((Int) -> Int) @ once, x : Int) : Int = g(x)
fn main() = println(apply1(\(n) -> n, 1))
";

const ONCE_DOUBLE_USE: &str = r"fn f(g : ((Int) -> Int) @ once) : Int = g(1) + g(2)
fn main() = println(f(\(n) -> n))
";

const ONCE_DELEGATION: &str = r"fn use2(g : (Int) -> Int) : Int = g(1) + g(2)
fn f(g : ((Int) -> Int) @ once) : Int = use2(g)
fn main() = println(f(\(n) -> n))
";

const ONCE_ALIAS: &str = r"fn f(g : ((Int) -> Int) @ once) : Int =
  let x = g
  x(1)
fn main() = println(f(\(n) -> n))
";

const ONCE_CAPTURE: &str = r"fn f(g : ((Int) -> Int) @ once) : Int = (\() -> g(1))()
fn main() = println(f(\(n) -> n))
";

const ONCE_PASS_ONCE: &str = r"fn apply1(g : ((Int) -> Int) @ once, x : Int) : Int = g(x)
fn f(g : ((Int) -> Int) @ once) : Int = apply1(g, 3)
fn main() = println(f(\(n) -> n))
";

// An inner binder that shadows the `@ once` parameter rebinds the name: uses of
// the shadow are a different variable and must not count against the contract.
// Here `g` is used once directly; the lambda's own `g` parameter is used twice.
const ONCE_SHADOWED: &str = r"fn f(g : ((Int) -> Int) @ once, x : Int) : Int =
  let twice = \(g : (Int) -> Int) -> g(g(0))
  g(x) + twice(\(n) -> n + 1)
fn main() = println(f(\(n) -> n, 5))
";

fn once_code(src: &str, what: &str) -> String {
    let err =
        prism::check(&prism::with_prelude(src)).expect_err(&format!("{what} must be rejected"));
    let Error::Type(ty) = &err else {
        panic!("expected a type error for {what}, got: {err}");
    };
    ty.code().unwrap_or("").to_string()
}

#[test]
fn once_single_use_and_pass_once_check() {
    assert!(
        prism::check(&prism::with_prelude(ONCE_SINGLE_USE)).is_ok(),
        "a single direct use of a `@ once` closure must check"
    );
    assert!(
        prism::check(&prism::with_prelude(ONCE_PASS_ONCE)).is_ok(),
        "passing a `@ once` closure to another `@ once` parameter must check"
    );
    assert!(
        prism::check(&prism::with_prelude(ONCE_SHADOWED)).is_ok(),
        "a shadowing inner binder must not count against the `@ once` contract"
    );
}

#[test]
fn once_direct_reuse_is_rejected() {
    assert_eq!(once_code(ONCE_DOUBLE_USE, "@ once double use"), "E6059");
    assert_eq!(once_code(ONCE_ALIAS, "@ once alias"), "E6059");
    assert_eq!(once_code(ONCE_CAPTURE, "@ once lambda capture"), "E6059");
}

#[test]
fn once_delegation_to_many_context_is_rejected() {
    // A `@ once` value in a `@ many` slot produces a contravariant subsumption
    // mismatch (a legacy `TypeFailure`, not a structured
    // catalogue error), so the pinned surface is its message, not a code.
    let err = prism::check(&prism::with_prelude(ONCE_DELEGATION))
        .expect_err("handing a `@ once` closure to a `@ many` context must be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("`@ once`") && msg.contains("more than once"),
        "delegation error must name the multiplicity contract, got: {msg}"
    );
}

// `@ portable` on a closure parameter is a mobility contract: the closure may
// capture only names that travel to a fresh runtime (a top-level function or
// constructor, another `@ portable` parameter, or a portable-typed parameter).
// Capturing a local closure, a `var` cell, or another nonportable value is
// rejected (E6060). It composes with `@ once` in the teleport contract.

const PORTABLE_TOP_LEVEL_OK: &str = "fn work() : Int = 42\n\
                                     fn run(f : (() -> Int) @ portable) : Int = f()\n\
                                     fn main() = println(run(\\() -> work()))\n";

const PORTABLE_SCALAR_PARAM_OK: &str = "fn run(f : (() -> Int) @ portable) : Int = f()\n\
                                        fn mk(x : Int) : Int = run(\\() -> x)\n\
                                        fn main() = println(mk(7))\n";

const PORTABLE_CAPTURE_CLOSURE: &str = "fn run(f : (() -> Int) @ portable) : Int = f()\n\
                                        fn o(g : (Int) -> Int) : Int = run(\\() -> g(1))\n\
                                        fn main() = println(o(\\(n) -> n))\n";

const PORTABLE_CAPTURE_VAR: &str = "fn run(f : (() -> Int) @ portable) : Int = f()\n\
                                    fn mk() : Int =\n  \
                                    var c := 3\n  \
                                    run(\\() -> c)\n\
                                    fn main() = println(mk())\n";

const TELEPORT_ONCE_PORTABLE_TWICE: &str =
    "fn teleport(f : (() -> Int) @ {once, portable}) : Int = f() + f()\n\
     fn main() = println(teleport(\\() -> 1))\n";

#[test]
fn portable_admits_code_refs_and_portable_data() {
    assert!(
        prism::check(&prism::with_prelude(PORTABLE_TOP_LEVEL_OK)).is_ok(),
        "a `@ portable` closure capturing only a top-level function must check"
    );
    assert!(
        prism::check(&prism::with_prelude(PORTABLE_SCALAR_PARAM_OK)).is_ok(),
        "a `@ portable` closure capturing a scalar parameter must check"
    );
}

#[test]
fn portable_rejects_nonportable_captures() {
    assert_eq!(
        once_code(PORTABLE_CAPTURE_CLOSURE, "portable captures a closure"),
        "E6060"
    );
    assert_eq!(
        once_code(PORTABLE_CAPTURE_VAR, "portable captures a var cell"),
        "E6060"
    );
}

#[test]
fn teleport_once_portable_composes_both_contracts() {
    // `@ {once, portable}` enforces the multiplicity check too: two calls exceed
    // `@ once` (E6059), independent of the portability of the closure.
    assert_eq!(
        once_code(TELEPORT_ONCE_PORTABLE_TWICE, "teleport used twice"),
        "E6059"
    );
}

// The stdlib `teleport` (Replay module) is the checked mobility boundary: its
// `@ {once, portable}` parameter makes every call enforce the portability and
// single-use contract on the closure handed to it. A closure that captures a
// nonportable local is rejected (E6060) exactly as a hand-written `@ portable`
// parameter would be.
const STDLIB_TELEPORT_OK: &str = "import Teleport (..)\n\
                                  fn work() : Int = 42\n\
                                  fn main() = println(teleport(\\() -> work()))\n";

const STDLIB_TELEPORT_NONPORTABLE: &str = "import Teleport (..)\n\
                                           fn o(g : (Int) -> Int) : Int = teleport(\\() -> g(1))\n\
                                           fn main() = println(o(\\(n) -> n))\n";

#[test]
fn stdlib_teleport_enforces_the_mobility_contract() {
    assert!(
        prism::check(&prism::with_prelude(STDLIB_TELEPORT_OK)).is_ok(),
        "teleporting a closure that captures only a top-level function must check"
    );
    assert_eq!(
        once_code(
            STDLIB_TELEPORT_NONPORTABLE,
            "teleport a nonportable capture"
        ),
        "E6060"
    );
}

// `@ noescape` on a function domain (`(Builder @ noescape) -> a`) is the
// scoped-token contract: the callback may use its argument but not let it
// outlive the call. The value analysis rejects the directly expressible escapes
// (returned, embedded in returned data, aliased then returned, captured by
// another closure); a call result stays opaque (the same documented hole as the
// `var` escape check). An argument that is not a closure literal, top-level
// function, or same-contract relay cannot be checked and is rejected (E6062).

const NOESCAPE_PRE: &str = "type Builder = MkBuilder(Int)\n\
                            fn finish(b : Builder) : Int =\n  \
                            match b of\n    \
                            MkBuilder(n) => n\n";

fn noescape_src(rest: &str) -> String {
    format!("{NOESCAPE_PRE}{rest}")
}

#[test]
fn noescape_consuming_callback_checks() {
    let ok = noescape_src(
        "fn with_builder(f : (Builder @ noescape) -> Int) : Int = f(MkBuilder(7))\n\
         fn main() = println(with_builder(\\(b) -> finish(b)))\n",
    );
    assert!(
        prism::check(&prism::with_prelude(&ok)).is_ok(),
        "a callback that only consumes its scoped token must check"
    );
}

#[test]
fn noescape_direct_escapes_are_rejected() {
    let returned = noescape_src(
        "fn keep(f : (Builder @ noescape) -> Builder) : Int = 0\n\
         fn main() = println(keep(\\(b) -> b))\n",
    );
    let embedded = noescape_src(
        "fn keep(f : (Builder @ noescape) -> (Builder, Int)) : Int = 0\n\
         fn main() = println(keep(\\(b) -> (b, 1)))\n",
    );
    let captured = noescape_src(
        "fn keep(f : (Builder @ noescape) -> (() -> Int)) : Int = 0\n\
         fn main() = println(keep(\\(b) -> \\() -> finish(b)))\n",
    );
    let aliased = noescape_src(
        "fn keep(f : (Builder @ noescape) -> Builder) : Int = 0\n\
         fn leak(b : Builder) : Builder =\n  \
         let x = b\n  \
         x\n\
         fn main() = println(keep(leak))\n",
    );
    for (what, src) in [
        ("returned token", returned),
        ("token embedded in returned data", embedded),
        ("token captured by returned closure", captured),
        ("token aliased then returned", aliased),
    ] {
        assert_eq!(once_code(&src, what), "E6061", "{what}");
    }
}

#[test]
fn noescape_uncheckable_argument_is_rejected() {
    let src = noescape_src(
        "fn use1(f : (Builder @ noescape) -> Int) : Int = f(MkBuilder(3))\n\
         fn pick(g : (Builder) -> Int) : Int = use1(g)\n\
         fn main() = println(pick(finish))\n",
    );
    assert_eq!(once_code(&src, "uncheckable noescape argument"), "E6062");
}

// Field types belong to constructors, so a match may refine the same label to
// a different type in each arm without making an unrefined projection safe.
#[test]
fn variant_local_shared_field_types_are_accepted() {
    let src = prism::with_prelude(
        r"type Shape = Circle { radius: Int } | Square { radius: Float }
fn radius_text(shape : Shape) : String =
  match shape of
    Circle { radius = radius } => show(radius)
    Square { radius = radius } => show(radius)
fn main() = println(radius_text(Circle { radius = 7 }))
",
    );
    prism::check(&src).expect("pattern refinement must permit constructor-local field types");
}

fn projection_error(src: &str, what: &str) {
    let err =
        prism::check(&prism::with_prelude(src)).expect_err(&format!("{what} must be rejected"));
    let Error::Type(ty) = &err else {
        panic!("expected a type error for {what}, got: {err}");
    };
    assert_eq!(ty.code(), Some("E1023"), "{what}: got {err}");
    assert!(
        err.to_string().contains("match a constructor first"),
        "{what}: diagnostic must name the repair: {err}"
    );
}

// A field present on only one constructor is partial on the unrefined nominal.
#[test]
fn constructor_specific_field_projection_is_rejected() {
    projection_error(
        "type Shape = Circle { radius: Int } | Square { side: Int }\n\
         fn radius(s : Shape) : Int = s.radius\n\
         fn main() = println(0)\n",
        "constructor-specific field projection",
    );
}

// Even a same-typed common field needs one lowering arm per constructor. Until
// projection facts carry that multi-arm evidence, accepting it would typecheck
// a program whose Core projection handles only one constructor.
#[test]
fn common_field_projection_without_multi_arm_evidence_is_rejected() {
    projection_error(
        "type Tagged = A { id: Int, kind: String } | B { id: Int }\n\
         fn tag_id(t : Tagged) : Int = t.id\n\
         fn main() = println(0)\n",
        "common field projection",
    );
}

// The same guard applies below a valid outer projection: `outer.inner` records
// one constructor, but `.id` still receives an unrefined sum.
#[test]
fn nested_sum_field_projection_is_rejected() {
    projection_error(
        "type Tagged = A { id: Int } | B { id: Int }\n\
         type Outer = Outer { inner: Tagged }\n\
         fn tag_id(outer : Outer) : Int = outer.inner.id\n\
         fn main() = println(0)\n",
        "nested sum field projection",
    );
}

// Bare `.name` is syntactically a field projection, never UFCS fallback. A
// same-named top-level function must not turn E1023 into a silent call.
#[test]
fn partial_projection_does_not_fall_back_to_ufcs() {
    projection_error(
        "type Shape = Circle { radius: Int } | Square { side: Int }\n\
         fn radius(_shape : Shape) : Int = 99\n\
         fn read(shape : Shape) : Int = shape.radius\n\
         fn main() = println(0)\n",
        "partial projection with a same-named function",
    );
}

#[test]
fn single_constructor_field_projection_checks() {
    let src = prism::with_prelude(
        "type Box = Box { value: Int }\n\
         fn value(box : Box) : Int = box.value\n\
         fn main() = println(value(Box { value = 22 }))\n",
    );
    prism::check(&src).expect("a single-constructor field projection must check");
}

#[test]
fn record_spread_from_unrefined_sum_is_rejected() {
    let src = prism::with_prelude(
        "type Shape = Circle { radius: Int } | Square { side: Int }\n\
         fn resize(shape : Shape) : Shape = Circle { ..shape, radius = 2 }\n\
         fn main() = println(0)\n",
    );
    let err = prism::check(&src).expect_err("constructor spread must prove the base layout");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E1024"), "got: {err}");
}

// A record pattern without `..` must bind every field of its constructor: the
// spread is what licenses omitting the rest. Before this check, `..` was parsed
// and dropped, so a forgotten field became a silent wildcard.
#[test]
fn record_pattern_without_spread_must_bind_all_fields() {
    let src = prism::with_prelude(
        "type P = P { x: Int, y: Int }\n\
         fn f(p : P) : Int = match p of\n  P { x = a } => a\n\
         fn main() = println(show(f(P { x = 1, y = 2 })))\n",
    );
    let err = prism::check(&src).expect_err("a partial record pattern without `..` must reject");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E4009"), "got: {err}");
}

// The same pattern with `..` is well formed: the spread ignores `y`.
#[test]
fn record_pattern_with_spread_is_accepted() {
    let src = prism::with_prelude(
        "type P = P { x: Int, y: Int }\n\
         fn f(p : P) : Int = match p of\n  P { x = a, .. } => a\n\
         fn main() = println(show(f(P { x = 1, y = 2 })))\n",
    );
    prism::check(&src).expect("a record pattern with `..` must be accepted");
}

/// One session of the interactive entry point: the lines are fed to the real
/// binary over its own input and the whole transcript comes back, since a
/// refusal is reported on the error stream and an accepted line prints its
/// value on the output stream.
fn repl_transcript(lines: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the interactive entry point");
    child
        .stdin
        .take()
        .expect("session input")
        .write_all(format!("{lines}:quit\n").as_bytes())
        .expect("drive the session");
    let out = child.wait_with_output().expect("session transcript");
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// A sum whose two constructors carry the same field, which is the shape that
/// makes both a projection and an update path ambiguous: nothing in the
/// unrefined type says which constructor a field access is aimed at.
const AMBIGUOUS_SUM: &str = "type Tagged = A { id: Int } | B { id: Int }\n";

// The interactive entry point reaches the checker without a file or a pipeline
// around it, so the constructor-ambiguity refusals are certified through it as
// well as through a compiled program. A field on an unrefined sum is refused in
// declaration position and in expression position alike; selecting the first
// constructor that happens to carry the label would make acceptance depend on
// how the program was entered.
#[test]
fn repl_refuses_unrefined_field_projection() {
    let out = repl_transcript(&format!(
        "{AMBIGUOUS_SUM}\
         fn tag_id(t : Tagged) : Int = t.id\n\
         let a = A {{ id = 1 }}\n\
         a.id\n"
    ));
    assert_eq!(
        out.matches("[E1023]").count(),
        2,
        "both the declared and the entered projection must be refused: {out}"
    );
    assert!(
        out.contains("match a constructor first"),
        "the refusal must name the repair: {out}"
    );
}

// The update path fails closed on the same shape, and it is the wider of the
// two: it refuses on the constructor count before it ever looks the field up,
// so a record update can never be aimed at a constructor the value may not be.
#[test]
fn repl_refuses_multi_constructor_update_path() {
    let out = repl_transcript(&format!(
        "{AMBIGUOUS_SUM}\
         fn bump(t : Tagged) : Tagged = {{ t | id = 1 }}\n\
         let a = A {{ id = 1 }}\n\
         {{ a | id = 2 }}\n"
    ));
    assert_eq!(
        out.matches("[E1013]").count(),
        2,
        "both the declared and the entered update path must be refused: {out}"
    );
    assert!(
        out.contains("single-constructor record"),
        "the refusal must name what the path needs: {out}"
    );
}

// Datatype arguments are invariant unless explicitly known covariant. Otherwise
// `Consumer(a)`, which stores `(a) -> Int`, could reverse a multiplicity widening.
const COVARIANT_DATATYPE_ARG: &str =
    include_str!("../fixtures/language/soundness/covariant_datatype_arg.pr");

#[test]
fn covariant_datatype_argument_is_rejected_at_source() {
    let src = prism::with_prelude(COVARIANT_DATATYPE_ARG);
    let err = prism::check(&src)
        .expect_err("an invariant datatype argument cannot widen `@ once` to `@ many`");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    // Reject during source checking rather than Typed-Core construction.
    assert_ne!(
        ty.code(),
        Some("E9996"),
        "the conversion must fail in source checking, not reach Typed-Core: {err}"
    );
    let text = err.to_string();
    assert!(
        text.contains("wrong_way") && text.contains("once"),
        "the rejection must name the function and the multiplicity reason: {err}"
    );
}

// A generalized local value is expanded and instantiated independently per use.
const POLYMORPHIC_LOCAL_LET: &str = include_str!("../cases/run/local_polymorphic_let.pr");

#[test]
fn a_polymorphic_local_let_instantiates_per_use() {
    let src = prism::with_prelude(POLYMORPHIC_LOCAL_LET);
    let run = prism::interpret(&src).expect("a polymorphic local `let` must check and run");
    assert_eq!(
        run.term, "1\nhi\n",
        "each use of the binding must instantiate on its own"
    );
}

// A computation-bound local remains monomorphic, so incompatible uses produce
// a source type error.
const COMPUTATION_LOCAL_LET: &str = r#"fn mk_id() = \(x) -> x
fn main() =
  let g = mk_id()
  println(g(1))
  println(g("hi"))
"#;

#[test]
fn a_local_let_never_reaches_typed_core_with_a_witness_conflict() {
    // Interpretation also exercises Typed-Core construction.
    let err = prism::interpret(&prism::with_prelude(COMPUTATION_LOCAL_LET))
        .expect_err("a computation-bound `let` used at two types must be rejected");
    let text = err.to_string();
    for code in ["E9996", "E9997"] {
        assert!(
            !text.contains(code),
            "the conflict must not reach typed-Core construction ({code}): {err}"
        );
    }
    let Error::Type(ty) = &err else {
        panic!("expected a source type error, got: {err}");
    };
    assert_eq!(
        ty.code(),
        Some("E1022"),
        "the two use types must disagree as a plain mismatch, got: {err}"
    );
}

// A value that closes over a local remains monomorphic and keeps its definition
// scope when a later binder shadows the captured name.
const OPEN_LOCAL_VALUE_SHADOWED: &str = r#"fn main() =
  let tag = "!"
  let mark = \(x) -> (tag, x)
  let tag = 9
  match mark(tag) of
    (a, _) => println(a)
"#;

#[test]
fn an_open_local_value_reads_its_definition_scope() {
    let run = prism::interpret(&prism::with_prelude(OPEN_LOCAL_VALUE_SHADOWED))
        .expect("an open local value used at one type must check and run");
    assert_eq!(
        run.term, "!\n",
        "the value must see the `tag` its definition closed over, not the use site's"
    );
}

// The same open value used at two types: with generalization declined, the
// disagreement is an ordinary source mismatch, never an internal typed-Core
// error and never an expansion.
const OPEN_LOCAL_VALUE_TWO_TYPES: &str = r#"fn main() =
  let tag = "!"
  let mark = \(x) -> (tag, x)
  println(show(mark(1)))
  println(show(mark(true)))
"#;

#[test]
fn an_open_local_value_stays_monomorphic() {
    let err = prism::interpret(&prism::with_prelude(OPEN_LOCAL_VALUE_TWO_TYPES))
        .expect_err("an open local value used at two types must be rejected");
    let text = err.to_string();
    for code in ["E9996", "E9997"] {
        assert!(
            !text.contains(code),
            "the conflict must not reach typed-Core construction ({code}): {err}"
        );
    }
    assert!(
        matches!(&err, Error::Type(_)),
        "expected a source type error, got: {err}"
    );
}

// The control that keeps the two refusals honest: on a single-constructor
// record the very same projection and update are unambiguous, and the session
// evaluates them rather than refusing everything it is handed.
#[test]
fn repl_accepts_single_constructor_field_paths() {
    let out = repl_transcript(
        "type Box = Box { value: Int }\n\
         let b = Box { value = 7 }\n\
         b.value\n\
         { b | value = 8 }\n",
    );
    assert!(
        out.contains("7 : Int"),
        "the projection must evaluate: {out}"
    );
    assert!(
        out.contains("Box(8) : Box"),
        "the update must evaluate: {out}"
    );
    assert!(
        !out.contains("Type Error"),
        "an unambiguous field path must not be refused: {out}"
    );
}
