// Source-soundness regression tests. Each program below isolates an
// effect, handler, or coeffect shape
// that must be rejected because accepting it would let a program observe which
// lowering tier fired (a duplicate arm silently shadowing, a partial handler
// leaving an operation undischarged, a borrow leaking through an open row, a
// `once` continuation resumed off the tail). These cases prevent silent
// regressions into acceptance: every negative test asserts both
// rejection and the exact structured diagnostic code, and one positive control
// proves the coverage rule does not over-reject a fully covered handler.

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
    assert_eq!(ty.code(), Some("E5011"), "got: {err}");
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
}

#[test]
fn or_null_over_heap_element_checks() {
    assert!(
        prism::check(&prism::with_prelude(OR_NULL_OK)).is_ok(),
        "OrNull(String) with Null/This arms must check"
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
    // Contravariant subsumption: a `@ once` value cannot fill a `@ many` slot.
    // This is a subsumption mismatch (a legacy `TypeFailure`, not a structured
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
