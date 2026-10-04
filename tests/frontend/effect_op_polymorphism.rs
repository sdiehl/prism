//! An effect operation's type variables are the operation's own.
//!
//! A signature that mentions one — `ask(a) : Int` — has to build a *closed* scheme.
//! A variable left free joins the environment's free variables, which generalization
//! anchors on, so any declaration that spells a signature variable the same way is
//! generalized without it, and its own correct `given` constraint is refused as
//! ambiguous.

use std::path::Path;

use indoc::indoc;
use prism::{check_on, default_roots, report, report_on, with_prelude, Config};

/// An ordinary class, a declaration that mentions its own type variable under a
/// constraint, and an operation polymorphic in a variable it names in a parameter.
const SHARING_A_NAME: &str = indoc! {"
    class C(a)
      c : (a) -> Int

    effect Ask
      ask(a) : Int

    fn needs(x : a) : Int given C(a) = c(x)

    fn main() = 1
"};

/// The same program with the operation's variable spelled differently, so nothing
/// shares a name — the control for what the fault is.
const NOT_SHARING: &str = indoc! {"
    class C(a)
      c : (a) -> Int

    effect Ask
      ask(zz) : Int

    fn needs(x : a) : Int given C(a) = c(x)

    fn main() = 1
"};

/// The operation alone: no other declaration mentions `a` under a constraint.
const OPERATION_ALONE: &str = indoc! {"
    effect Ask
      ask(a) : Int

    fn main() = 1
"};

/// The declaration alone: no operation mentions `a`.
const DECLARATION_ALONE: &str = indoc! {"
    class C(a)
      c : (a) -> Int

    fn needs(x : a) : Int given C(a) = c(x)

    fn main() = 1
"};

/// What the operation is for: one polymorphic op, performed at two types.
const PERFORMED_AT_TWO_TYPES: &str = indoc! {r#"
    effect Ask
      ask(a) : Int

    fn one() : Int = ask(1)
    fn two() : Int = ask("x")
"#};

/// The same, but the operation's variable is its *result* as well as its parameter,
/// performed at two different result types inside one row. This is what a capability
/// needs (one unparameterised effect answering whatever each call site asked for)
/// and what an effect *parameter* cannot express, being fixed once per row.
const TWO_RESULT_TYPES_IN_ONE_ROW: &str = indoc! {r#"
    type Key(a) = Key { id : String }

    effect Read
      read(Key(a)) : a

    fn both() : (Int, String) ! {Read} =
      ( read(Key { id = "clock" }), read(Key { id = "url" }) )
"#};

/// A monomorphic operation, unaffected by any of this.
const MONOMORPHIC: &str = indoc! {"
    effect Ask
      ask(Int) : Int

    fn one() : Int = ask(1)
"};

/// One operation performed at a single type, handled by a clause that passes an
/// *enclosing function's* type variable through the continuation.
///
/// A clause binds the operation's own variables, and an operation's variable means
/// "whatever type the perform site chose" — here `String`, for `id(\"hello\")`, which is
/// not the type of `run`'s `y`. Passing `y` where the operation's value belongs is
/// therefore a mismatch, and it has to be found here: a checker that accepts it
/// reifies the value at the wrong type, and the fault surfaces at runtime instead,
/// inside `str_len`.
///
/// Unlike the cases above, this one needs the prelude (`str_len`, `println`), so it is
/// checked with roots rather than with nothing resolved for it.
const CAPTURING_HANDLER: &str = indoc! {r#"
    effect Id
      id(a) : a

    fn go() : Int ! {Id} =
      let s = id("hello")
      str_len(s) + 0

    fn run(y : a) : Unit =
      handle go() with
        id(x) resume k => k(y)
        return r => println("{r}")

    fn main() = run(42)
"#};

/// Checked with nothing resolved for it: `Int` is built in, and every name these
/// programs use is declared in the program itself.
fn check(src: &str) -> Result<(), String> {
    check_on(src, &[]).map(|_| ()).map_err(|e| e.to_string())
}

/// The same, for a program that uses the standard library: `default_roots` is what
/// the prelude's own `import Data…` lines resolve against (see `prelude_capture.rs`).
fn check_with_prelude(src: &str) -> Result<(), String> {
    check_on(&with_prelude(src), &default_roots(Path::new(".")))
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn an_operation_variable_is_not_shared_with_another_declaration() {
    if let Err(e) = check(SHARING_A_NAME) {
        panic!("the operation's variable reached a declaration beside it: {e}");
    }
    let pipeline = report(SHARING_A_NAME);
    assert!(
        !pipeline.contains("ambiguous constraint"),
        "the pipeline refuses it too:\n{pipeline}"
    );
}

#[test]
fn spelling_the_operation_variable_differently_changes_nothing_else() {
    if let Err(e) = check(NOT_SHARING) {
        panic!("nothing shares a name here: {e}");
    }
}

#[test]
fn neither_half_refuses_on_its_own() {
    if let Err(e) = check(OPERATION_ALONE) {
        panic!("the operation alone: {e}");
    }
    if let Err(e) = check(DECLARATION_ALONE) {
        panic!("the declaration alone: {e}");
    }
}

#[test]
fn the_operation_is_polymorphic_at_each_perform_site() {
    if let Err(e) = check(PERFORMED_AT_TWO_TYPES) {
        panic!("one op performed at two types: {e}");
    }
}

#[test]
fn an_operation_variable_is_instantiated_at_each_result_type() {
    if let Err(e) = check(TWO_RESULT_TYPES_IN_ONE_ROW) {
        panic!("one op at two result types in one row: {e}");
    }
}

#[test]
fn a_monomorphic_operation_is_unaffected() {
    if let Err(e) = check(MONOMORPHIC) {
        panic!("monomorphic op: {e}");
    }
}

/// A clause binds the operation's own variables, so passing an enclosing function's
/// variable where the operation's value belongs is a mismatch. The check belongs to
/// typechecking rather than to the runtime: what it prevents is a program that checks
/// and then reifies the value at the wrong type, which is a soundness hole rather than
/// a nuisance.
#[test]
fn a_clause_may_not_pass_an_enclosing_functions_variable_for_the_operations() {
    let err = check_with_prelude(CAPTURING_HANDLER)
        .expect_err("the clause passes `run`'s variable where the operation's belongs");
    assert!(
        err.contains("type mismatch"),
        "a named mismatch, not an internal invariant: {err}"
    );

    // And the same through the pipeline, where it carries its E-code: a reader of a
    // build log should be able to see what kind of fault it is.
    let pipeline = report_on(
        &with_prelude(CAPTURING_HANDLER),
        &default_roots(Path::new(".")),
        &Config::default(),
    );
    assert!(
        pipeline.contains("E1022") && pipeline.contains("type mismatch"),
        "the pipeline reports it as a type error too:\n{pipeline}"
    );
}

/// A clause's own existentials outlive it. A nested `??` checks the inner lookup
/// inside the outer `fail` clause, and that lookup's `Ord` constraint defaults after
/// the clause closes; scoping the clause by truncation would strand it.
const NESTED_DEFAULTS: &str = indoc! {r#"
    fn main() =
      let cfg = map_from_list([("host", 80)])
      println(cfg.at_map("port") ?? cfg.at_map("https") ?? 443)
"#};

/// A clause that keeps the operation's value at the operation's own type, through
/// locals of its own, is generic and accepted.
const GENERIC_CLAUSE: &str = indoc! {r#"
    effect Id
      id(a) : a

    fn go() : Int ! {Id} = id(41) + 1

    fn main() =
      handle go() with
        id(x) resume k =>
          let y = x
          k(y)
        return r => println("{r}")
"#};

#[test]
fn a_clause_leaves_deferred_constraints_resolvable() {
    if let Err(e) = check_with_prelude(NESTED_DEFAULTS) {
        panic!("nested `??` lost its deferred constraint: {e}");
    }
}

#[test]
fn a_clause_may_use_the_operations_value_at_its_own_type() {
    if let Err(e) = check_with_prelude(GENERIC_CLAUSE) {
        panic!("a generic clause was refused: {e}");
    }
}
