// Declaration-order independence of top-level inference. A function's inferred
// type must not depend on where it (or its callees) are declared, and a mutually
// recursive group is inferred against shared monomorphic variables, then
// generalized once (textbook Hindley-Milner for a recursion group).

use std::collections::BTreeMap;

fn sigs(src: &str) -> BTreeMap<String, String> {
    let checked = prism::check(&prism::with_prelude(src)).expect("program should type check");
    checked
        .decls
        .iter()
        .map(|d| (d.name.clone(), d.ty.show()))
        .collect()
}

fn sig(src: &str, name: &str) -> String {
    sigs(src)
        .get(name)
        .cloned()
        .unwrap_or_else(|| panic!("no top-level declaration `{name}`"))
}

fn check_err(src: &str) -> String {
    match prism::check(&prism::with_prelude(src)) {
        Ok(_) => panic!("expected a type error, but the program checked"),
        Err(e) => e.to_string(),
    }
}

// The cycle's structure lives in `g` (the `match` pins its argument to a list)
// and must flow back to `f`, whose own body (`f(x) = g(x)`) constrains nothing.
// On a structure-free mutual stub `f` would infer as `(a) -> b`; against shared
// monomorphic variables it infers the precise `(List(a)) -> Int`.
const FLOW_FWD: &str = "\
fn f(x) = g(x)

fn g(y) =
  match y of
    Nil => 0
    Cons(_, rest) => f(rest)
";

const FLOW_REV: &str = "\
fn g(y) =
  match y of
    Nil => 0
    Cons(_, rest) => f(rest)

fn f(x) = g(x)
";

#[test]
fn mutual_recursion_structure_flows_through_the_cycle() {
    assert_eq!(sig(FLOW_FWD, "f"), "forall a. (List(a)) -> Int");
    assert_eq!(sig(FLOW_FWD, "g"), "forall a. (List(a)) -> Int");
}

#[test]
fn mutual_recursion_is_declaration_order_independent() {
    assert_eq!(sig(FLOW_FWD, "f"), sig(FLOW_REV, "f"));
    assert_eq!(sig(FLOW_FWD, "g"), sig(FLOW_REV, "g"));
    assert_eq!(sig(FLOW_REV, "f"), "forall a. (List(a)) -> Int");
}

// Annotated polymorphic recursion: `poly` calls itself with `[x] : List(a)` for
// the `a` parameter, so it is used at `(Int, List(a)) -> Int`. The signature is
// the contract the recursive call checks against, so this is accepted.
#[test]
fn annotated_polymorphic_recursion_is_accepted() {
    let src = "\
fn poly(n : Int, x : a) : Int =
  if n == 0 then 0 else poly(n - 1, [x])
";
    assert_eq!(sig(src, "poly"), "forall a. (Int, a) -> Int");
}

// The same shape without a signature cannot be typed monomorphically; the error
// must name the remedy.
#[test]
fn unannotated_polymorphic_recursion_is_rejected_with_remedy() {
    let src = "\
fn poly(n, x) =
  if n == 0 then 0 else poly(n - 1, [x])
";
    let err = check_err(src);
    assert!(
        err.contains("add a type signature"),
        "expected a polymorphic-recursion remedy hint, got: {err}"
    );
}

#[test]
fn unannotated_mutual_polymorphic_recursion_is_rejected_with_remedy() {
    let src = "\
fn pa(n, x) =
  if n == 0 then 0 else pb(n - 1, [x])

fn pb(n, x) =
  if n == 0 then 1 else pa(n - 1, [x])
";
    let err = check_err(src);
    assert!(
        err.contains("add a type signature"),
        "expected a polymorphic-recursion remedy hint, got: {err}"
    );
}

// A constant in a cycle with a function (`k = f(0)`, `f(n) = .. k ..`) flows
// through the same component machinery: the constant is mono-seeded as a value,
// inferred, and generalized by value restriction.
#[test]
fn constant_in_a_cycle_with_a_function() {
    let src = "\
let k = f(0)

fn f(n : Int) : Int =
  if n == 0 then 0 else k
";
    assert_eq!(sig(src, "k"), "Int");
    assert_eq!(sig(src, "f"), "(Int) -> Int");
}

// The call graph over-approximates: a local `dup` that shadows the top-level
// `dup` adds a spurious `caller -> dup` edge. That edge must never change
// inference, so `caller` stays fully polymorphic rather than being pinned to the
// top-level `dup : (Int) -> Int`.
#[test]
fn shadowing_local_sharing_a_top_level_name_is_sound() {
    let src = "\
fn dup(n) = n + n

fn caller(z) =
  let dup = \\(w) -> w
  dup(z)
";
    assert_eq!(sig(src, "dup"), "(Int) -> Int");
    assert_eq!(sig(src, "caller"), "forall a. (a) -> a");
}
