//! Shared tail-recursion / TRMC classification.
//!
//! One analysis, two consumers:
//! `check_fip` (`core::fbip`) reads it to PROVE a `fip` function runs in
//! constant stack, and `emit.rs` reads it to lower a recursive tail into a
//! loop. Keeping the decision here means a `fip` function is accepted exactly
//! when codegen can in fact make it constant-stack: the static promise and the
//! generated code can never disagree because they share this module.
//!
//! TRMC (tail recursion modulo constructor / addition): a function whose
//! recursive call feeds exactly one constructor field in tail position, like
//! `Cons(y, map(f, rest))`, or sits under an associative `1 + f(x)`, runs in
//! constant stack once the backend turns the cons/add into a hole-passing or
//! accumulator loop. A plain tail call is the degenerate case (no surrounding
//! constructor). Anything else grows the stack one frame per recursive step.

use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{Comp, Core, CoreOp, Value};
use super::fv;
use crate::sym::Sym;

// A heap tag / field index as `i64`. Mirrors `emit::idx64`: a count that large
// needs an >8-exabyte program on an LP64 host, so saturate rather than panic.
fn idx64(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

// The two ways a recursive tail loops: a constructor hole passed down the chain,
// or an integer accumulator. A function realizes at most one of them.
#[derive(Clone, Copy, Debug)]
pub enum TrmcMode {
    Hole,
    Acc,
}

// One recursive-tail site, resolved against the continuation that follows the
// call. `Ctor` carries everything codegen needs to allocate the cell and thread
// the hole; `Acc` carries the other addend.
#[derive(Debug)]
pub enum TrmcShape<'a> {
    Ctor {
        token: Option<&'a Sym>,
        tag: i64,
        fields: &'a [Value],
        hole: usize,
    },
    Acc(&'a Value),
}

fn occurs(v: &Value, x: &str) -> usize {
    match v {
        Value::Var(y) => usize::from(*y == x),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().map(|f| occurs(f, x)).sum(),
        Value::Thunk(c) => 2 * usize::from(fv::comp(c).iter().any(|s| *s == x)),
        _ => 0,
    }
}

fn ctor_shape<'a>(v: &'a Value, x: &str, token: Option<&'a Sym>) -> Option<TrmcShape<'a>> {
    let (tag, fields) = match v {
        Value::Ctor(_, t, fs) => (idx64(*t), fs.as_slice()),
        Value::Tuple(fs) => (0, fs.as_slice()),
        _ => return None,
    };
    let hole = fields
        .iter()
        .position(|f| matches!(f, Value::Var(y) if *y == x))?;
    let total: usize = fields.iter().map(|f| occurs(f, x)).sum();
    (total == 1).then_some(TrmcShape::Ctor {
        token,
        tag,
        fields,
        hole,
    })
}

// Given the continuation `k` after a recursive call bound to `x`, decide which
// (if any) TRMC shape the tail realizes: `x` feeding a single constructor field
// (with or without a reuse token), or `x` as one addend of an `Int +`.
#[must_use]
pub fn trmc_shape<'a>(k: &'a Comp, x: &str) -> Option<TrmcShape<'a>> {
    match k {
        Comp::Return(v) => ctor_shape(v, x, None),
        Comp::Reuse(Value::Var(tok), v) if *tok != x => ctor_shape(v, x, Some(tok)),
        Comp::Prim(CoreOp::Add, a, b) => match (occurs(a, x), occurs(b, x)) {
            (1, 0) if matches!(a, Value::Var(_)) => Some(TrmcShape::Acc(b)),
            (0, 1) if matches!(b, Value::Var(_)) => Some(TrmcShape::Acc(a)),
            _ => None,
        },
        _ => None,
    }
}

fn scan_trmc(c: &Comp, name: &str, arity: usize, ctor: &mut bool, acc: &mut bool) {
    match c {
        Comp::Bind(m, x, n) => {
            if let Comp::Call(g, args) = m.as_ref() {
                if *g == name && args.len() == arity {
                    match trmc_shape(n, x.as_str()) {
                        Some(TrmcShape::Ctor { .. }) => return *ctor = true,
                        Some(TrmcShape::Acc(_)) => return *acc = true,
                        None => {}
                    }
                }
            }
            scan_trmc(n, name, arity, ctor, acc);
        }
        Comp::If(_, t, e) => {
            scan_trmc(t, name, arity, ctor, acc);
            scan_trmc(e, name, arity, ctor, acc);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                scan_trmc(b, name, arity, ctor, acc);
            }
        }
        _ => {}
    }
}

// The whole-function decision codegen acts on: does the body's self-recursion
// loop via a constructor hole, an accumulator, or not at all? A body mixing both
// shapes returns `None` (no single loop realizes it), so codegen leaves it a
// plain recursive function and the bounded-stack check must reject it as `fip`.
#[must_use]
pub fn trmc_mode(name: &str, arity: usize, body: &Comp) -> Option<TrmcMode> {
    let (mut ctor, mut acc) = (false, false);
    scan_trmc(body, name, arity, &mut ctor, &mut acc);
    match (ctor, acc) {
        (true, false) => Some(TrmcMode::Hole),
        (false, true) => Some(TrmcMode::Acc),
        _ => None,
    }
}

// Elaboration nests binds to the left, hiding the recursive call from the tail
// pattern; the monad associativity law `(a to y; b) to x; k` ==
// `a to y; (b to x; k)` flattens them. Skipped when it would capture y in k.
// Codegen runs this before lowering, so the bounded-stack check runs it too: the
// classification must see the same shape the backend lowers.
#[must_use]
pub fn reassoc(c: &Comp) -> Comp {
    match c {
        Comp::Bind(m, x, n) => rebind(reassoc(m), *x, reassoc(n)),
        Comp::If(v, t, e) => Comp::If(v.clone(), Box::new(reassoc(t)), Box::new(reassoc(e))),
        Comp::Case(v, arms) => Comp::Case(
            v.clone(),
            arms.iter().map(|(p, b)| (p.clone(), reassoc(b))).collect(),
        ),
        other => other.clone(),
    }
}

fn rebind(m: Comp, x: Sym, n: Comp) -> Comp {
    match m {
        Comp::Bind(a, y, b) if y == "_" || (y != x && !fv::comp(&n).contains(&y)) => {
            Comp::Bind(a, y, Box::new(rebind(*b, x, n)))
        }
        other => Comp::Bind(Box::new(other), x, Box::new(n)),
    }
}

// How a recursive call site sits in the stack. Tail and the two TRMC shapes all
// lower to a loop; `NonTail` is a real frame per recursive step.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TailClass {
    Tail,
    TrmcCons,
    TrmcAdd,
    NonTail,
}

// Classify every call to a member of `group` reachable within `body`'s own
// evaluation, in source order. Calls hidden inside a thunk, lambda, or handler
// run in a later, separate frame and do not grow THIS body's stack, so the walk
// does not descend into them; only the `Bind`/`If`/`Case` control flow of the
// current frame is followed. `self_name`/`self_arity` decide TRMC and plain-tail
// eligibility, which the backend only realizes for a saturated self-call (and a
// same-arity mutual tail call, via musttail).
#[must_use]
pub fn recursive_calls(
    body: &Comp,
    self_name: Sym,
    self_arity: usize,
    group: &BTreeSet<Sym>,
) -> Vec<(Sym, TailClass)> {
    let mut out = Vec::new();
    walk(&reassoc(body), self_name, self_arity, group, true, &mut out);
    out
}

fn walk(
    c: &Comp,
    self_name: Sym,
    self_arity: usize,
    group: &BTreeSet<Sym>,
    tail: bool,
    out: &mut Vec<(Sym, TailClass)>,
) {
    let recur = |c, tail, out: &mut _| walk(c, self_name, self_arity, group, tail, out);
    match c {
        Comp::Bind(m, x, n) => {
            // A tail-position bind whose head is a self-call feeding a single
            // constructor field / one addend of `+` in the continuation is the
            // TRMC tail the backend turns into a loop.
            if tail {
                if let Comp::Call(g, args) = m.as_ref() {
                    if *g == self_name && args.len() == self_arity {
                        if let Some(shape) = trmc_shape(n, x.as_str()) {
                            out.push((
                                *g,
                                match shape {
                                    TrmcShape::Ctor { .. } => TailClass::TrmcCons,
                                    TrmcShape::Acc(_) => TailClass::TrmcAdd,
                                },
                            ));
                            // The continuation only assembles the cons/acc; any
                            // further recursive call in it is a real frame.
                            recur(n, false, out);
                            return;
                        }
                    }
                }
            }
            // The bound head never runs in tail position; the continuation
            // inherits this site's tail-ness.
            recur(m, false, out);
            recur(n, tail, out);
        }
        Comp::If(_, t, e) => {
            recur(t, tail, out);
            recur(e, tail, out);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                recur(b, tail, out);
            }
        }
        Comp::Call(g, args) if group.contains(g) => {
            // A bare tail call loops via musttail only when its arity matches
            // the current frame's (self-call, or a same-arity mutual tail).
            let cls = if tail && args.len() == self_arity {
                TailClass::Tail
            } else {
                TailClass::NonTail
            };
            out.push((*g, cls));
        }
        _ => {}
    }
}

// The call graph over user functions. An edge is a direct call head (`calls_in`,
// which `fv` deliberately drops) UNIONED with any first-class reference (`fv`,
// for a function flowing as a bare value). Missing a direct-call edge would
// shrink an SCC and let a mutually recursive non-tail cycle slip the
// bounded-stack check, so both sources matter; over-approximating via `fv` only
// grows an SCC, which is safe (it demands tail recursion of a few more calls).
fn call_graph(core: &Core, users: &BTreeSet<Sym>, refs: bool) -> BTreeMap<Sym, BTreeSet<Sym>> {
    core.fns
        .iter()
        .map(|f| {
            let mut heads = Vec::new();
            super::cbpv::calls_in(&f.body, &mut heads);
            let edges: BTreeSet<Sym> = if refs {
                heads
                    .into_iter()
                    .chain(fv::comp(&f.body))
                    .filter(|n| users.contains(n))
                    .collect()
            } else {
                heads.into_iter().filter(|n| users.contains(n)).collect()
            };
            (f.name, edges)
        })
        .collect()
}

fn reaches(adj: &BTreeMap<Sym, BTreeSet<Sym>>, start: Sym) -> BTreeSet<Sym> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(n) = stack.pop() {
        if seen.insert(n) {
            if let Some(es) = adj.get(&n) {
                stack.extend(es.iter().copied());
            }
        }
    }
    seen
}

/// The strongly connected component of `f` in the user-function call graph.
///
/// This is the mutual-recursion group whose members must all tail-recurse for
/// `f` to be `fip`. Always contains `f` itself (a non-recursive function gets a
/// singleton, so it has no in-group call sites to constrain).
#[must_use]
pub fn scc_of(core: &Core, users: &BTreeSet<Sym>, f: Sym) -> BTreeSet<Sym> {
    scc_in(&call_graph(core, users, true), f)
}

/// The SCC of `f` using only direct-call edges (no first-class references).
///
/// This is a subset of [`scc_of`]: a member present here recurses with `f`
/// through actual calls, whereas a member only in [`scc_of`] is tied to `f`
/// solely by a function flowing as a value. The bounded-stack rule uses the
/// sound `scc_of`; this finer view only sharpens the rejection message.
#[must_use]
pub fn scc_of_calls(core: &Core, users: &BTreeSet<Sym>, f: Sym) -> BTreeSet<Sym> {
    scc_in(&call_graph(core, users, false), f)
}

fn scc_in(adj: &BTreeMap<Sym, BTreeSet<Sym>>, f: Sym) -> BTreeSet<Sym> {
    let fwd = reaches(adj, f);
    let mut scc = BTreeSet::new();
    scc.insert(f);
    for g in fwd {
        if g != f && reaches(adj, g).contains(&f) {
            scc.insert(g);
        }
    }
    scc
}

#[cfg(test)]
mod tests {
    use super::super::cbpv::{CoreFn, CorePat};
    use super::*;

    fn group(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::from(*n)).collect()
    }

    // f(x) bound to t, then `k`; the classic recursive-call-feeding-continuation
    // shape every TRMC tail elaborates to.
    fn bind_call(args: Vec<Value>, k: Comp) -> Comp {
        Comp::Bind(
            Box::new(Comp::Call("f".into(), args)),
            "t".into(),
            Box::new(k),
        )
    }

    fn classes(body: &Comp, arity: usize) -> Vec<TailClass> {
        recursive_calls(body, "f".into(), arity, &group(&["f"]))
            .into_iter()
            .map(|(_, c)| c)
            .collect()
    }

    #[test]
    fn bare_self_tail_call_is_tail() {
        let body = Comp::Call("f".into(), vec![Value::Var("x".into())]);
        assert_eq!(classes(&body, 1), [TailClass::Tail]);
    }

    #[test]
    fn self_call_feeding_a_prim_is_nontail() {
        // `f(x) * x` keeps the frame alive to multiply the result.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Mul, Value::Var("t".into()), Value::Var("x".into())),
        );
        assert_eq!(classes(&body, 1), [TailClass::NonTail]);
    }

    #[test]
    fn self_call_under_one_ctor_field_is_trmc_cons() {
        // `Cons(h, f(x))`: the result sits in exactly one constructor field.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons]);
    }

    #[test]
    fn self_call_under_addition_is_trmc_add() {
        // `1 + f(x)`: the result is one addend of an associative add.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Add, Value::Int(1), Value::Var("t".into())),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcAdd]);
    }

    #[test]
    fn reuse_token_ctor_tail_is_trmc_cons() {
        // The reuse-lowered form `reuse tok as Cons(h, f(x))` is still a cons tail.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Reuse(
                Value::Var("tok".into()),
                Value::Ctor(
                    "Cons".into(),
                    1,
                    vec![Value::Var("h".into()), Value::Var("t".into())],
                ),
            ),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons]);
    }

    #[test]
    fn second_recursive_call_in_a_field_is_nontail() {
        // `Cons(g(x), f(x))` (g == f): only one occurrence can be the hole, so
        // the other branch of the tree is a real recursive frame.
        let inner = Comp::Bind(
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
            "h".into(),
            Box::new(Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            ))),
        );
        let body = bind_call(vec![Value::Var("x".into())], inner);
        // Inner self-call is non-tail; outer feeds the single hole (TrmcCons).
        let got = classes(&body, 1);
        assert!(got.contains(&TailClass::NonTail), "{got:?}");
        assert!(got.contains(&TailClass::TrmcCons), "{got:?}");
    }

    #[test]
    fn wrong_arity_self_call_is_nontail() {
        // A saturated self-call must match the frame's arity to musttail.
        let body = Comp::Call("f".into(), vec![Value::Var("x".into())]);
        assert_eq!(classes(&body, 2), [TailClass::NonTail]);
    }

    #[test]
    fn branches_classify_independently() {
        let then = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        let els = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Add, Value::Int(1), Value::Var("t".into())),
        );
        let body = Comp::If(Value::Bool(true), Box::new(then), Box::new(els));
        let got = classes(&body, 1);
        assert!(got.contains(&TailClass::TrmcCons) && got.contains(&TailClass::TrmcAdd));
    }

    #[test]
    fn case_arm_tail_call_is_tail() {
        let arm = (
            CorePat::Ctor("Cons".into(), vec![Some("h".into()), Some("t".into())]),
            Comp::Call("f".into(), vec![Value::Var("t".into())]),
        );
        let body = Comp::Case(Value::Var("xs".into()), vec![arm]);
        assert_eq!(classes(&body, 1), [TailClass::Tail]);
    }

    fn fnamed(name: &str, body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            params: vec![],
            body,
        }
    }

    #[test]
    fn scc_is_singleton_for_nonrecursive() {
        let core = Core {
            fns: vec![fnamed("f", Comp::Return(Value::Unit))],
        };
        let scc = scc_of(&core, &group(&["f"]), "f".into());
        assert_eq!(scc, group(&["f"]));
    }

    #[test]
    fn scc_captures_mutual_recursion() {
        // f -> g -> f is one component; a lone h sharing the graph is excluded.
        let core = Core {
            fns: vec![
                fnamed("f", Comp::Call("g".into(), vec![])),
                fnamed("g", Comp::Call("f".into(), vec![])),
                fnamed("h", Comp::Call("f".into(), vec![])),
            ],
        };
        let users = group(&["f", "g", "h"]);
        assert_eq!(scc_of(&core, &users, "f".into()), group(&["f", "g"]));
        // h reaches f but f never reaches h, so h is its own component.
        assert_eq!(scc_of(&core, &users, "h".into()), group(&["h"]));
    }

    #[test]
    fn reference_only_cycle_splits_scc_views() {
        // f calls g directly; g merely returns f as a first-class value (a
        // reference, not a call). The sound `scc_of` ties them together, but the
        // direct-call view keeps them apart, which is what lets the rejection say
        // the group exists only because a function flows as a value.
        let core = Core {
            fns: vec![
                fnamed("f", Comp::Call("g".into(), vec![])),
                fnamed("g", Comp::Return(Value::Var("f".into()))),
            ],
        };
        let users = group(&["f", "g"]);
        assert_eq!(scc_of(&core, &users, "f".into()), group(&["f", "g"]));
        assert_eq!(scc_of_calls(&core, &users, "f".into()), group(&["f"]));
    }
}
