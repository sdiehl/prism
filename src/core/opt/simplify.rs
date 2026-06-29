//! The gentle simplifier: the fixed-point local-rewrite workhorse.
//!
//! Bundles the cheap, parity-safe Core simplifications and runs them to a fixed
//! point:
//!
//! - Case-of-known-constructor: a `Case` whose scrutinee is a known constructor,
//!   tuple, or literal (directly, or through a `let`) reduces to the matching
//!   arm, with its fields rebound.
//! - Trivial copy-propagation: a `let` binding a variable or literal is inlined
//!   at its uses (a trivial value duplicates for free and carries no effect).
//! - Dead-let elimination: a `let` whose right-hand side is a pure `Return` and
//!   whose binder is unused is dropped.
//! - Constant folding: a `Prim` over integer literals reduces to its result. It
//!   mirrors the evaluator's i64 fast path exactly and folds only the cases that
//!   path keeps in i64, so it stays parity-safe (see `const_fold`).
//!
//! The simplifier is a late pass, run after effect lowering (the var/State fusion
//! analysis matches Core shapes that copy-propagation would otherwise destroy);
//! it never introduces rc (`Dup`/`Drop`/`WithReuse`/`Reuse`) nodes, though it
//! descends through any present.

use std::collections::{BTreeMap, BTreeSet};

use super::super::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use super::super::fv;
use super::super::traverse::Rewrite;
use crate::sym::Sym;

// A runaway guard: a correct fixed point converges far below this, so exceeding
// it means a rewrite is fighting itself.
const MAX_TICKS: u64 = 5_000_000;

/// Simplify to a fixed point, returning the result and the total rewrites fired.
pub(crate) fn simplify_counted(core: &Core) -> (Core, u64) {
    let mut fns = core.fns.clone();
    let mut total = 0u64;
    loop {
        let mut s = Simplifier { ticks: 0 };
        let env = Env::new();
        fns = fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                body: s.comp(&f.body, &env),
            })
            .collect();
        total += s.ticks;
        assert!(
            total <= MAX_TICKS,
            "simplifier exceeded {MAX_TICKS} ticks (non-convergent rewrite)"
        );
        if s.ticks == 0 {
            break;
        }
    }
    (Core { fns }, total)
}

// Maps a let binder to the value it is known to hold, for the region where that
// is still true.
type Env = BTreeMap<Sym, Value>;

struct Simplifier {
    ticks: u64,
}

// A value worth remembering for a binder: a constructor or tuple (enables
// case-of-known-constructor) or a trivial value (enables copy-propagation). A
// thunk is not tracked, since inlining it could duplicate work.
const fn known(v: &Value) -> bool {
    matches!(v, Value::Ctor(..) | Value::Tuple(_)) || trivial(v)
}

const fn trivial(v: &Value) -> bool {
    matches!(
        v,
        Value::Var(_)
            | Value::Int(_)
            | Value::I64(_)
            | Value::U64(_)
            | Value::Float(_)
            | Value::Bool(_)
            | Value::Unit
            | Value::Str(_)
    )
}

// Drop env entries a binder invalidates: those whose key it shadows, and those
// whose remembered value mentions a shadowed name (inlining which would capture).
fn narrow(env: &Env, bs: &[Sym]) -> Env {
    if bs.is_empty() {
        return env.clone();
    }
    let set: BTreeSet<Sym> = bs.iter().copied().collect();
    env.iter()
        .filter(|(k, v)| !set.contains(k) && fv::value(v).is_disjoint(&set))
        .map(|(k, v)| (*k, v.clone()))
        .collect()
}

fn pat_binders(p: &CorePat) -> Vec<Sym> {
    let mut s = fv::Set::new();
    fv::pat_vars(p, &mut s);
    s.into_iter().collect()
}

// Bindings produced by matching `pat` against the known value `kv`, or `None` if
// the pattern cannot match it.
fn pat_match(pat: &CorePat, kv: &Value) -> Option<Vec<(Sym, Value)>> {
    let fields_binds = |binders: &[Option<Sym>], fields: &[Value]| {
        binders
            .iter()
            .zip(fields)
            .filter_map(|(b, f)| b.map(|s| (s, f.clone())))
            .collect()
    };
    match (pat, kv) {
        (CorePat::Wild, _) => Some(Vec::new()),
        (CorePat::Var(y), _) => Some(vec![(*y, kv.clone())]),
        (CorePat::Ctor(c, binders), Value::Ctor(c2, _, fields))
            if c == c2 && binders.len() == fields.len() =>
        {
            Some(fields_binds(binders, fields))
        }
        (CorePat::Tuple(binders), Value::Tuple(fields)) if binders.len() == fields.len() => {
            Some(fields_binds(binders, fields))
        }
        _ => None,
    }
}

// Resolve a scrutinee to a known constructor/tuple/literal, through one env hop.
// A variable bound to another variable is not chased here; copy-prop rewrites it
// first.
fn resolve(scrut: &Value, env: &Env) -> Option<Value> {
    match scrut {
        Value::Ctor(..) | Value::Tuple(_) => Some(scrut.clone()),
        _ if trivial(scrut) && !matches!(scrut, Value::Var(_)) => Some(scrut.clone()),
        Value::Var(x) => match env.get(x) {
            Some(v) if !matches!(v, Value::Var(_)) => Some(v.clone()),
            _ => None,
        },
        _ => None,
    }
}

// Fold a `Prim` over integer literals, mirroring the evaluator's i64 fast path
// (`dispatch_int_op`). Comparisons fold always; arithmetic folds only when the
// result is representable as a `Value::Int`, i.e. it neither overflows i64 nor
// leaves the tagged-immediate range the elaborator uses (`small_int`) -- a result
// outside that range is a heap bignum the Core has no literal for, so its `Prim`
// is left for the runtime to build. A `Div`/`Rem` by zero never folds (the
// runtime error must still raise). Float and machine-int (`I64`/`U64`) operands
// are left alone, so the fold is parity-exact.
fn const_fold(op: CoreOp, a: &Value, b: &Value) -> Option<Value> {
    let (Value::Int(x), Value::Int(y)) = (a, b) else {
        return None;
    };
    let (x, y) = (*x, *y);
    // The immediate (untagged 63-bit) range a `Value::Int` may hold, matching
    // `small_int` in elaboration.
    let imm = |r: i64| ((-(1i64 << 62))..(1i64 << 62)).contains(&r).then_some(Value::Int(r));
    match op {
        CoreOp::Eq => Some(Value::Bool(x == y)),
        CoreOp::Ne => Some(Value::Bool(x != y)),
        CoreOp::Lt => Some(Value::Bool(x < y)),
        CoreOp::Le => Some(Value::Bool(x <= y)),
        CoreOp::Gt => Some(Value::Bool(x > y)),
        CoreOp::Ge => Some(Value::Bool(x >= y)),
        CoreOp::Add => x.checked_add(y).and_then(imm),
        CoreOp::Sub => x.checked_sub(y).and_then(imm),
        CoreOp::Mul => x.checked_mul(y).and_then(imm),
        CoreOp::Div if y != 0 => x.checked_div(y).and_then(imm),
        CoreOp::Rem if y != 0 => imm(x.wrapping_rem(y)),
        _ => None,
    }
}

// The selected arm: bind each matched field, then the original body.
fn build_arm(binds: Vec<(Sym, Value)>, body: &Comp) -> Comp {
    let mut out = body.clone();
    for (s, v) in binds.into_iter().rev() {
        out = Comp::Bind(Box::new(Comp::Return(v)), s, Box::new(out));
    }
    out
}

impl Rewrite for Simplifier {
    type Ctx = Env;

    fn value(&mut self, v: &Value, env: &Env) -> Value {
        if let Value::Var(x) = v {
            if let Some(t) = env.get(x) {
                if trivial(t) {
                    self.ticks += 1;
                    return t.clone();
                }
            }
        }
        self.descend_value(v, env)
    }

    fn comp(&mut self, c: &Comp, env: &Env) -> Comp {
        match c {
            Comp::Bind(rhs, x, body) => {
                let rhs2 = self.comp(rhs, env);
                let mut benv = narrow(env, &[*x]);
                if let Comp::Return(v) = &rhs2 {
                    if known(v) {
                        benv.insert(*x, v.clone());
                    }
                }
                let body2 = self.comp(body, &benv);
                if matches!(rhs2, Comp::Return(_)) && !fv::comp(&body2).contains(x) {
                    self.ticks += 1; // dead-let
                    body2
                } else {
                    Comp::Bind(Box::new(rhs2), *x, Box::new(body2))
                }
            }
            Comp::Case(scrut, arms) => {
                if let Some(kv) = resolve(scrut, env) {
                    for (pat, body) in arms {
                        if let Some(binds) = pat_match(pat, &kv) {
                            self.ticks += 1; // case-of-known-constructor
                            return build_arm(binds, body);
                        }
                    }
                }
                let scrut2 = self.value(scrut, env);
                let arms2 = arms
                    .iter()
                    .map(|(p, b)| {
                        let e = narrow(env, &pat_binders(p));
                        (p.clone(), self.comp(b, &e))
                    })
                    .collect();
                Comp::Case(scrut2, arms2)
            }
            Comp::Lam(ps, b) => {
                let e = narrow(env, ps);
                Comp::Lam(ps.clone(), Box::new(self.comp(b, &e)))
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                let body2 = Box::new(self.comp(body, env));
                let return_body2 = return_body.as_ref().map(|b| {
                    let e = narrow(env, &return_var.iter().copied().collect::<Vec<_>>());
                    Box::new(self.comp(b, &e))
                });
                let ops2 = ops
                    .iter()
                    .map(|o| {
                        let mut bs = o.params.clone();
                        bs.push(o.resume);
                        let e = narrow(env, &bs);
                        HandleOp {
                            name: o.name,
                            params: o.params.clone(),
                            resume: o.resume,
                            body: self.comp(&o.body, &e),
                        }
                    })
                    .collect();
                Comp::Handle {
                    body: body2,
                    return_var: *return_var,
                    return_body: return_body2,
                    ops: ops2,
                }
            }
            Comp::WithReuse { token, freed, body } => {
                let freed2 = self.value(freed, env);
                let e = narrow(env, &[*token]);
                Comp::WithReuse {
                    token: *token,
                    freed: freed2,
                    body: Box::new(self.comp(body, &e)),
                }
            }
            Comp::Prim(op, a, b) => {
                let a2 = self.value(a, env);
                let b2 = self.value(b, env);
                if let Some(folded) = const_fold(*op, &a2, &b2) {
                    self.ticks += 1;
                    Comp::Return(folded)
                } else {
                    Comp::Prim(*op, a2, b2)
                }
            }
            _ => self.descend_comp(c, env),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::simplify_counted;
    use crate::core::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, Value};
    use crate::sym::Sym;

    fn s(n: &str) -> Sym {
        Sym::new(n)
    }
    fn one(params: Vec<Sym>, body: Comp) -> Core {
        Core {
            fns: vec![CoreFn {
                name: s("f"),
                params,
                body,
            }],
        }
    }

    // A constructor built then matched collapses end to end: the field flows
    // through case-of-known-constructor, copy-propagation, and dead-let to leave
    // just the field. `fn f(v) = let s = Some(v) in match s { Some(a) => a }`.
    #[test]
    fn known_constructor_match_collapses_to_the_field() {
        let v = s("v");
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Ctor(s("Some"), 0, vec![Value::Var(v)]))),
            s("sc"),
            Box::new(Comp::Case(
                Value::Var(s("sc")),
                vec![
                    (
                        CorePat::Ctor(s("Some"), vec![Some(s("a"))]),
                        Comp::Return(Value::Var(s("a"))),
                    ),
                    (CorePat::Ctor(s("None"), vec![]), Comp::Return(Value::Unit)),
                ],
            )),
        );
        let (out, ticks) = simplify_counted(&one(vec![v], body));
        assert!(ticks > 0);
        match &out.fns[0].body {
            Comp::Return(Value::Var(x)) => assert_eq!(*x, v),
            other => panic!("expected `return v`, got {other:?}"),
        }
    }

    // Integer `Prim` over literals folds to its result, but a div-by-zero and an
    // overflowing add are left intact (the error must still raise; the overflow
    // result is a bignum the Core cannot spell).
    #[test]
    fn const_folds_only_the_parity_safe_integer_cases() {
        let fold = |op, x, y| {
            let (out, _) = simplify_counted(&one(
                vec![],
                Comp::Prim(op, Value::Int(x), Value::Int(y)),
            ));
            out.fns.into_iter().next().unwrap().body
        };
        match fold(CoreOp::Add, 2, 3) {
            Comp::Return(Value::Int(5)) => {}
            other => panic!("expected `return 5`, got {other:?}"),
        }
        assert!(matches!(fold(CoreOp::Lt, 2, 3), Comp::Return(Value::Bool(true))));
        // div by zero: unfolded (preserves the runtime error)
        assert!(matches!(fold(CoreOp::Div, 1, 0), Comp::Prim(CoreOp::Div, ..)));
        // i64 overflow: unfolded (result would be a bignum)
        assert!(matches!(fold(CoreOp::Add, i64::MAX, 1), Comp::Prim(CoreOp::Add, ..)));
        // fits i64 but leaves the tagged-immediate range: unfolded, since a
        // `Value::Int` cannot represent it (this was a real parity bug).
        let big = (1i64 << 62) - 1;
        assert!(matches!(fold(CoreOp::Add, big, big), Comp::Prim(CoreOp::Add, ..)));
    }

    // A let of a variable is copy-propagated into its uses and then dropped.
    // `fn f(y) = let x = y in x + x` becomes `y + y`.
    #[test]
    fn trivial_let_is_copy_propagated_and_dropped() {
        let y = s("y");
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Var(y))),
            s("x"),
            Box::new(Comp::Prim(CoreOp::Add, Value::Var(s("x")), Value::Var(s("x")))),
        );
        let (out, ticks) = simplify_counted(&one(vec![y], body));
        assert!(ticks > 0);
        match &out.fns[0].body {
            Comp::Prim(CoreOp::Add, Value::Var(a), Value::Var(b)) => {
                assert_eq!(*a, y);
                assert_eq!(*b, y);
            }
            other => panic!("expected `y + y`, got {other:?}"),
        }
    }
}
