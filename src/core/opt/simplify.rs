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
//! - Constant folding: a `Prim` over integer or float literals reduces to its
//!   result. It mirrors the evaluator's i64 fast path and `dispatch_float_op`
//!   exactly (folding only the integer cases that stay in i64), so it is
//!   parity-safe (see `const_fold`).
//! - Used-once-thunk inlining: a thunk bound and then immediately forced once
//!   collapses to its computation, dropping the allocation (sound because thunks
//!   are not memoized).
//! - Case-of-case (terminating form only): `let x = E in K` where `E` is a
//!   case/if of known returns and `K` immediately scrutinizes `x` floats into
//!   `E`'s arms, where each known value collapses the inner scrutinee on the
//!   spot. Guarded by a size bound on `K`, so it strictly removes a join and
//!   never grows unboundedly (see `case_of_case`).
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

// Fold a `Prim` over float literals, mirroring the evaluator's `dispatch_float_op`
// exactly. IEEE-754 round-to-nearest is deterministic, so a compile-time `f64` op
// matches the backend's at the bit level for finite results; for NaN/inf the
// observable value and every comparison agree regardless of payload. `Divf` by
// zero yields inf (not a trap), so unlike integer `Div` it folds.
#[allow(clippy::float_cmp)]
fn const_fold_float(op: CoreOp, x: f64, y: f64) -> Option<Value> {
    Some(match op {
        CoreOp::Addf => Value::Float(x + y),
        CoreOp::Subf => Value::Float(x - y),
        CoreOp::Mulf => Value::Float(x * y),
        CoreOp::Divf => Value::Float(x / y),
        CoreOp::Eqf => Value::Bool(x == y),
        CoreOp::Nef => Value::Bool(x != y),
        CoreOp::Ltf => Value::Bool(x < y),
        CoreOp::Lef => Value::Bool(x <= y),
        CoreOp::Gtf => Value::Bool(x > y),
        CoreOp::Gef => Value::Bool(x >= y),
        _ => return None,
    })
}

// Fold a `Prim` over integer literals, mirroring the evaluator's i64 fast path
// (`dispatch_int_op`). Comparisons fold always; arithmetic folds only when the
// result is representable as a `Value::Int`, i.e. it neither overflows i64 nor
// leaves the tagged-immediate range the elaborator uses (`small_int`) -- a result
// outside that range is a heap bignum the Core has no literal for, so its `Prim`
// is left for the runtime to build. A `Div`/`Rem` by zero never folds (the
// runtime error must still raise). Float operands fold via `const_fold_float`;
// machine-int (`I64`/`U64`) operands are left alone, so the fold is parity-exact.
fn const_fold(op: CoreOp, a: &Value, b: &Value) -> Option<Value> {
    if let (Value::Float(x), Value::Float(y)) = (a, b) {
        return const_fold_float(op, *x, *y);
    }
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

// The node budget a case-of-case continuation may have. The bound is what keeps
// duplication (each scrutinee arm gets the continuation branch it selects) finite.
const COC_SIZE_LIMIT: usize = 48;

// A bounded node count of `c`, for the case-of-case size guard.
fn comp_nodes(c: &Comp) -> usize {
    1 + match c {
        Comp::Bind(a, _, b) => comp_nodes(a) + comp_nodes(b),
        Comp::Case(_, arms) => arms.iter().map(|(_, b)| comp_nodes(b)).sum(),
        Comp::If(_, t, e) => comp_nodes(t) + comp_nodes(e),
        Comp::Lam(_, b) | Comp::Mask(_, b) => comp_nodes(b),
        Comp::App(f, _) => comp_nodes(f),
        Comp::WithReuse { body, .. } => comp_nodes(body),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            comp_nodes(body)
                + return_body.as_ref().map_or(0, |b| comp_nodes(b))
                + ops.iter().map(|o| comp_nodes(&o.body)).sum::<usize>()
        }
        _ => 0,
    }
}

// A continuation `K` that immediately scrutinizes the let-bound `x` and nothing
// else: either `case x of <arms>` or `if x then .. else ..`. Used by case-of-case
// to compute, per scrutinee arm, the branch a known value selects.
enum Cont<'a> {
    Case(&'a [(CorePat, Comp)]),
    If(&'a Comp, &'a Comp),
}

// View `body` as a continuation on `x`: it must scrutinize `x` at its head and
// use `x` nowhere else (so dropping the `let x = ...` cannot leave `x` dangling).
fn cont_on(x: Sym, body: &Comp) -> Option<Cont<'_>> {
    match body {
        Comp::Case(Value::Var(y), arms) if *y == x => {
            (!arms.iter().any(|(_, b)| fv::comp(b).contains(&x))).then_some(Cont::Case(arms))
        }
        Comp::If(Value::Var(y), t, e) if *y == x => {
            (!fv::comp(t).contains(&x) && !fv::comp(e).contains(&x)).then_some(Cont::If(t, e))
        }
        _ => None,
    }
}

impl Cont<'_> {
    // The branch this continuation takes when `x` is the known value `kv`, fully
    // collapsed (the inner scrutinee is gone). `None` if no branch is selected, in
    // which case case-of-case must not fire (collapse is not guaranteed).
    fn select(&self, kv: &Value) -> Option<Comp> {
        match self {
            Self::Case(arms) => arms
                .iter()
                .find_map(|(pat, body)| pat_match(pat, kv).map(|binds| build_arm(binds, body))),
            Self::If(t, e) => match kv {
                Value::Bool(true) => Some((*t).clone()),
                Value::Bool(false) => Some((*e).clone()),
                _ => None,
            },
        }
    }
}

// `Return(v)` with `v` a known value, the shape every arm/branch of a case-of-case
// scrutinee must have.
fn ret_known(c: &Comp) -> Option<Value> {
    match c {
        Comp::Return(v) if known(v) => Some(v.clone()),
        _ => None,
    }
}

// Case-of-case, terminating-by-construction form. Floats `let x = E in K` into
// E's arms only when the float is guaranteed to immediately collapse and strictly
// remove a join: `E` is a `Case`/`If` whose every arm/branch is `Return(known)`,
// `K` immediately scrutinizes `x` (and uses it nowhere else), and `K` is within
// the size bound. Each arm becomes the K-branch that arm's known value selects,
// computed here, so the inner scrutinee vanishes with no later pass and no growth
// beyond K's bounded size. `None` when any precondition fails.
fn case_of_case(x: Sym, rhs: &Comp, body: &Comp) -> Option<Comp> {
    if !matches!(rhs, Comp::Case(..) | Comp::If(..)) {
        return None;
    }
    let cont = cont_on(x, body)?;
    if comp_nodes(body) > COC_SIZE_LIMIT {
        return None;
    }
    match rhs {
        Comp::Case(scrut, arms) => {
            // `K` is floated under each arm's pattern binders; a binder that
            // shadows a free var of `K` would capture it, so bail in that case.
            let kfv: BTreeSet<Sym> = fv::comp(body).into_iter().filter(|v| *v != x).collect();
            let mut out = Vec::with_capacity(arms.len());
            for (pat, abody) in arms {
                if pat_binders(pat).iter().any(|b| kfv.contains(b)) {
                    return None;
                }
                out.push((pat.clone(), cont.select(&ret_known(abody)?)?));
            }
            Some(Comp::Case(scrut.clone(), out))
        }
        Comp::If(scrut, t, e) => {
            let tb = cont.select(&ret_known(t)?)?;
            let eb = cont.select(&ret_known(e)?)?;
            Some(Comp::If(scrut.clone(), Box::new(tb), Box::new(eb)))
        }
        _ => None,
    }
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
                // Case-of-case (terminating-by-construction): when `rhs` is a
                // case/if of known returns and `body` immediately scrutinizes `x`,
                // float into the arms, collapsing the inner scrutinee on the spot.
                if let Some(coc) = case_of_case(*x, &rhs2, &body2) {
                    self.ticks += 1;
                    return coc;
                }
                // Used-once-thunk inlining (canonical immediate-force shape): a
                // thunk bound and then immediately forced once collapses to its
                // computation, dropping the allocation. Sound because Prism thunks
                // are not memoized (forcing re-runs the computation), so the inline
                // runs it exactly as often; `x` not free in `rest` confirms the
                // force was the only use.
                if let Comp::Return(Value::Thunk(c)) = &rhs2 {
                    if let Comp::Bind(forced, y, rest) = &body2 {
                        if matches!(forced.as_ref(), Comp::Force(Value::Var(f)) if f == x)
                            && !fv::comp(rest).contains(x)
                        {
                            self.ticks += 1;
                            return Comp::Bind(c.clone(), *y, rest.clone());
                        }
                    }
                }
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

    // Float `Prim`s fold like the evaluator: arithmetic to a `Float`, comparison
    // to a `Bool`, and (unlike integer `Div`) `Divf` by zero folds to inf.
    #[test]
    fn const_folds_float_arithmetic_and_comparison() {
        let fold = |op, x, y| {
            let (out, _) = simplify_counted(&one(
                vec![],
                Comp::Prim(op, Value::Float(x), Value::Float(y)),
            ));
            out.fns.into_iter().next().unwrap().body
        };
        match fold(CoreOp::Addf, 2.5, 0.5) {
            Comp::Return(Value::Float(f)) => assert!((f - 3.0).abs() < f64::EPSILON),
            other => panic!("expected `return 3.0`, got {other:?}"),
        }
        assert!(matches!(fold(CoreOp::Ltf, 1.0, 2.0), Comp::Return(Value::Bool(true))));
        assert!(matches!(fold(CoreOp::Eqf, 1.0, 2.0), Comp::Return(Value::Bool(false))));
        // Divf by zero is inf, not a trap, so it folds (a finite over +0.0).
        match fold(CoreOp::Divf, 1.0, 0.0) {
            Comp::Return(Value::Float(f)) => assert!(f.is_infinite() && f > 0.0),
            other => panic!("expected `return inf`, got {other:?}"),
        }
    }

    // A thunk bound and immediately forced once collapses to its computation,
    // dropping the allocation. `fn f(n) = let t = thunk(return n) in let y =
    // force t in return y` becomes `let y = (return n) in return y`.
    #[test]
    fn used_once_thunk_inlines_at_its_force() {
        let n = s("n");
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Thunk(Box::new(Comp::Return(Value::Var(n)))))),
            s("t"),
            Box::new(Comp::Bind(
                Box::new(Comp::Force(Value::Var(s("t")))),
                s("y"),
                Box::new(Comp::Return(Value::Var(s("y")))),
            )),
        );
        let (out, ticks) = simplify_counted(&one(vec![n], body));
        assert!(ticks > 0);
        // The thunk binder `t` is gone; no `Force` remains.
        let printed = format!("{:?}", out.fns[0].body);
        assert!(!printed.contains("Force"), "force not inlined: {printed}");
        assert!(!printed.contains("Thunk"), "thunk not dropped: {printed}");
    }

    // Case-of-case collapses end to end: `let x = (case s of A => Some(1), B =>
    // None) in (case x of Some(n) => n, None => 0)` becomes `case s of A => 1, B
    // => 0` -- the inner scrutinee on `x` is gone in every arm.
    #[test]
    fn case_of_case_floats_and_collapses_the_inner_scrutinee() {
        let some = |v| Value::Ctor(s("Some"), 0, vec![v]);
        let none = Value::Ctor(s("None"), 1, vec![]);
        let inner = Comp::Case(
            Value::Var(s("x")),
            vec![
                (
                    CorePat::Ctor(s("Some"), vec![Some(s("n"))]),
                    Comp::Return(Value::Var(s("n"))),
                ),
                (CorePat::Ctor(s("None"), vec![]), Comp::Return(Value::Int(0))),
            ],
        );
        let outer = Comp::Bind(
            Box::new(Comp::Case(
                Value::Var(s("sv")),
                vec![
                    (CorePat::Ctor(s("A"), vec![]), Comp::Return(some(Value::Int(1)))),
                    (CorePat::Ctor(s("B"), vec![]), Comp::Return(none)),
                ],
            )),
            s("x"),
            Box::new(inner),
        );
        let (out, ticks) = simplify_counted(&one(vec![s("sv")], outer));
        assert!(ticks > 0);
        // No `Some`/`None` scrutinee remains: the result is `case sv of A => 1, B
        // => 0`, with both arms a bare integer return.
        match &out.fns[0].body {
            Comp::Case(Value::Var(v), arms) if *v == s("sv") => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(&arms[0].1, Comp::Return(Value::Int(1))));
                assert!(matches!(&arms[1].1, Comp::Return(Value::Int(0))));
            }
            other => panic!("expected collapsed `case sv`, got {other:?}"),
        }
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
