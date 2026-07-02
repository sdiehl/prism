//! ANF-shape predicates and small constructors the state-mode lowering reasons
//! over: recognizing identity returns/transformers, the `SMore`/`SDone` Step
//! values, resume-tail shapes, and the substitution helpers that see through
//! A-normal-form let-bindings.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cbpv::{Comp, CorePat, Value};
pub(super) use crate::core::effect_lower::{sdone, smore};
use crate::core::fv;
use crate::sym::Sym;

// A forwarding handler's identity return clause `return r => return r`: the
// source's final value (the threaded accumulator) passes through unchanged.
pub(super) fn is_id_return(return_var: Option<Sym>, return_body: Option<&Comp>) -> bool {
    match (return_var, return_body) {
        (Some(v), Some(Comp::Return(Value::Var(r)))) => *r == v,
        _ => false,
    }
}

// The identity state transformer `return thunk { \a. return a }`, a fold's
// return clause: the producer's unit result maps to the unchanged accumulator.
pub(super) fn is_id_transformer(rb: &Comp) -> bool {
    matches!(rb, Comp::Return(Value::Thunk(t))
        if matches!(t.as_ref(), Comp::Lam(ps, b)
            if ps.len() == 1
                && matches!(b.as_ref(), Comp::Return(Value::Var(v)) if v == &ps[0])))
}

// A one-parameter state-transformer return clause `return thunk { \s. <body> }`.
// The identity transformer is the writer special case; a get-style handler's
// `\s -> r` (yield the producer value, discard the final state) is the general
// shape, lowered by applying it to the final accumulator at the use site.
pub(super) fn is_state_transformer(rb: &Comp) -> bool {
    matches!(rb, Comp::Return(Value::Thunk(t))
        if matches!(t.as_ref(), Comp::Lam(ps, _) if ps.len() == 1))
}

// The resume value `A` a fold clause's `k(A)(B)` tail resumes the op with. Tier-1
// fusion admits only the two shapes whose `A` the producer can reconstruct with no
// allocation: `Unit` (a write/`put`, the op's result is unit) and `Acc` (a
// read/`get`, the op's result is the current accumulator). Any other pure `A`
// falls back to the `@region` driver.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in crate::core::effect_lower) enum AKind {
    Unit,
    Acc,
}

// Classify a resume value against the fold lambda's accumulator parameter.
fn a_kind(a: &Value, acc: Sym) -> Option<AKind> {
    match a {
        Value::Unit => Some(AKind::Unit),
        Value::Var(v) if *v == acc => Some(AKind::Acc),
        _ => None,
    }
}

// Whether a branch uses a resume alias (so it resumes) rather than dropping it.
pub(super) fn branch_resumes(c: &Comp, aliases: &BTreeSet<Sym>) -> bool {
    !fv::comp(c).is_disjoint(aliases)
}

// The branches of a take clause's tail `if`, skipping its leading counter-test
// binds. None when the clause is not a (binds; if) shape.
pub(super) fn tail_if(c: &Comp) -> Option<(&Comp, &Comp)> {
    match c {
        Comp::Bind(_, _, n) => tail_if(n),
        Comp::If(_, t, e) => Some((t, e)),
        _ => None,
    }
}

// Resolve `g(arg)` written in ANF (`return v to x; ..; (force f)(a)`) to its
// single argument value, following `return`-bindings so the head resolves to
// `g`. None when the rest is not a unary application of `g`.
pub(super) fn anf_app_arg(g: Sym, c: &Comp) -> Option<Value> {
    let mut subst: BTreeMap<Sym, Value> = BTreeMap::new();
    let mut cur = c;
    loop {
        match cur {
            Comp::Bind(m, x, n) => {
                let Comp::Return(v) = m.as_ref() else {
                    return None;
                };
                subst.insert(*x, v.clone());
                cur = n;
            }
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(fv)) = f.as_ref() else {
                    return None;
                };
                if anf_resolve(*fv, &subst) != g {
                    return None;
                }
                let [a] = args.as_slice() else {
                    return None;
                };
                return Some(anf_resolve_val(a, &subst));
            }
            _ => return None,
        }
    }
}

// Follow `return`-binding aliases to the underlying variable name.
pub(super) fn anf_resolve(v: Sym, subst: &BTreeMap<Sym, Value>) -> Sym {
    match subst.get(&v) {
        Some(Value::Var(w)) => anf_resolve(*w, subst),
        _ => v,
    }
}

pub(super) fn anf_resolve_val(v: &Value, subst: &BTreeMap<Sym, Value>) -> Value {
    match v {
        Value::Var(w) => subst
            .get(w)
            .map_or_else(|| v.clone(), |inner| anf_resolve_val(inner, subst)),
        _ => v.clone(),
    }
}

// A rebinding of the resume, `return k to x` for an alias `k`.
pub(super) fn is_alias_return(m: &Comp, aliases: &BTreeSet<Sym>) -> bool {
    matches!(m, Comp::Return(Value::Var(v)) if aliases.contains(v))
}

// `Name(var)` constructor pattern binding one field.
pub(super) fn ctor_pat1(name: &str, var: Sym) -> CorePat {
    CorePat::Ctor(Sym::from(name), vec![Some(var)])
}

// Rewrite a fold clause's tail `k(A)(B)` to `return B`, dropping the resume
// binder, and report the resume value's [`AKind`] (`Unit` for a write `k(())(B)`,
// `Acc` for a read `k(s)(B)` where `s` is the accumulator). Mirrors
// [`strip_resume`] but for the parameter-passing double application: `k(A)` is its
// own ANF sub-block whose result is then applied to the new accumulator `B`.
// Returns None when the clause is not state-tail-resumptive or `A` is outside the
// admitted set, and None when the clause's branches disagree on the read kind.
pub(super) fn strip_state(c: &Comp, aliases: &BTreeSet<Sym>, acc: Sym) -> Option<(Comp, AKind)> {
    strip_state_go(c, aliases, acc, &BTreeMap::new())
}

// `subst` accumulates the pure `return v to x` aliases seen so far, so the resume
// argument (an ANF binder like `t` for `return s to t; k(t)(..)`) resolves back to
// the accumulator before its [`AKind`] is classified.
fn strip_state_go(
    c: &Comp,
    aliases: &BTreeSet<Sym>,
    acc: Sym,
    subst: &BTreeMap<Sym, Value>,
) -> Option<(Comp, AKind)> {
    match c {
        Comp::Bind(m, x, n) => {
            // Drop a rebinding of the resume (`return k to k'`).
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    let mut a2 = aliases.clone();
                    a2.insert(*x);
                    return strip_state_go(n, &a2, acc, subst);
                }
            }
            // The double application: `m` computes the resumption `k(A)` and
            // binds it to `x`; the tail `n` applies it to `B`.
            if let Some(a) = resume_arg(m, aliases, subst) {
                let kind = a_kind(&a, acc)?;
                let Comp::App(g, gargs) = n.as_ref() else {
                    return None;
                };
                if !matches!(g.as_ref(), Comp::Force(Value::Var(kc)) if kc == x) {
                    return None;
                }
                let [ns] = gargs.as_slice() else {
                    return None;
                };
                if !fv::value(ns).is_disjoint(aliases) {
                    return None;
                }
                return Some((Comp::Return(ns.clone()), kind));
            }
            // A pure leading bind (the `f(acc, x)` block): keep, record any value
            // alias for resume-argument resolution, and thread on.
            if !fv::comp(m).is_disjoint(aliases) {
                return None;
            }
            let mut subst2 = subst.clone();
            if let Comp::Return(v) = m.as_ref() {
                subst2.insert(*x, v.clone());
            }
            let (tail, kind) = strip_state_go(n, aliases, acc, &subst2)?;
            Some((Comp::Bind(m.clone(), *x, Box::new(tail)), kind))
        }
        Comp::If(v, t, e) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            let (tt, kt) = strip_state_go(t, aliases, acc, subst)?;
            let (te, ke) = strip_state_go(e, aliases, acc, subst)?;
            if kt != ke {
                return None;
            }
            Some((Comp::If(v.clone(), Box::new(tt), Box::new(te)), kt))
        }
        Comp::Case(v, arms) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            let mut kind: Option<AKind> = None;
            let mut out = Vec::with_capacity(arms.len());
            for (p, b) in arms {
                let (tb, kb) = strip_state_go(b, aliases, acc, subst)?;
                match kind {
                    Some(k) if k != kb => return None,
                    _ => kind = Some(kb),
                }
                out.push((p.clone(), tb));
            }
            Some((Comp::Case(v.clone(), out), kind?))
        }
        _ => None,
    }
}

// The argument `rv` of `resume(rv)` when a computation evaluates to a unary
// application of an alias, allowing leading pure binds and resume rebindings. The
// argument must be disjoint from the aliases (it is not the resume itself). `subst`
// (the caller's value aliases, extended with the sub-block's own pure binds)
// resolves the returned value, since the resume argument is itself an ANF binder
// defined inside this sub-block (`return s to t; k(t)`).
pub(super) fn resume_arg(
    c: &Comp,
    aliases: &BTreeSet<Sym>,
    subst: &BTreeMap<Sym, Value>,
) -> Option<Value> {
    match c {
        Comp::App(f, args) => {
            if !matches!(f.as_ref(), Comp::Force(Value::Var(k)) if aliases.contains(k)) {
                return None;
            }
            let [rv] = args.as_slice() else {
                return None;
            };
            fv::value(rv)
                .is_disjoint(aliases)
                .then(|| anf_resolve_val(rv, subst))
        }
        Comp::Bind(m, x, n) => {
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    let mut a2 = aliases.clone();
                    a2.insert(*x);
                    return resume_arg(n, &a2, subst);
                }
            }
            if !fv::comp(m).is_disjoint(aliases) {
                return None;
            }
            let mut s2 = subst.clone();
            if let Comp::Return(v) = m.as_ref() {
                s2.insert(*x, v.clone());
            }
            resume_arg(n, aliases, &s2)
        }
        _ => None,
    }
}

// Whether a computation evaluates to `resume(rv)` for a single argument `rv`
// disjoint from the aliases (the argument is discarded, so its binders may be).
pub(super) fn resume_call(c: &Comp, aliases: &BTreeSet<Sym>) -> bool {
    resume_arg(c, aliases, &BTreeMap::new()).is_some()
}
