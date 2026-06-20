//! ANF-shape predicates and small constructors the state-mode lowering reasons
//! over: recognizing identity returns/transformers, the `SMore`/`SDone` Step
//! values, resume-tail shapes, and the substitution helpers that see through
//! A-normal-form let-bindings.

use std::collections::BTreeSet;

use crate::core::cbpv::{Comp, CorePat, Value};
use crate::core::effect_lower::{SDONE, SMORE};
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

pub(super) fn smore(v: Value) -> Value {
    Value::Ctor(SMORE.into(), 0, vec![v])
}

pub(super) fn sdone(v: Value) -> Value {
    Value::Ctor(SDONE.into(), 1, vec![v])
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
    let mut subst: std::collections::BTreeMap<Sym, Value> = std::collections::BTreeMap::new();
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
pub(super) fn anf_resolve(v: Sym, subst: &std::collections::BTreeMap<Sym, Value>) -> Sym {
    match subst.get(&v) {
        Some(Value::Var(w)) => anf_resolve(*w, subst),
        _ => v,
    }
}

pub(super) fn anf_resolve_val(v: &Value, subst: &std::collections::BTreeMap<Sym, Value>) -> Value {
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

// Rewrite a fold clause's tail `k(())(ns)` to `return ns`, dropping the resume
// binder. Mirrors [`strip_resume`] but for the parameter-passing double
// application: `k(())` is its own ANF sub-block whose result is then applied to
// the new accumulator `ns`. Returns None when the clause is not
// state-tail-resumptive.
pub(super) fn strip_state(c: &Comp, aliases: &std::collections::BTreeSet<Sym>) -> Option<Comp> {
    match c {
        Comp::Bind(m, x, n) => {
            // Drop a rebinding of the resume (`return k to k'`).
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    let mut a2 = aliases.clone();
                    a2.insert(*x);
                    return strip_state(n, &a2);
                }
            }
            // The double application: `m` computes the resumption `k(())` and
            // binds it to `x`; the tail `n` applies it to `ns`.
            if resume_call(m, aliases) {
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
                return Some(Comp::Return(ns.clone()));
            }
            // A pure leading bind (the `f(acc, x)` block): keep and thread on.
            if !fv::comp(m).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(strip_state(n, aliases)?),
            ))
        }
        Comp::If(v, t, e) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::If(
                v.clone(),
                Box::new(strip_state(t, aliases)?),
                Box::new(strip_state(e, aliases)?),
            ))
        }
        Comp::Case(v, arms) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), strip_state(b, aliases)?)))
                    .collect::<Option<_>>()?,
            ))
        }
        _ => None,
    }
}

// Whether a computation evaluates to `resume(rv)` for a single argument `rv`
// disjoint from the aliases: a unary application of an alias, allowing leading
// pure binds and resume rebindings (the argument is discarded, so its binders
// may be too).
pub(super) fn resume_call(c: &Comp, aliases: &std::collections::BTreeSet<Sym>) -> bool {
    match c {
        Comp::App(f, args) => {
            matches!(f.as_ref(), Comp::Force(Value::Var(k)) if aliases.contains(k))
                && matches!(args.as_slice(), [rv] if fv::value(rv).is_disjoint(aliases))
        }
        Comp::Bind(m, x, n) => {
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    let mut a2 = aliases.clone();
                    a2.insert(*x);
                    return resume_call(n, &a2);
                }
            }
            fv::comp(m).is_disjoint(aliases) && resume_call(n, aliases)
        }
        _ => false,
    }
}
