//! Witness-preserving fold-clause stripping.

use super::super::as_var;
use super::thread::{a_kind, resume_arg};
use super::{
    free_comp_vars, free_value_vars, BTreeMap, BTreeSet, CompSig, EffRow, FoldAKind, Sym,
    TypedComp, TypedCompKind, TypedValue,
};

/// Rewrite a fold clause's tail `k(A)(B)` to `return B`, dropping the resume
/// binder, and report what the resume value was: unit for a write, the
/// accumulator for a read.
///
/// The neutral clause-shape predicates answer a question, and erasure preserves
/// everything they read; this returns a rewritten clause body, and an erased
/// rewrite has dropped exactly the witnesses the typed tree carries. The kind
/// computed here is therefore cross-checked against [`is_fold`] by the caller.
///
/// `None` when the clause is not state-tail-resumptive, when the resume value is
/// outside the admitted set, or when branches disagree on the kind.
pub(super) fn strip_state(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    acc: Sym,
) -> Option<(TypedComp, FoldAKind)> {
    strip_state_go(c, aliases, acc, &BTreeMap::new())
}

/// `subst` accumulates the pure `return v to x` aliases seen so far, so a resume
/// argument that is itself an A-normal-form binder (`return s to t; k(t)(..)`)
/// resolves back to the accumulator before its kind is classified.
fn strip_state_go(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    acc: Sym,
    subst: &BTreeMap<Sym, TypedValue>,
) -> Option<(TypedComp, FoldAKind)> {
    match c.kind() {
        TypedCompKind::Bind(m, x, n) => {
            // Drop a rebinding of the resume (`return k to k'`).
            if let TypedCompKind::Return(v) = m.kind() {
                if as_var(v).is_some_and(|v| aliases.contains(&v)) {
                    let mut a2 = aliases.clone();
                    a2.insert(x.name());
                    return strip_state_go(n, &a2, acc, subst);
                }
            }
            // The double application: `m` computes the resumption `k(A)` and binds
            // it to `x`, and the tail `n` applies that to the new accumulator `B`.
            if let Some(a) = resume_arg(m, aliases, subst) {
                let kind = a_kind(&a, acc)?;
                let TypedCompKind::App { callee, args, .. } = n.kind() else {
                    return None;
                };
                if !matches!(callee.kind(), TypedCompKind::Force(k)
                    if as_var(k) == Some(x.name()))
                {
                    return None;
                }
                let [ns] = args.as_slice() else {
                    return None;
                };
                if !free_value_vars(ns).is_disjoint(aliases) {
                    return None;
                }
                return Some((
                    TypedComp::new(
                        CompSig::new(ns.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(ns.clone()),
                    ),
                    kind,
                ));
            }
            // A pure leading bind (the `f(acc, x)` block): keep it, record any
            // value alias for resolving the resume argument, and thread on.
            if !free_comp_vars(m).is_disjoint(aliases) {
                return None;
            }
            let mut subst2 = subst.clone();
            if let TypedCompKind::Return(v) = m.kind() {
                subst2.insert(x.name(), v.clone());
            }
            let (tail, kind) = strip_state_go(n, aliases, acc, &subst2)?;
            Some((
                TypedComp::new(
                    tail.sig().clone(),
                    TypedCompKind::Bind(m.clone(), x.clone(), Box::new(tail)),
                ),
                kind,
            ))
        }
        TypedCompKind::If(v, t, e) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let (tt, kt) = strip_state_go(t, aliases, acc, subst)?;
            let (te, ke) = strip_state_go(e, aliases, acc, subst)?;
            if kt != ke {
                return None;
            }
            Some((
                TypedComp::new(
                    tt.sig().clone(),
                    TypedCompKind::If(v.clone(), Box::new(tt), Box::new(te)),
                ),
                kt,
            ))
        }
        TypedCompKind::Case(v, arms) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let mut kind: Option<FoldAKind> = None;
            let mut out = Vec::with_capacity(arms.len());
            for (p, b) in arms {
                let (tb, kb) = strip_state_go(b, aliases, acc, subst)?;
                match kind {
                    Some(k) if k != kb => return None,
                    _ => kind = Some(kb),
                }
                out.push((p.clone(), tb));
            }
            let sig = out.first().map(|(_, b)| b.sig().clone())?;
            Some((
                TypedComp::new(sig, TypedCompKind::Case(v.clone(), out)),
                kind?,
            ))
        }
        _ => None,
    }
}
