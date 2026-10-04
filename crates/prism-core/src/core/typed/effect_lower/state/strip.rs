//! Witness-preserving fold-clause stripping.

use super::super::as_var;
use super::thread::{a_kind, resume_arg};
use super::{
    free_comp_vars, free_value_vars, pair_value, BTreeMap, BTreeSet, CompSig, EffRow, FoldAKind,
    Sym, TypedComp, TypedCompKind, TypedValue,
};

/// Rewrite a fold clause's tail `k(A)(B)` to `return B`, dropping the resume
/// binder, and report what the resume value was: unit for a write, the
/// accumulator for a read, and anything else a value of the clause's own, whose
/// tail becomes `return #(B, A)` so the two travel together.
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
    paired: bool,
) -> Option<(TypedComp, FoldAKind)> {
    strip_state_go(c, aliases, acc, &BTreeMap::new(), paired)
}

/// `subst` accumulates the pure `return v to x` aliases seen so far, so a resume
/// argument that is itself an A-normal-form binder (`return s to t; k(t)(..)`)
/// resolves back to the accumulator before its kind is classified.
fn strip_state_go(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    acc: Sym,
    subst: &BTreeMap<Sym, TypedValue>,
    paired: bool,
) -> Option<(TypedComp, FoldAKind)> {
    match c.kind() {
        TypedCompKind::Bind(m, x, n) => {
            // Drop a rebinding of the resume (`return k to k'`).
            if let TypedCompKind::Return(v) = m.kind() {
                if as_var(v).is_some_and(|v| aliases.contains(&v)) {
                    let mut a2 = aliases.clone();
                    a2.insert(x.name());
                    return strip_state_go(n, &a2, acc, subst, paired);
                }
            }
            // The double application: `m` computes the resumption `k(A)` and binds
            // it to `x`, and the tail `n` applies that to the new accumulator `B`.
            if let Some(a) = resume_arg(m, aliases, subst) {
                let kind = a_kind(&a, acc, paired)?;
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
                // A resume value of the clause's own leaves with the new
                // accumulator, in the same order every paired scope carries
                // the two. The value is what the dropped resumption computed,
                // so the binds that build it are kept and only the resumption
                // itself gives way to the pair.
                let stripped = match kind {
                    FoldAKind::Value => yield_beside(m, aliases, &pair_value(ns.clone(), a)?)?,
                    FoldAKind::Unit | FoldAKind::Acc => TypedComp::new(
                        CompSig::new(ns.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(ns.clone()),
                    ),
                };
                return Some((stripped, kind));
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
            let (tail, kind) = strip_state_go(n, aliases, acc, &subst2, paired)?;
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
            let (tt, kt) = strip_state_go(t, aliases, acc, subst, paired)?;
            let (te, ke) = strip_state_go(e, aliases, acc, subst, paired)?;
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
                let (tb, kb) = strip_state_go(b, aliases, acc, subst, paired)?;
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

/// The resumption head `k(A)` rewritten to answer `pair` instead of resuming:
/// its leading binds stay, so the value it computed for `A` is still in scope
/// where the pair reads it, and the resume rebindings it holds go the way they
/// go everywhere else.
fn yield_beside(m: &TypedComp, aliases: &BTreeSet<Sym>, pair: &TypedValue) -> Option<TypedComp> {
    match m.kind() {
        TypedCompKind::App { .. } => Some(TypedComp::new(
            CompSig::new(pair.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(pair.clone()),
        )),
        TypedCompKind::Bind(h, x, n) => {
            if let TypedCompKind::Return(v) = h.kind() {
                if as_var(v).is_some_and(|v| aliases.contains(&v)) {
                    let mut a2 = aliases.clone();
                    a2.insert(x.name());
                    return yield_beside(n, &a2, pair);
                }
            }
            let tail = yield_beside(n, aliases, pair)?;
            Some(TypedComp::new(
                tail.sig().clone(),
                TypedCompKind::Bind(h.clone(), x.clone(), Box::new(tail)),
            ))
        }
        _ => None,
    }
}
