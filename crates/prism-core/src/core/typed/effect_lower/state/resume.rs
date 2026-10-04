//! Erasing a tail-resumptive clause's continuation.
//!
//! A clause that calls its resumption exactly once, in tail position, owes the
//! continuation nothing after the call returns, so the resumption need never
//! exist as a value: the clause is just a function from the operation's
//! arguments to the handler's answer. The rewrite here is what turns one shape
//! into the other, and its refusal is what tells a caller the clause genuinely
//! needs a reified continuation.

use std::collections::BTreeSet;

use prism_common::sym::Sym;

use crate::types::ty::EffRow;

use super::super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::super::{CompSig, TypedComp, TypedCompKind};
use super::super::diagnostics::DriftLog;
use super::super::{as_var, union_effects};

/// Rewrite a tail-resumptive clause body into a plain function body: drop the
/// `resume` binder (and any rebindings of it), and turn its single tail call
/// `resume(v)` into `return v`.
///
/// `None` when the clause is not tail-resumptive (resume captured, used off the
/// tail, or some path never resumes), which is exactly the test for whether the
/// continuation can be erased at all.
///
/// Post-condition guard: a successful strip erases the continuation, so no
/// resume alias may survive in the result. This enforces at the IR level the
/// structural assumption the matcher makes about elaborator output. An
/// upstream change that emitted a clause shape this matcher misreads (accepting
/// it yet leaving a live resume reference) must NOT be accepted: debug builds
/// panic so the drift is loud during development, and release builds reject the
/// match, so the caller falls back to the general lowering rather than
/// miscompiling.
pub(super) fn strip_resume(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    drift: &DriftLog,
) -> Option<TypedComp> {
    let stripped = strip_resume_go(c, aliases, drift)?;
    if !free_comp_vars(&stripped).is_disjoint(aliases) {
        debug_assert!(
            false,
            "strip_resume accepted a clause but left a resume reference: \
             the elaborated shape drifted"
        );
        drift.shape_drift(STRIP_RESUME);
        return None;
    }
    Some(stripped)
}

// The matcher this guard names in a drift report.
const STRIP_RESUME: &str = "strip_resume";

fn strip_resume_go(c: &TypedComp, aliases: &BTreeSet<Sym>, drift: &DriftLog) -> Option<TypedComp> {
    match c.kind() {
        // The tail `resume(v)`: the continuation is the clause's own return.
        TypedCompKind::App { callee, args, .. } if forces_alias(callee, aliases) => {
            let [arg] = args.as_slice() else {
                return None;
            };
            if !free_value_vars(arg).is_disjoint(aliases) {
                return None;
            }
            Some(TypedComp::new(
                CompSig::new(arg.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(arg.clone()),
            ))
        }
        TypedCompKind::Bind(m, x, n) => {
            // `let x = resume` aliases the resumption; track it and keep going.
            if let TypedCompKind::Return(v) = m.kind() {
                if as_var(v).is_some_and(|name| aliases.contains(&name)) {
                    let mut extended = aliases.clone();
                    extended.insert(x.name());
                    return strip_resume(n, &extended, drift);
                }
            }
            // Resume may not be consumed off the tail.
            if !free_comp_vars(m).is_disjoint(aliases) {
                return None;
            }
            let rest = strip_resume(n, aliases, drift)?;
            Some(TypedComp::new(
                CompSig::new(
                    rest.sig().result().clone(),
                    union_effects(m.sig().effects(), rest.sig().effects()),
                ),
                TypedCompKind::Bind(m.clone(), x.clone(), Box::new(rest)),
            ))
        }
        TypedCompKind::If(v, t, e) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let t2 = strip_resume(t, aliases, drift)?;
            let e2 = strip_resume(e, aliases, drift)?;
            Some(TypedComp::new(
                CompSig::new(
                    t2.sig().result().clone(),
                    union_effects(t2.sig().effects(), e2.sig().effects()),
                ),
                TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
            ))
        }
        TypedCompKind::Case(v, arms) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let mut out = Vec::with_capacity(arms.len());
            for (p, b) in arms {
                out.push((p.clone(), strip_resume(b, aliases, drift)?));
            }
            let result = out.first()?.1.sig().result().clone();
            let effects = out.iter().fold(EffRow::Empty, |acc, (_, b)| {
                union_effects(&acc, b.sig().effects())
            });
            Some(TypedComp::new(
                CompSig::new(result, effects),
                TypedCompKind::Case(v.clone(), out),
            ))
        }
        _ => None,
    }
}

// `force(k)` where `k` is one of the resumption's aliases.
fn forces_alias(callee: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    matches!(callee.kind(), TypedCompKind::Force(v)
        if as_var(v).is_some_and(|name| aliases.contains(&name)))
}

#[cfg(test)]
mod tests {
    use crate::types::Type;

    use super::super::super::super::{
        CoreFnSig, CoreType, TypedBinder, TypedValue, TypedValueKind,
    };
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    /// The alias set a clause's resumption is known by: its own binder, plus any
    /// name a trivial `let` rebinds it to.
    fn resume_set(resume: Sym) -> BTreeSet<Sym> {
        let mut s = BTreeSet::new();
        s.insert(resume);
        s
    }

    fn thunk_of(body: TypedComp) -> TypedValue {
        TypedValue::new(
            CoreType::Thunk(Box::new(body.sig().clone())),
            TypedValueKind::Thunk(Box::new(body)),
        )
    }

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    // The resumption's type in a tail-resumptive clause: `thunk ((Int) -> Int)`.
    fn resume_ty() -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![int()],
                CompSig::new(int(), EffRow::Empty),
            ))),
            EffRow::Empty,
        )))
    }

    // `resume(v)` at the clause's tail.
    fn resume_call(arg: TypedValue) -> TypedComp {
        let k = var("k", resume_ty());
        let CoreType::Thunk(sig) = resume_ty() else {
            unreachable!()
        };
        let force = TypedComp::new(*sig, TypedCompKind::Force(k));
        TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![arg],
            },
        )
    }

    // A tail-resumptive clause is exactly the shape this erasure needs: the
    // continuation vanishes and the clause becomes a plain function body.
    #[test]
    fn a_tail_resume_strips_to_a_plain_return() {
        let drift = DriftLog::new(true);
        let body = resume_call(TypedValue::new(int(), TypedValueKind::Int(7)));
        let stripped = strip_resume(&body, &resume_set(sym("k")), &drift).expect("tail-resumptive");
        let TypedCompKind::Return(v) = stripped.kind() else {
            panic!("resume(v) becomes return v: {stripped:?}");
        };
        assert!(matches!(v.kind(), TypedValueKind::Int(7)));
    }

    // A resumption that escapes into a value is not tail-resumptive: the
    // continuation genuinely survives, so the erasure must decline rather than
    // silently drop it.
    #[test]
    fn a_captured_resume_refuses_to_strip() {
        let drift = DriftLog::new(true);
        // `return thunk { resume(1) }`: the continuation escapes into a thunk.
        let inner = resume_call(TypedValue::new(int(), TypedValueKind::Int(1)));
        let escaped = thunk_of(inner);
        let body = TypedComp::new(
            CompSig::new(escaped.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(escaped),
        );
        assert!(
            strip_resume(&body, &resume_set(sym("k")), &drift).is_none(),
            "a captured resume is not tail-resumptive"
        );
    }

    // A resume consumed off the tail (its value bound and used) is likewise
    // not tail-resumptive.
    #[test]
    fn a_non_tail_resume_refuses_to_strip() {
        let drift = DriftLog::new(true);
        let call = resume_call(TypedValue::new(int(), TypedValueKind::Int(1)));
        let body = TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(call),
                TypedBinder::new(sym("r"), int()),
                Box::new(TypedComp::new(
                    CompSig::new(int(), EffRow::Empty),
                    TypedCompKind::Return(var("r", int())),
                )),
            ),
        );
        assert!(
            strip_resume(&body, &resume_set(sym("k")), &drift).is_none(),
            "a resume off the tail is not tail-resumptive"
        );
    }

    // An alias of the resumption is tracked, so a clause that rebinds it still
    // strips (and, critically, still leaves no live reference behind).
    #[test]
    fn an_aliased_resume_is_tracked() {
        let drift = DriftLog::new(true);
        let tail = {
            let j = var("j", resume_ty());
            let CoreType::Thunk(sig) = resume_ty() else {
                unreachable!()
            };
            let force = TypedComp::new(*sig, TypedCompKind::Force(j));
            TypedComp::new(
                CompSig::new(int(), EffRow::Empty),
                TypedCompKind::App {
                    callee: Box::new(force),
                    instantiation: Vec::new(),
                    args: vec![TypedValue::new(int(), TypedValueKind::Int(3))],
                },
            )
        };
        // `let j = k in j(3)`
        let body = TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(resume_ty(), EffRow::Empty),
                    TypedCompKind::Return(var("k", resume_ty())),
                )),
                TypedBinder::new(sym("j"), resume_ty()),
                Box::new(tail),
            ),
        );
        let stripped = strip_resume(&body, &resume_set(sym("k")), &drift)
            .expect("an alias is still tail-resumptive");
        assert!(
            free_comp_vars(&stripped).is_disjoint(&resume_set(sym("k"))),
            "the guard's invariant: no resume reference survives a strip"
        );
    }
}
