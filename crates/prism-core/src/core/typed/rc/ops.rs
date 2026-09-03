//! Emitting one reference-count operation.
//!
//! Each of these takes the witness the ownership rules chose and wraps it around
//! a continuation. Nothing here decides whether an operation is needed; that is
//! the caller's job, and keeping the decision and the emission apart is what
//! lets the witness travel from the walk that found it to the term that carries
//! it without a lookup in between.

use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use super::super::verify::{clone_comp_sig, clone_core_type};
use super::super::{
    CompSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedValue, TypedValueKind,
};
use super::scope::{operand, Scope};
use super::{by_name, Set};

pub(super) const fn pure_unit() -> CompSig {
    CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty)
}

pub(super) fn seq(op: TypedComp, continuation: TypedComp) -> TypedComp {
    TypedComp::new(
        clone_comp_sig(&continuation.sig),
        TypedCompKind::Bind(
            Box::new(op),
            TypedBinder::rc_sequence(),
            Box::new(continuation),
        ),
    )
}

// The witness is the occurrence that justified the retain, not a lookup by
// name: a polymorphic global occurs at several instantiations and they are not
// interchangeable to a consumer that has to say which one a later release
// discharges.
pub(super) fn dup(witness: TypedValue, continuation: TypedComp) -> TypedComp {
    seq(
        TypedComp::new(pure_unit(), TypedCompKind::Dup(witness)),
        continuation,
    )
}

/// One retain per occurrence, each against the occurrence that needs it.
pub(super) fn dup_each(witnesses: Vec<TypedValue>, continuation: TypedComp) -> TypedComp {
    witnesses
        .into_iter()
        .fold(continuation, |out, witness| dup(witness, out))
}

pub(super) fn drop_(name: Sym, continuation: TypedComp, scope: &Scope) -> TypedComp {
    seq(
        TypedComp::new(pure_unit(), TypedCompKind::Drop(operand(scope, name))),
        continuation,
    )
}

pub(super) fn defer_call_drops(
    call: TypedComp,
    deferred: &Set,
    scope: &Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    let result = TypedBinder::new(
        Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump())),
        clone_core_type(&call.sig.result),
    );
    let returned = TypedValue::new(
        clone_core_type(&result.ty),
        TypedValueKind::Var {
            name: result.name,
            instantiation: Vec::new(),
        },
    );
    let mut post = TypedComp::new(
        CompSig::new(clone_core_type(&result.ty), EffRow::Empty),
        TypedCompKind::Return(returned),
    );
    for name in by_name(deferred.iter().copied()) {
        post = drop_(name, post, scope);
    }
    TypedComp::new(
        clone_comp_sig(&call.sig),
        TypedCompKind::Bind(Box::new(call), result, Box::new(post)),
    )
}
