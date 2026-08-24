//! Recursing into the suspended computations a leaf carries.
//!
//! A leaf's own references are counted where it sits, but a thunk it holds has a
//! body with its own ownership partition, and that body has to be walked before
//! the leaf is emitted.

use crate::core::fbip::Sigs;
use prism_common::fresh::Fresh;

use super::super::specialize_support::free_comp_vars;
use super::super::{TypedComp, TypedCompKind, TypedValue, TypedValueKind};
use super::scope::Scope;
use super::{rc, Set};

// A thunk cell owns its captures. The suspended body therefore treats captures
// as borrowed while lambda parameters remain owned.
pub(super) fn rc_value(
    value: &TypedValue,
    sigs: &Sigs,
    scope: &mut Scope,
    fresh: &mut Fresh,
) -> TypedValue {
    let kind = match &value.kind {
        TypedValueKind::Thunk(body) => TypedValueKind::Thunk(Box::new(rc(
            body,
            &Set::new(),
            &free_comp_vars(body),
            sigs,
            scope,
            fresh,
        ))),
        TypedValueKind::Ctor {
            name,
            tag,
            instantiation,
            fields,
        } => TypedValueKind::Ctor {
            name: *name,
            tag: *tag,
            instantiation: instantiation.clone(),
            fields: fields
                .iter()
                .map(|field| rc_value(field, sigs, scope, fresh))
                .collect(),
        },
        TypedValueKind::Tuple(fields) => TypedValueKind::Tuple(
            fields
                .iter()
                .map(|field| rc_value(field, sigs, scope, fresh))
                .collect(),
        ),
        TypedValueKind::UnboxedTuple(fields) => TypedValueKind::UnboxedTuple(
            fields
                .iter()
                .map(|field| rc_value(field, sigs, scope, fresh))
                .collect(),
        ),
        TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
            fields
                .iter()
                .map(|(name, field)| (*name, rc_value(field, sigs, scope, fresh)))
                .collect(),
        ),
        TypedValueKind::Reinterpret(inner) => {
            TypedValueKind::Reinterpret(Box::new(rc_value(inner, sigs, scope, fresh)))
        }
        TypedValueKind::LoweredRepr { value, proof } => TypedValueKind::LoweredRepr {
            value: Box::new(rc_value(value, sigs, scope, fresh)),
            proof: proof.clone(),
        },
        TypedValueKind::NewtypeRepr {
            constructor,
            instantiation,
            value,
        } => TypedValueKind::NewtypeRepr {
            constructor: *constructor,
            instantiation: instantiation.clone(),
            value: Box::new(rc_value(value, sigs, scope, fresh)),
        },
        _ => return value.clone(),
    };
    TypedValue::new(value.ty.clone(), kind)
}

pub(super) fn rc_thunks(
    comp: &TypedComp,
    sigs: &Sigs,
    scope: &mut Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    let kind = match &comp.kind {
        TypedCompKind::Return(result) => {
            TypedCompKind::Return(rc_value(result, sigs, scope, fresh))
        }
        TypedCompKind::Force(thunk) => TypedCompKind::Force(rc_value(thunk, sigs, scope, fresh)),
        TypedCompKind::Error(error) => TypedCompKind::Error(rc_value(error, sigs, scope, fresh)),
        TypedCompKind::Io(op, args) => TypedCompKind::Io(
            *op,
            args.iter()
                .map(|arg| rc_value(arg, sigs, scope, fresh))
                .collect(),
        ),
        TypedCompKind::FloatBuiltin(op, arg) => {
            TypedCompKind::FloatBuiltin(*op, rc_value(arg, sigs, scope, fresh))
        }
        TypedCompKind::Neg(lane, arg) => {
            TypedCompKind::Neg(*lane, rc_value(arg, sigs, scope, fresh))
        }
        TypedCompKind::Prim(op, lhs, rhs) => TypedCompKind::Prim(
            *op,
            rc_value(lhs, sigs, scope, fresh),
            rc_value(rhs, sigs, scope, fresh),
        ),
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } => TypedCompKind::Call {
            callee: *callee,
            instantiation: instantiation.clone(),
            args: args
                .iter()
                .map(|arg| rc_value(arg, sigs, scope, fresh))
                .collect(),
        },
        TypedCompKind::Do {
            operation,
            instantiation,
            args,
        } => TypedCompKind::Do {
            operation: *operation,
            instantiation: instantiation.clone(),
            args: args
                .iter()
                .map(|arg| rc_value(arg, sigs, scope, fresh))
                .collect(),
        },
        TypedCompKind::StrBuiltin {
            op,
            instantiation,
            args,
        } => TypedCompKind::StrBuiltin {
            op: *op,
            instantiation: instantiation.clone(),
            args: args
                .iter()
                .map(|arg| rc_value(arg, sigs, scope, fresh))
                .collect(),
        },
        TypedCompKind::App {
            callee,
            instantiation,
            args,
        } => TypedCompKind::App {
            callee: Box::new(rc_thunks(callee, sigs, scope, fresh)),
            instantiation: instantiation.clone(),
            args: args
                .iter()
                .map(|arg| rc_value(arg, sigs, scope, fresh))
                .collect(),
        },
        TypedCompKind::RefNew(initial) => {
            TypedCompKind::RefNew(rc_value(initial, sigs, scope, fresh))
        }
        TypedCompKind::RefGet(cell) => TypedCompKind::RefGet(rc_value(cell, sigs, scope, fresh)),
        TypedCompKind::RefSet(cell, new_value) => TypedCompKind::RefSet(
            rc_value(cell, sigs, scope, fresh),
            rc_value(new_value, sigs, scope, fresh),
        ),
        TypedCompKind::InitAt(cell, ctor) => TypedCompKind::InitAt(
            rc_value(cell, sigs, scope, fresh),
            rc_value(ctor, sigs, scope, fresh),
        ),
        _ => return comp.clone(),
    };
    TypedComp::new(comp.sig.clone(), kind)
}
