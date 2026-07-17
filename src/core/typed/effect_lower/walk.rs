//! Generic typed-CBPV traversal/query combinators.
//!
//! `each_value` visits a computation's immediate value positions,
//! `each_subcomp` its immediate sub-computations, and the thunk collectors
//! descend through constructor and tuple fields. Representation wrappers are
//! transparent to thunk discovery, so collection looks through
//! `Reinterpret`/`NewtypeRepr` while callers keep the original wrapped values.

use std::collections::BTreeSet;

use crate::sym::Sym;

use super::super::{TypedComp, TypedCompKind, TypedValue, TypedValueKind};

pub(super) fn thunks_in_comp<'a>(c: &'a TypedComp, out: &mut Vec<&'a TypedComp>) {
    each_value(c, &mut |v| thunks_in_value(v, out));
    each_subcomp(c, &mut |sc| thunks_in_comp(sc, out));
}

pub(super) fn thunks_in_value<'a>(v: &'a TypedValue, out: &mut Vec<&'a TypedComp>) {
    match &v.kind {
        TypedValueKind::Thunk(c) => {
            out.push(c);
            thunks_in_comp(c, out);
        }
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            thunks_in_value(inner, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                thunks_in_value(f, out);
            }
        }
        _ => {}
    }
}

pub(super) fn each_value<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedValue)) {
    match c.kind() {
        TypedCompKind::Return(v)
        | TypedCompKind::Force(v)
        | TypedCompKind::Error(v)
        | TypedCompKind::FloatBuiltin(_, v)
        | TypedCompKind::Neg(_, v)
        | TypedCompKind::Dup(v)
        | TypedCompKind::Drop(v)
        | TypedCompKind::WithReuse { freed: v, .. }
        | TypedCompKind::Reuse(_, v)
        | TypedCompKind::RefNew(v)
        | TypedCompKind::RefGet(v)
        | TypedCompKind::UnboxedProject(v, _)
        | TypedCompKind::If(v, ..)
        | TypedCompKind::Case(v, _) => f(v),
        TypedCompKind::Prim(_, a, b)
        | TypedCompKind::RefSet(a, b)
        | TypedCompKind::InitAt(a, b) => {
            f(a);
            f(b);
        }
        TypedCompKind::App { args, .. }
        | TypedCompKind::Call { args, .. }
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. }
        | TypedCompKind::Io(_, args) => {
            for a in args {
                f(a);
            }
        }
        // The remaining forms carry no immediate value positions (their
        // children are all sub-computations); enumerated so a new variant
        // fails the match.
        TypedCompKind::Bind(..)
        | TypedCompKind::Lam(..)
        | TypedCompKind::Mask(..)
        | TypedCompKind::Handle { .. } => {}
    }
}

pub(super) fn each_subcomp<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedComp)) {
    match c.kind() {
        TypedCompKind::Bind(m, _, n) => {
            f(m);
            f(n);
        }
        TypedCompKind::Lam(_, b)
        | TypedCompKind::Mask(_, b)
        | TypedCompKind::WithReuse { body: b, .. } => f(b),
        TypedCompKind::App { callee, .. } => f(callee),
        TypedCompKind::If(_, t, e) => {
            f(t);
            f(e);
        }
        TypedCompKind::Case(_, arms) => {
            for (_, b) in arms {
                f(b);
            }
        }
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            f(body);
            if let Some(rb) = return_body {
                f(rb);
            }
            for o in ops.arms() {
                f(o.body());
            }
        }
        // The remaining forms carry no immediate sub-computations (their
        // children are all values); enumerated so a new variant fails the
        // match.
        TypedCompKind::Return(_)
        | TypedCompKind::Force(_)
        | TypedCompKind::Error(_)
        | TypedCompKind::FloatBuiltin(..)
        | TypedCompKind::Neg(..)
        | TypedCompKind::UnboxedProject(..)
        | TypedCompKind::Dup(_)
        | TypedCompKind::Drop(_)
        | TypedCompKind::Reuse(..)
        | TypedCompKind::InitAt(..)
        | TypedCompKind::RefNew(_)
        | TypedCompKind::RefGet(_)
        | TypedCompKind::RefSet(..)
        | TypedCompKind::Prim(..)
        | TypedCompKind::Call { .. }
        | TypedCompKind::Do { .. }
        | TypedCompKind::StrBuiltin { .. }
        | TypedCompKind::Io(..) => {}
    }
}

// Visit immediate sub-computations and thunk bodies in immediate values, the
// common subterm inventory shared by the erasure analyses.
pub(super) fn each_subterm<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedComp)) {
    each_subcomp(c, f);
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            f(t);
        }
    });
}

// Every effect op a computation names: performed (`Do`), handled (`Handle`
// arm), or masked, descending through thunks.
pub(super) fn collect_ops(c: &TypedComp, out: &mut BTreeSet<Sym>) {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => {
            out.insert(*operation);
        }
        TypedCompKind::Handle { ops, .. } => {
            for op in ops.arms() {
                out.insert(op.name());
            }
        }
        TypedCompKind::Mask(ops, _) => out.extend(ops.iter().copied()),
        _ => {}
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            collect_ops(t, out);
        }
    });
    each_subcomp(c, &mut |sc| collect_ops(sc, out));
}
