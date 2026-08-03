//! Generic typed-CBPV traversal/query combinators.
//!
//! `each_value` visits a computation's immediate value positions,
//! `each_subcomp` its immediate sub-computations, and `each_subterm` the union
//! of the two plus the thunks the values hold: the subterm inventory every
//! reachability and purity query in this directory recurses over.
//!
//! Thunk discovery descends through every aggregate field, boxed or unboxed,
//! and treats representation wrappers as transparent, looking through
//! `Reinterpret`/`NewtypeRepr`/`LoweredRepr` while callers keep the original
//! wrapped values. A thunk buried in a constructor is still a computation the
//! program can force, so a walk that stopped at the wrapper would answer
//! "performs nothing" for code that performs everything.

use std::collections::BTreeSet;

use prism_common::sym::Sym;

use super::super::{TypedComp, TypedCompKind, TypedValue, TypedValueKind};

pub fn thunks_in_comp<'a>(c: &'a TypedComp, out: &mut Vec<&'a TypedComp>) {
    each_value(c, &mut |v| thunks_in_value(v, out));
    each_subcomp(c, &mut |sc| thunks_in_comp(sc, out));
}

pub fn thunks_in_value<'a>(v: &'a TypedValue, out: &mut Vec<&'a TypedComp>) {
    let mut top = Vec::new();
    top_thunks_in_value(v, &mut top);
    for t in top {
        out.push(t);
        thunks_in_comp(t, out);
    }
}

/// The thunks a value holds directly.
///
/// Aggregates and representation wrappers are transparent, but a thunk's own
/// body is not entered: a caller that recurses into every subterm it is handed
/// reaches each nested thunk exactly once this way, where [`thunks_in_value`]'s
/// transitive answer would hand it the same thunk again at every enclosing
/// level.
pub fn top_thunks_in_value<'a>(v: &'a TypedValue, out: &mut Vec<&'a TypedComp>) {
    match &v.kind {
        TypedValueKind::Thunk(c) => {
            out.push(c);
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            top_thunks_in_value(inner, out);
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for f in fields {
                top_thunks_in_value(f, out);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, f) in fields {
                top_thunks_in_value(f, out);
            }
        }
        // The remaining forms carry no nested values; enumerated so a new
        // variant fails the match rather than silently hiding a thunk from
        // every reachability and purity query built on this walk.
        TypedValueKind::Var { .. }
        | TypedValueKind::Unit
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Str(_) => {}
    }
}

/// Whether a value is a thunk in its own right, rather than an aggregate
/// holding thunks in its fields.
///
/// Representation wrappers are transparent here exactly as they are to
/// [`top_thunks_in_value`], so the two agree on which value a thunk was found
/// at: a thunk standing alone is named by the position it flows from, where a
/// field of an aggregate is named by nothing until a later `case` extracts it.
#[must_use]
pub fn is_thunk(v: &TypedValue) -> bool {
    match &v.kind {
        TypedValueKind::Thunk(_) => true,
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => is_thunk(inner),
        _ => false,
    }
}

pub fn each_value<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedValue)) {
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

pub fn each_subcomp<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedComp)) {
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
pub fn each_subterm<'a>(c: &'a TypedComp, f: &mut impl FnMut(&'a TypedComp)) {
    each_subcomp(c, f);
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        top_thunks_in_value(v, &mut ts);
        for t in ts {
            f(t);
        }
    });
}

// Every effect op a computation names: performed (`Do`), handled (`Handle`
// arm), or masked, descending through thunks.
pub fn collect_ops(c: &TypedComp, out: &mut BTreeSet<Sym>) {
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
    each_subterm(c, &mut |sub| collect_ops(sub, out));
}
