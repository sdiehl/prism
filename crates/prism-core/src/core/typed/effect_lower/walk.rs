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

use crate::core::typed::traverse::Visit;
use crate::core::typed::{TypedComp, TypedCompKind, TypedHandleOp, TypedValue, TypedValueKind};

pub fn thunks_in_comp<'a>(c: &'a TypedComp, out: &mut Vec<&'a TypedComp>) {
    collect_thunks(ThunkFrame::Comp(c), out, true);
}

pub fn thunks_in_value<'a>(v: &'a TypedValue, out: &mut Vec<&'a TypedComp>) {
    collect_thunks(ThunkFrame::Value(v), out, true);
}

/// The thunks a value holds directly.
///
/// Aggregates and representation wrappers are transparent, but a thunk's own
/// body is not entered: a caller that recurses into every subterm it is handed
/// reaches each nested thunk exactly once this way, where [`thunks_in_value`]'s
/// transitive answer would hand it the same thunk again at every enclosing
/// level.
pub fn top_thunks_in_value<'a>(v: &'a TypedValue, out: &mut Vec<&'a TypedComp>) {
    collect_thunks(ThunkFrame::Value(v), out, false);
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
    let mut value = v;
    loop {
        match value.kind() {
            TypedValueKind::Thunk(_) => return true,
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::LoweredRepr { value: inner, .. }
            | TypedValueKind::NewtypeRepr { value: inner, .. } => value = inner,
            _ => return false,
        }
    }
}

enum ThunkFrame<'a> {
    Comp(&'a TypedComp),
    Value(&'a TypedValue),
}

fn collect_thunks<'a>(root: ThunkFrame<'a>, out: &mut Vec<&'a TypedComp>, descend_bodies: bool) {
    let mut stack = vec![root];
    while let Some(frame) = stack.pop() {
        match frame {
            ThunkFrame::Comp(comp) => {
                let start = stack.len();
                each_subcomp(comp, &mut |child| stack.push(ThunkFrame::Comp(child)));
                stack[start..].reverse();

                let start = stack.len();
                each_value(comp, &mut |value| stack.push(ThunkFrame::Value(value)));
                stack[start..].reverse();
            }
            ThunkFrame::Value(value) => match value.kind() {
                TypedValueKind::Thunk(body) => {
                    out.push(body);
                    if descend_bodies {
                        stack.push(ThunkFrame::Comp(body));
                    }
                }
                TypedValueKind::Reinterpret(inner)
                | TypedValueKind::LoweredRepr { value: inner, .. }
                | TypedValueKind::NewtypeRepr { value: inner, .. } => {
                    stack.push(ThunkFrame::Value(inner));
                }
                TypedValueKind::Ctor { fields, .. }
                | TypedValueKind::Tuple(fields)
                | TypedValueKind::UnboxedTuple(fields) => {
                    stack.extend(fields.iter().rev().map(ThunkFrame::Value));
                }
                TypedValueKind::UnboxedRecord(fields) => {
                    stack.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|(_, field)| ThunkFrame::Value(field)),
                    );
                }
                TypedValueKind::Var { .. }
                | TypedValueKind::Unit
                | TypedValueKind::Int(_)
                | TypedValueKind::I64(_)
                | TypedValueKind::U64(_)
                | TypedValueKind::Bool(_)
                | TypedValueKind::Float(_)
                | TypedValueKind::Str(_) => {}
            },
        }
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

#[must_use]
pub fn contains_mask(c: &TypedComp) -> bool {
    struct MaskFinder(bool);

    impl Visit for MaskFinder {
        fn comp(&mut self, comp: &TypedComp) -> bool {
            let masked = matches!(comp.kind(), TypedCompKind::Mask(..));
            self.0 |= masked;
            !masked
        }
    }

    let mut finder = MaskFinder(false);
    finder.walk_comp(c);
    finder.0
}

// Every effect op a computation names: performed (`Do`), handled (`Handle`
// arm), or masked, descending through thunks.
pub fn collect_ops(c: &TypedComp, out: &mut BTreeSet<Sym>) {
    OpCollector(out).walk_comp(c);
}

struct OpCollector<'a>(&'a mut BTreeSet<Sym>);

impl Visit for OpCollector<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        match comp.kind() {
            TypedCompKind::Do { operation, .. } => {
                self.0.insert(*operation);
            }
            TypedCompKind::Handle { ops, .. } => {
                self.0.extend(ops.arms().iter().map(TypedHandleOp::name));
            }
            TypedCompKind::Mask(ops, _) => self.0.extend(ops.iter().copied()),
            _ => {}
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;
    use crate::core::typed::{CompSig, CoreType, TypedBinder};
    use crate::types::ty::EffRow;
    use crate::types::Type;

    const DEEP_NODE_COUNT: usize = 50_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn unit_value() -> TypedValue {
        TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit)
    }

    fn unit_return() -> TypedComp {
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::Return(unit_value()),
        )
    }

    #[test]
    fn walk_queries_handle_deep_terms_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-effect-query-walks".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let pure_thunk_type = CoreType::Thunk(Box::new(unit_return().sig().clone()));
                let mut wrapped = TypedValue::new(
                    pure_thunk_type.clone(),
                    TypedValueKind::Thunk(Box::new(unit_return())),
                );
                for _ in 0..DEEP_NODE_COUNT {
                    wrapped = TypedValue::new(
                        pure_thunk_type.clone(),
                        TypedValueKind::Reinterpret(Box::new(wrapped)),
                    );
                }
                assert!(is_thunk(&wrapped));
                mem::forget(wrapped);

                let operation = Sym::new("Deep.perform");
                let effect = TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton(operation)),
                    TypedCompKind::Do {
                        operation,
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                );
                let thunk_type = CoreType::Thunk(Box::new(effect.sig().clone()));
                let mut nested =
                    TypedValue::new(thunk_type, TypedValueKind::Thunk(Box::new(effect)));
                for _ in 0..DEEP_NODE_COUNT {
                    nested = TypedValue::new(
                        CoreType::Source(Type::Unit),
                        TypedValueKind::Tuple(vec![nested]),
                    );
                }
                let mut top = Vec::new();
                top_thunks_in_value(&nested, &mut top);
                assert_eq!(top.len(), 1);
                drop(top);

                let mut body = TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    TypedCompKind::Return(nested),
                );
                for _ in 0..DEEP_NODE_COUNT {
                    let sig = body.sig().clone();
                    body = TypedComp::new(
                        sig,
                        TypedCompKind::Bind(
                            Box::new(unit_return()),
                            TypedBinder::new(Sym::new("ignored"), CoreType::Source(Type::Unit)),
                            Box::new(body),
                        ),
                    );
                }

                let mut thunks = Vec::new();
                thunks_in_comp(&body, &mut thunks);
                assert_eq!(thunks.len(), 1);
                let mut operations = BTreeSet::new();
                collect_ops(&body, &mut operations);
                assert_eq!(operations, BTreeSet::from([operation]));
                assert!(!contains_mask(&body));
                mem::forget(body);
            })
            .expect("spawn deep effect-query test")
            .join()
            .expect("deep effect-query test panicked");
    }
}
