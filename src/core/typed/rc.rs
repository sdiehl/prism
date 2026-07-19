//! Reference-count insertion for witness-carrying Core.
//!
//! This is the typed counterpart of [`super::super::fbip::insert_rc`]. It keeps
//! the same ownership partition, free-variable decisions, borrow masks, and
//! name-stable insertion order while retaining the witness for every inserted
//! `dup` and `drop` operand.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::fbip::Sigs;
use crate::names;
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;
use crate::util::fresh::Fresh;

use super::specialize_support::free_comp_vars;
use super::{
    CompSig, CoreType, EffectLowered, Owned, TypedBinder, TypedComp, TypedCompKind, TypedCore,
    TypedCoreFn, TypedHandleOp, TypedHandler, TypedPattern, TypedValue, TypedValueKind,
};

type Set = BTreeSet<Sym>;
type Scope = BTreeMap<Sym, TypedValue>;

/// Insert precise reference-count operations without erasing type witnesses.
#[must_use]
pub(crate) fn insert_rc(core: TypedCore<EffectLowered>, sigs: &Sigs) -> TypedCore<Owned> {
    let globals = reference_scope(&core);
    let mut fresh = Fresh::new();
    let fns = core
        .fns
        .into_iter()
        .map(|function| {
            let mask = sigs.get(&function.name).map(Vec::as_slice);
            let owned: Set = function
                .params
                .iter()
                .enumerate()
                .filter(|(index, _)| !borrowed_at(mask, *index))
                .map(|(_, binder)| binder.name)
                .collect();
            let borrowed: Set = function
                .params
                .iter()
                .enumerate()
                .filter(|(index, _)| borrowed_at(mask, *index))
                .map(|(_, binder)| binder.name)
                .collect();
            let scope = with_binders(&globals, &function.params);
            let body = rc(&function.body, &owned, &borrowed, sigs, &scope, &mut fresh);
            TypedCoreFn::new(
                function.name,
                function.params,
                body,
                function.sig,
                function.dict_arity,
            )
        })
        .collect();
    TypedCore::new(fns)
}

fn borrowed_at(mask: Option<&[bool]>, index: usize) -> bool {
    mask.is_some_and(|entries| entries.get(index).copied().unwrap_or(false))
}

// `Sym` orders by intern id, which is intentionally unrelated to the stable
// emitted order. RC operations are therefore sorted by their textual names.
fn by_name(syms: impl IntoIterator<Item = Sym>) -> Vec<Sym> {
    let mut names: Vec<Sym> = syms.into_iter().collect();
    names.sort_by(|lhs, rhs| lhs.as_str().cmp(rhs.as_str()));
    names
}

fn binder_value(binder: &TypedBinder) -> TypedValue {
    TypedValue::new(
        binder.ty.clone(),
        TypedValueKind::Var {
            name: binder.name,
            instantiation: Vec::new(),
        },
    )
}

fn with_binders(scope: &Scope, binders: &[TypedBinder]) -> Scope {
    let mut nested = scope.clone();
    for binder in binders {
        nested.insert(binder.name, binder_value(binder));
    }
    nested
}

fn with_optional_binder(scope: &Scope, binder: Option<&TypedBinder>) -> Scope {
    let mut nested = scope.clone();
    if let Some(binder) = binder {
        nested.insert(binder.name, binder_value(binder));
    }
    nested
}

fn operand(scope: &Scope, name: Sym) -> TypedValue {
    scope
        .get(&name)
        .unwrap_or_else(|| panic!("verified RC operand {name} is out of scope"))
        .clone()
}

const fn pure_unit() -> CompSig {
    CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty)
}

fn seq(op: TypedComp, continuation: TypedComp) -> TypedComp {
    TypedComp::new(
        continuation.sig.clone(),
        TypedCompKind::Bind(
            Box::new(op),
            TypedBinder::rc_sequence(),
            Box::new(continuation),
        ),
    )
}

fn dup(name: Sym, continuation: TypedComp, scope: &Scope) -> TypedComp {
    seq(
        TypedComp::new(pure_unit(), TypedCompKind::Dup(operand(scope, name))),
        continuation,
    )
}

fn drop_(name: Sym, continuation: TypedComp, scope: &Scope) -> TypedComp {
    seq(
        TypedComp::new(pure_unit(), TypedCompKind::Drop(operand(scope, name))),
        continuation,
    )
}

fn erased_var(value: &TypedValue) -> Option<Sym> {
    match &value.kind {
        TypedValueKind::Var { name, .. } => Some(*name),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => erased_var(inner),
        _ => None,
    }
}

fn borrowed_call_vars(comp: &TypedComp, sigs: &Sigs) -> Set {
    let TypedCompKind::Call { callee, args, .. } = &comp.kind else {
        return Set::new();
    };
    let mask = sigs.get(callee).map(Vec::as_slice);
    args.iter()
        .enumerate()
        .filter(|(index, _)| borrowed_at(mask, *index))
        .map(|(_, arg)| {
            erased_var(arg).unwrap_or_else(|| {
                panic!("borrowed call argument to {callee} is not an erased variable")
            })
        })
        .collect()
}

fn defer_call_drops(
    call: TypedComp,
    deferred: &Set,
    scope: &Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    let result = TypedBinder::new(
        Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump())),
        call.sig.result.clone(),
    );
    let returned = TypedValue::new(
        result.ty.clone(),
        TypedValueKind::Var {
            name: result.name,
            instantiation: Vec::new(),
        },
    );
    let mut post = TypedComp::new(
        CompSig::new(result.ty.clone(), EffRow::Empty),
        TypedCompKind::Return(returned),
    );
    for name in by_name(deferred.iter().copied()) {
        post = drop_(name, post, scope);
    }
    TypedComp::new(
        call.sig.clone(),
        TypedCompKind::Bind(Box::new(call), result, Box::new(post)),
    )
}

#[allow(clippy::too_many_lines)]
fn rc(
    comp: &TypedComp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    scope: &Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    match &comp.kind {
        TypedCompKind::Bind(first, binder, rest) => {
            let first_free = free_comp_vars(first);
            let mut rest_free = free_comp_vars(rest);
            rest_free.remove(&binder.name);
            let first_owned: Set = owned.intersection(&first_free).copied().collect();
            let rest_owned: Set = owned.intersection(&rest_free).copied().collect();
            let shared = by_name(first_owned.intersection(&rest_owned).copied());
            let dead = by_name(
                owned
                    .iter()
                    .filter(|name| !first_free.contains(*name) && !rest_free.contains(*name))
                    .copied(),
            );
            let first_borrowed: Set = borrowed.intersection(&first_free).copied().collect();
            let rest_borrowed: Set = borrowed.intersection(&rest_free).copied().collect();
            let first = rc(first, &first_owned, &first_borrowed, sigs, scope, fresh);
            let rest_scope = with_binders(scope, std::slice::from_ref(binder));
            let mut rest_owned = rest_owned;
            rest_owned.insert(binder.name);
            let rest = rc(rest, &rest_owned, &rest_borrowed, sigs, &rest_scope, fresh);
            let mut out = TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Bind(Box::new(first), binder.clone(), Box::new(rest)),
            );
            for name in shared {
                out = dup(name, out, scope);
            }
            for name in dead {
                out = drop_(name, out, scope);
            }
            out
        }
        TypedCompKind::If(condition, yes, no) => TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::If(
                condition.clone(),
                Box::new(rc(yes, owned, borrowed, sigs, scope, fresh)),
                Box::new(rc(no, owned, borrowed, sigs, scope, fresh)),
            ),
        ),
        TypedCompKind::Case(scrutinee, arms) => TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Case(
                scrutinee.clone(),
                arms.iter()
                    .map(|(pattern, body)| {
                        (
                            pattern.clone(),
                            rc_arm(pattern, body, owned, borrowed, sigs, scope, fresh),
                        )
                    })
                    .collect(),
            ),
        ),
        TypedCompKind::Lam(params, body) => {
            let params_set: Set = params.iter().map(|binder| binder.name).collect();
            let captures: Set = free_comp_vars(body)
                .difference(&params_set)
                .copied()
                .collect();
            let body_scope = with_binders(scope, params);
            TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Lam(
                    params.clone(),
                    Box::new(rc(body, &params_set, &captures, sigs, &body_scope, fresh)),
                ),
            )
        }
        TypedCompKind::Mask(effects, body) => TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Mask(
                effects.clone(),
                Box::new(rc(body, owned, borrowed, sigs, scope, fresh)),
            ),
        ),
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            let body = Box::new(rc(body, &Set::new(), &Set::new(), sigs, scope, fresh));
            let return_scope = with_optional_binder(scope, return_binder.as_ref());
            let return_body = return_body.as_ref().map(|body| {
                let owned = return_binder.iter().map(|binder| binder.name).collect();
                Box::new(rc(body, &owned, &Set::new(), sigs, &return_scope, fresh))
            });
            let arms = ops
                .arms
                .iter()
                .map(|arm| {
                    let owned = arm.params.iter().map(|binder| binder.name).collect();
                    let mut binders = arm.params.clone();
                    binders.push(arm.resume.clone());
                    let arm_scope = with_binders(scope, &binders);
                    TypedHandleOp::new(
                        arm.name,
                        arm.instantiation.clone(),
                        arm.params.clone(),
                        arm.resume.clone(),
                        rc(&arm.body, &owned, &Set::new(), sigs, &arm_scope, fresh),
                    )
                })
                .collect();
            TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Handle {
                    body,
                    return_binder: return_binder.clone(),
                    return_body,
                    ops: TypedHandler {
                        arms,
                        forwarded: ops.forwarded.clone(),
                    },
                },
            )
        }
        _ => {
            let mut counts = BTreeMap::new();
            leaf_counts(comp, &mut counts, sigs);
            let borrowed_call = borrowed_call_vars(comp, sigs);
            let deferred: Set = owned.intersection(&borrowed_call).copied().collect();
            let mut out = rc_thunks(comp, sigs, scope, fresh);
            if !deferred.is_empty() {
                out = defer_call_drops(out, &deferred, scope, fresh);
            }
            for name in by_name(owned.iter().copied()) {
                let count = counts.get(&name).copied().unwrap_or(0);
                if deferred.contains(&name) {
                    for _ in 0..count {
                        out = dup(name, out, scope);
                    }
                } else {
                    match count {
                        0 => out = drop_(name, out, scope),
                        count => {
                            for _ in 1..count {
                                out = dup(name, out, scope);
                            }
                        }
                    }
                }
            }
            for name in by_name(borrowed.iter().copied()) {
                for _ in 0..counts.get(&name).copied().unwrap_or(0) {
                    out = dup(name, out, scope);
                }
            }
            out
        }
    }
}

// A thunk cell owns its captures. The suspended body therefore treats captures
// as borrowed while lambda parameters remain owned.
fn rc_value(value: &TypedValue, sigs: &Sigs, scope: &Scope, fresh: &mut Fresh) -> TypedValue {
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

fn rc_thunks(comp: &TypedComp, sigs: &Sigs, scope: &Scope, fresh: &mut Fresh) -> TypedComp {
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

fn pattern_binders(pattern: &TypedPattern) -> Vec<TypedBinder> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.clone()],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().cloned().collect()
        }
    }
}

fn rc_arm(
    pattern: &TypedPattern,
    body: &TypedComp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    scope: &Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    let body_free = free_comp_vars(body);
    let binders = pattern_binders(pattern);
    let fields: Set = binders.iter().map(|binder| binder.name).collect();
    let live = by_name(fields.intersection(&body_free).copied());
    let dead = by_name(
        owned
            .iter()
            .filter(|name| !body_free.contains(*name))
            .copied(),
    );
    let mut body_owned: Set = owned.intersection(&body_free).copied().collect();
    body_owned.extend(live.iter().copied());
    let body_borrowed: Set = borrowed.intersection(&body_free).copied().collect();
    let body_scope = with_binders(scope, &binders);
    let mut out = rc(body, &body_owned, &body_borrowed, sigs, &body_scope, fresh);
    for name in &dead {
        out = drop_(*name, out, &body_scope);
    }
    for name in live.iter().rev() {
        out = dup(*name, out, &body_scope);
    }
    out
}

fn count_value(value: &TypedValue, counts: &mut BTreeMap<Sym, usize>) {
    match &value.kind {
        TypedValueKind::Var { name, .. } => *counts.entry(*name).or_default() += 1,
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                count_value(field, counts);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                count_value(field, counts);
            }
        }
        TypedValueKind::Thunk(body) => {
            for name in free_comp_vars(body) {
                *counts.entry(name).or_default() += 1;
            }
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => count_value(inner, counts),
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

fn leaf_counts(comp: &TypedComp, counts: &mut BTreeMap<Sym, usize>, sigs: &Sigs) {
    match &comp.kind {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => count_value(value, counts),
        TypedCompKind::RefSet(cell, value) | TypedCompKind::InitAt(cell, value) => {
            count_value(cell, counts);
            count_value(value, counts);
        }
        TypedCompKind::App { callee, args, .. } => {
            for name in free_comp_vars(callee) {
                *counts.entry(name).or_default() += 1;
            }
            for arg in args {
                count_value(arg, counts);
            }
        }
        TypedCompKind::Prim(_, lhs, rhs) => {
            count_value(lhs, counts);
            count_value(rhs, counts);
        }
        TypedCompKind::Call { callee, args, .. } => {
            let mask = sigs.get(callee).map(Vec::as_slice);
            for (index, arg) in args.iter().enumerate() {
                if !borrowed_at(mask, index) {
                    count_value(arg, counts);
                }
            }
        }
        TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. }
        | TypedCompKind::Io(_, args) => {
            for arg in args {
                count_value(arg, counts);
            }
        }
        TypedCompKind::Bind(_, _, _)
        | TypedCompKind::Lam(_, _)
        | TypedCompKind::If(_, _, _)
        | TypedCompKind::Case(_, _)
        | TypedCompKind::Handle { .. }
        | TypedCompKind::Mask(_, _)
        | TypedCompKind::UnboxedProject(_, _)
        | TypedCompKind::Dup(_)
        | TypedCompKind::Drop(_)
        | TypedCompKind::WithReuse { .. }
        | TypedCompKind::Reuse(_, _) => {}
    }
}

// A polymorphic global may occur at several instances. RC operations inspect
// only its runtime word, so the first verified, lexically unshadowed occurrence
// is a sufficient operand witness for every inserted operation on that symbol.
// The declared-signature fallback is used only when no value occurrence exists.
fn reference_scope(core: &TypedCore<EffectLowered>) -> Scope {
    let globals: Set = core.fns.iter().map(|function| function.name).collect();
    let mut scope = Scope::new();
    for function in &core.fns {
        let mut bound: Vec<Sym> = function.params.iter().map(|binder| binder.name).collect();
        collect_global_refs_comp(&function.body, &globals, &mut bound, &mut scope);
    }
    for function in &core.fns {
        scope.entry(function.name).or_insert_with(|| {
            TypedValue::new(
                CoreType::Function(Box::new(function.sig.clone())),
                TypedValueKind::Var {
                    name: function.name,
                    instantiation: Vec::new(),
                },
            )
        });
    }
    scope
}

fn collect_global_refs_value(
    value: &TypedValue,
    globals: &Set,
    bound: &mut Vec<Sym>,
    scope: &mut Scope,
) {
    match &value.kind {
        TypedValueKind::Var { name, .. } => {
            if globals.contains(name) && !bound.contains(name) {
                scope.entry(*name).or_insert_with(|| value.clone());
            }
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            collect_global_refs_value(inner, globals, bound, scope);
        }
        TypedValueKind::Thunk(body) => collect_global_refs_comp(body, globals, bound, scope),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_global_refs_value(field, globals, bound, scope);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_global_refs_value(field, globals, bound, scope);
            }
        }
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

#[allow(clippy::too_many_lines)]
fn collect_global_refs_comp(
    comp: &TypedComp,
    globals: &Set,
    bound: &mut Vec<Sym>,
    scope: &mut Scope,
) {
    match &comp.kind {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value)
        | TypedCompKind::Reuse(_, value) => {
            collect_global_refs_value(value, globals, bound, scope);
        }
        TypedCompKind::Prim(_, lhs, rhs)
        | TypedCompKind::RefSet(lhs, rhs)
        | TypedCompKind::InitAt(lhs, rhs) => {
            collect_global_refs_value(lhs, globals, bound, scope);
            collect_global_refs_value(rhs, globals, bound, scope);
        }
        TypedCompKind::Bind(first, binder, rest) => {
            collect_global_refs_comp(first, globals, bound, scope);
            let old_len = bound.len();
            bound.push(binder.name);
            collect_global_refs_comp(rest, globals, bound, scope);
            bound.truncate(old_len);
        }
        TypedCompKind::Lam(params, body) => {
            let old_len = bound.len();
            bound.extend(params.iter().map(|binder| binder.name));
            collect_global_refs_comp(body, globals, bound, scope);
            bound.truncate(old_len);
        }
        TypedCompKind::Mask(_, body) => {
            collect_global_refs_comp(body, globals, bound, scope);
        }
        TypedCompKind::App { callee, args, .. } => {
            collect_global_refs_comp(callee, globals, bound, scope);
            for arg in args {
                collect_global_refs_value(arg, globals, bound, scope);
            }
        }
        TypedCompKind::If(condition, yes, no) => {
            collect_global_refs_value(condition, globals, bound, scope);
            collect_global_refs_comp(yes, globals, bound, scope);
            collect_global_refs_comp(no, globals, bound, scope);
        }
        TypedCompKind::Call { args, .. }
        | TypedCompKind::Io(_, args)
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. } => {
            for arg in args {
                collect_global_refs_value(arg, globals, bound, scope);
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            collect_global_refs_value(scrutinee, globals, bound, scope);
            for (pattern, body) in arms {
                let old_len = bound.len();
                bound.extend(pattern_binders(pattern).iter().map(|binder| binder.name));
                collect_global_refs_comp(body, globals, bound, scope);
                bound.truncate(old_len);
            }
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            collect_global_refs_comp(body, globals, bound, scope);
            if let Some(return_body) = return_body {
                let old_len = bound.len();
                bound.extend(return_binder.iter().map(|binder| binder.name));
                collect_global_refs_comp(return_body, globals, bound, scope);
                bound.truncate(old_len);
            }
            for arm in &ops.arms {
                let old_len = bound.len();
                bound.extend(arm.params.iter().map(|binder| binder.name));
                bound.push(arm.resume.name);
                collect_global_refs_comp(&arm.body, globals, bound, scope);
                bound.truncate(old_len);
            }
        }
        TypedCompKind::WithReuse { token, freed, body } => {
            collect_global_refs_value(freed, globals, bound, scope);
            let old_len = bound.len();
            bound.push(token.name);
            collect_global_refs_comp(body, globals, bound, scope);
            bound.truncate(old_len);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::core::fbip::{balanced, insert_rc as legacy_insert_rc};
    use crate::core::{Comp, Value};
    use crate::names::ALLOC_OP;
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::verify::{verify, OperationSig, VerifyEnv};
    use super::super::{CoreFnSig, CoreInstantiation, CoreQuantifier, LoweredType, TypedValueKind};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
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

    fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(value.ty.clone()), TypedCompKind::Return(value))
    }

    fn function(name: &str, params: Vec<TypedBinder>, body: TypedComp) -> TypedCoreFn {
        let signature = CoreFnSig::new(
            Vec::new(),
            params.iter().map(|binder| binder.ty.clone()).collect(),
            body.sig.clone(),
        );
        TypedCoreFn::new(sym(name), params, body, signature, 0)
    }

    fn head_dup<'a>(comp: &'a Comp, name: &str) -> &'a Comp {
        let Comp::Bind(op, binder, rest) = comp else {
            panic!("expected a leading dup, found {comp:?}");
        };
        assert_eq!(binder.as_str(), "_");
        assert!(matches!(
            &**op,
            Comp::Dup(Value::Var(actual)) if *actual == sym(name)
        ));
        rest
    }

    fn head_drop<'a>(comp: &'a Comp, name: &str) -> &'a Comp {
        let Comp::Bind(op, binder, rest) = comp else {
            panic!("expected a leading drop, found {comp:?}");
        };
        assert_eq!(binder.as_str(), "_");
        assert!(matches!(
            &**op,
            Comp::Drop(Value::Var(actual)) if *actual == sym(name)
        ));
        rest
    }

    fn assert_differential(
        input: &TypedCore<EffectLowered>,
        sigs: &Sigs,
        env: &VerifyEnv,
    ) -> TypedCore<Owned> {
        if let Err(violations) = verify(input, env) {
            panic!("input fixture is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let expected = legacy_insert_rc(&legacy_input, sigs);
        let actual = insert_rc(input.clone(), sigs);
        if let Err(violations) = verify(&actual, env) {
            panic!("owned typed Core is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        if let Err(error) = balanced(&expected, sigs) {
            panic!("legacy balance oracle rejected the fixture: {error}");
        }
        actual
    }

    #[test]
    fn borrow_masks_preserve_the_calling_convention() {
        let int = source(Type::Int);
        let parameter = TypedBinder::new(sym("borrowed"), int.clone());
        let body = ret(var("borrowed", int));
        let observe = function("observe", vec![parameter], body);
        let retained = TypedBinder::new(sym("retained"), source(Type::Int));
        let call = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Call {
                callee: sym("observe"),
                instantiation: Vec::new(),
                args: vec![var("retained", source(Type::Int))],
            },
        );
        let caller = function("caller", vec![retained], call);
        let input = TypedCore::new(vec![observe, caller]);
        let sigs = std::iter::once((sym("observe"), vec![true])).collect();
        let actual = assert_differential(&input, &sigs, &VerifyEnv::new()).erase();
        let observe_rest = head_dup(&actual.fns[0].body, "borrowed");
        assert!(matches!(
            observe_rest,
            Comp::Return(Value::Var(name)) if *name == sym("borrowed")
        ));
        let Comp::Bind(call, result, post) = &actual.fns[1].body else {
            panic!("borrowed tail call must retain its argument through the call");
        };
        assert!(matches!(
            &**call,
            Comp::Call(name, args)
                if *name == sym("observe")
                    && matches!(args.as_slice(), [Value::Var(arg)] if *arg == sym("retained"))
        ));
        assert_eq!(result.as_str(), "%rc0");
        let returned = head_drop(post, "retained");
        assert!(matches!(
            returned,
            Comp::Return(Value::Var(name)) if name == result
        ));
    }

    #[test]
    fn an_owned_and_borrowed_alias_keeps_a_loan_token_through_the_call() {
        let int = source(Type::Int);
        let owned = TypedBinder::new(sym("owned"), int.clone());
        let loan = TypedBinder::new(sym("loan"), int.clone());
        let callee = function(
            "consume_and_borrow",
            vec![owned, loan],
            ret(var("owned", int.clone())),
        );
        let shared = TypedBinder::new(sym("shared"), int.clone());
        let call = TypedComp::new(
            pure(int.clone()),
            TypedCompKind::Call {
                callee: sym("consume_and_borrow"),
                instantiation: Vec::new(),
                args: vec![var("shared", int.clone()), var("shared", int)],
            },
        );
        let invoking_function = function("caller", vec![shared], call);
        let input = TypedCore::new(vec![callee, invoking_function]);
        let sigs = std::iter::once((sym("consume_and_borrow"), vec![false, true])).collect();
        let actual = assert_differential(&input, &sigs, &VerifyEnv::new()).erase();

        let after_loan = head_dup(&actual.fns[1].body, "shared");
        let Comp::Bind(call, result, post) = after_loan else {
            panic!("aliased call must defer loan cleanup");
        };
        assert!(matches!(
            &**call,
            Comp::Call(name, args)
                if *name == sym("consume_and_borrow")
                    && matches!(
                        args.as_slice(),
                        [Value::Var(lhs), Value::Var(rhs)]
                            if *lhs == sym("shared") && *rhs == sym("shared")
                    )
        ));
        assert_eq!(result.as_str(), "%rc0");
        let returned = head_drop(post, "shared");
        assert!(matches!(
            returned,
            Comp::Return(Value::Var(name)) if name == result
        ));
    }

    #[test]
    fn thunk_captures_are_borrowed_inside_the_suspension() {
        let int = source(Type::Int);
        let capture = TypedBinder::new(sym("capture"), int.clone());
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(pure(int.clone()))),
            TypedValueKind::Thunk(Box::new(ret(var("capture", int)))),
        );
        let input = TypedCore::new(vec![function("main", vec![capture], ret(thunk))]);
        assert_differential(&input, &Sigs::new(), &VerifyEnv::new());
    }

    #[test]
    fn rc_sequence_binders_do_not_shadow_a_lowered_word_discard() {
        let int = source(Type::Int);
        let capture = TypedBinder::new(sym("capture"), int.clone());
        let word = CoreType::Lowered(LoweredType::Word);
        let discarded = TypedBinder::new(sym("_"), word.clone());
        let lambda_sig = CoreFnSig::new(Vec::new(), vec![word], pure(int.clone()));
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(lambda_sig))),
            TypedCompKind::Lam(vec![discarded], Box::new(ret(var("capture", int)))),
        );
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig.clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        );
        let input = TypedCore::new(vec![function("main", vec![capture], ret(thunk))]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new());

        let TypedCompKind::Return(thunk) = &actual.fns[0].body.kind else {
            panic!("expected returned thunk");
        };
        let TypedValueKind::Thunk(lambda) = &thunk.kind else {
            panic!("expected retained thunk body");
        };
        let TypedCompKind::Lam(_, body) = &lambda.kind else {
            panic!("expected retained lambda body");
        };
        let TypedCompKind::Bind(_, first_sequence, rest) = &body.kind else {
            panic!("expected the capture dup to be sequenced");
        };
        assert_eq!(first_sequence.name().as_str(), names::RC_SEQUENCE_BINDER);
        assert_eq!(first_sequence.erase_name().as_str(), "_");
        let TypedCompKind::Bind(_, second_sequence, _) = &rest.kind else {
            panic!("expected the discarded parameter drop to be sequenced");
        };
        assert_eq!(second_sequence.name().as_str(), names::RC_SEQUENCE_BINDER);
        assert_eq!(second_sequence.erase_name().as_str(), "_");
    }

    #[test]
    fn unboxed_products_rewrite_the_thunks_they_contain() {
        let int = source(Type::Int);
        let source_function = Type::Fun(Vec::new(), EffRow::Empty, Box::new(Type::Int));
        let captured_thunk = |capture: &str| {
            let closure_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(int.clone()));
            let closure = TypedComp::new(
                pure(CoreType::Function(Box::new(closure_sig))),
                TypedCompKind::Lam(Vec::new(), Box::new(ret(var(capture, int.clone())))),
            );
            TypedValue::new(
                CoreType::Thunk(Box::new(closure.sig.clone())),
                TypedValueKind::Thunk(Box::new(closure)),
            )
        };

        let tuple_capture = TypedBinder::new(sym("tuple_capture"), int.clone());
        let tuple = TypedValue::new(
            source(Type::UnboxedTuple(vec![source_function.clone()])),
            TypedValueKind::UnboxedTuple(vec![captured_thunk("tuple_capture")]),
        );
        let tuple_function = function("tuple", vec![tuple_capture], ret(tuple));

        let field_name = sym("run");
        let record_capture = TypedBinder::new(sym("record_capture"), int.clone());
        let record = TypedValue::new(
            source(Type::UnboxedRecord(vec![(field_name, source_function)])),
            TypedValueKind::UnboxedRecord(vec![(field_name, captured_thunk("record_capture"))]),
        );
        let record_function = function("record", vec![record_capture], ret(record));
        let input = TypedCore::new(vec![tuple_function, record_function]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new()).erase();

        let Comp::Return(Value::UnboxedTuple(tuple_fields)) = &actual.fns[0].body else {
            panic!("expected unboxed tuple return");
        };
        let Value::Thunk(tuple_closure) = &tuple_fields[0] else {
            panic!("expected tuple thunk");
        };
        let Comp::Lam(_, tuple_body) = &**tuple_closure else {
            panic!("expected tuple closure");
        };
        let tuple_rest = head_dup(tuple_body, "tuple_capture");
        assert!(matches!(
            tuple_rest,
            Comp::Return(Value::Var(name)) if *name == sym("tuple_capture")
        ));

        let Comp::Return(Value::UnboxedRecord(record_fields)) = &actual.fns[1].body else {
            panic!("expected unboxed record return");
        };
        let Value::Thunk(record_closure) = &record_fields[0].1 else {
            panic!("expected record thunk");
        };
        let Comp::Lam(_, record_body) = &**record_closure else {
            panic!("expected record closure");
        };
        let record_rest = head_dup(record_body, "record_capture");
        assert!(matches!(
            record_rest,
            Comp::Return(Value::Var(name)) if *name == sym("record_capture")
        ));
    }

    #[test]
    fn branches_and_refs_balance_on_every_path() {
        let int = source(Type::Int);
        let condition = TypedBinder::new(sym("condition"), source(Type::Bool));
        let cell_ty = CoreType::Ref(Box::new(int.clone()));
        let cell = TypedBinder::new(sym("cell"), cell_ty.clone());
        let get = || {
            TypedComp::new(
                pure(int.clone()),
                TypedCompKind::RefGet(var("cell", cell_ty.clone())),
            )
        };
        let body = TypedComp::new(
            pure(int.clone()),
            TypedCompKind::If(
                var("condition", source(Type::Bool)),
                Box::new(get()),
                Box::new(get()),
            ),
        );
        let input = TypedCore::new(vec![function("main", vec![condition, cell], body)]);
        assert_differential(&input, &Sigs::new(), &VerifyEnv::new());
    }

    #[test]
    fn pattern_arms_duplicate_live_fields_before_dropping_the_scrutinee() {
        let int = source(Type::Int);
        let tuple_ty = source(Type::Tuple(vec![Type::Int]));
        let scrutinee = TypedBinder::new(sym("scrutinee"), tuple_ty.clone());
        let field = TypedBinder::new(sym("field"), int.clone());
        let body = TypedComp::new(
            pure(int.clone()),
            TypedCompKind::Case(
                var("scrutinee", tuple_ty),
                vec![(
                    TypedPattern::Tuple(vec![Some(field)]),
                    ret(var("field", int)),
                )],
            ),
        );
        let input = TypedCore::new(vec![function("main", vec![scrutinee], body)]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new()).erase();
        let Comp::Case(_, arms) = &actual.fns[0].body else {
            panic!("expected case after RC insertion");
        };
        let field_rest = head_dup(&arms[0].1, "field");
        let scrutinee_rest = head_drop(field_rest, "scrutinee");
        assert!(matches!(
            scrutinee_rest,
            Comp::Return(Value::Var(name)) if *name == sym("field")
        ));
    }

    #[test]
    fn init_at_consumes_the_cell_and_every_constructor_field() {
        let int = source(Type::Int);
        let tuple = source(Type::Tuple(vec![Type::Int, Type::Int]));
        let cell = TypedBinder::new(sym("cell"), int.clone());
        let field = TypedBinder::new(sym("field"), int.clone());
        let ctor = TypedValue::new(
            tuple.clone(),
            TypedValueKind::Tuple(vec![var("field", int.clone()), var("field", int.clone())]),
        );
        let body = TypedComp::new(
            pure(tuple),
            TypedCompKind::InitAt(var("cell", int.clone()), ctor),
        );
        let input = TypedCore::new(vec![function("main", vec![cell, field], body)]);
        let mut env = VerifyEnv::new();
        env.insert_operation(
            sym(ALLOC_OP),
            OperationSig::new(
                Vec::new(),
                vec![int.clone()],
                int,
                Label::bare(sym("Arena")),
            ),
        );
        let actual = assert_differential(&input, &Sigs::new(), &env).erase();
        let after_dup = head_dup(&actual.fns[0].body, "field");
        assert!(matches!(
            after_dup,
            Comp::InitAt(Value::Var(cell), Value::Tuple(fields))
                if *cell == sym("cell")
                    && matches!(
                        fields.as_slice(),
                        [Value::Var(lhs), Value::Var(rhs)]
                            if *lhs == sym("field") && *rhs == sym("field")
                    )
        ));
    }

    #[test]
    fn polymorphic_global_closures_share_one_verified_rc_operand_instance() {
        let id = sym("id");
        let parameter_type = sym("a");
        let generic = source(Type::Var(parameter_type));
        let parameter = TypedBinder::new(sym("value"), generic.clone());
        let id_body = ret(var("value", generic.clone()));
        let id_sig = CoreFnSig::new(
            vec![CoreQuantifier::Type(parameter_type)],
            vec![generic.clone()],
            pure(generic),
        );
        let id_function = TypedCoreFn::new(id, vec![parameter], id_body, id_sig, 0);

        let capture = |name: &str, ty: Type| {
            let instance = CoreFnSig::new(
                Vec::new(),
                vec![source(ty.clone())],
                pure(source(ty.clone())),
            );
            let global = TypedValue::new(
                CoreType::Function(Box::new(instance)),
                TypedValueKind::Var {
                    name: id,
                    instantiation: vec![CoreInstantiation::Type(ty)],
                },
            );
            let closure_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(global.ty.clone()));
            let closure = TypedComp::new(
                pure(CoreType::Function(Box::new(closure_sig))),
                TypedCompKind::Lam(Vec::new(), Box::new(ret(global))),
            );
            function(name, Vec::new(), closure)
        };
        let input = TypedCore::new(vec![
            id_function,
            capture("int_capture", Type::Int),
            capture("bool_capture", Type::Bool),
        ]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new());
        let int_instance = CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![source(Type::Int)],
            pure(source(Type::Int)),
        )));

        for function in &actual.fns[1..] {
            let TypedCompKind::Lam(_, body) = &function.body.kind else {
                panic!("expected captured global closure");
            };
            let TypedCompKind::Bind(dup, _, _) = &body.kind else {
                panic!("expected a capture dup");
            };
            let TypedCompKind::Dup(operand) = &dup.kind else {
                panic!("expected a typed dup operand");
            };
            assert_eq!(operand.ty, int_instance);
        }
    }

    #[test]
    fn a_shadowing_local_cannot_poison_a_later_global_capture_witness() {
        let global_name = sym("f");
        let int = source(Type::Int);
        let unit = source(Type::Unit);
        let global_sig = CoreFnSig::new(Vec::new(), vec![unit.clone()], pure(unit.clone()));

        let poison_param = TypedBinder::new(global_name, int.clone());
        let poison = function(
            "poison",
            vec![poison_param],
            ret(TypedValue::new(
                int,
                TypedValueKind::Var {
                    name: global_name,
                    instantiation: Vec::new(),
                },
            )),
        );
        let global_param = TypedBinder::new(sym("arg"), unit);
        let global = TypedCoreFn::new(
            global_name,
            vec![global_param.clone()],
            ret(binder_value(&global_param)),
            global_sig.clone(),
            0,
        );
        let global_value = TypedValue::new(
            CoreType::Function(Box::new(global_sig.clone())),
            TypedValueKind::Var {
                name: global_name,
                instantiation: Vec::new(),
            },
        );
        let capture_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(global_value.ty.clone()));
        let capture = function(
            "capture",
            Vec::new(),
            TypedComp::new(
                pure(CoreType::Function(Box::new(capture_sig))),
                TypedCompKind::Lam(Vec::new(), Box::new(ret(global_value))),
            ),
        );
        let input = TypedCore::new(vec![poison, global, capture]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new());
        let TypedCompKind::Lam(_, body) = &actual.fns[2].body.kind else {
            panic!("expected global-capturing closure");
        };
        let TypedCompKind::Bind(dup, _, _) = &body.kind else {
            panic!("expected capture dup");
        };
        let TypedCompKind::Dup(operand) = &dup.kind else {
            panic!("expected typed dup operand");
        };
        assert_eq!(
            operand.ty,
            CoreType::Function(Box::new(global_sig)),
            "the earlier local f:Int must not replace the global f witness"
        );
    }

    #[test]
    fn insertion_order_is_name_stable() {
        let int = source(Type::Int);
        let zulu = TypedBinder::new(sym("zulu"), int.clone());
        let alpha = TypedBinder::new(sym("alpha"), int);
        let unit = TypedValue::new(source(Type::Unit), TypedValueKind::Unit);
        let input = TypedCore::new(vec![function("main", vec![zulu, alpha], ret(unit))]);
        let actual = assert_differential(&input, &Sigs::new(), &VerifyEnv::new()).erase();
        let rendered = crate::core::pp_core(&actual);
        let alpha_at = rendered.find("drop alpha").expect("alpha drop");
        let zulu_at = rendered.find("drop zulu").expect("zulu drop");
        assert!(
            zulu_at < alpha_at,
            "outer wrapping must match the legacy pass"
        );
    }
}
