//! Pure erased-Core shape facts shared by Core construction and typed lowering.
//!
//! The functions here classify handler resumptions and state-fold clauses. They
//! never rewrite a program or select a lowering strategy.

use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{Comp, HandleOp, Value};
use super::fv;
use crate::sym::Sym;

/// How one handler clause uses its resumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ResumeUse {
    /// The only use is one tail `resume(value)`.
    pub(crate) tail: bool,
    /// The resumption escapes or may be called more than once.
    pub(crate) multishot: bool,
    /// The resumption occurs free inside a thunk.
    pub(crate) in_thunk: bool,
}

/// Classify one clause. `CheckedHandler` is the sole durable owner of this
/// derived fact and recomputes it whenever a handler is rebuilt.
pub(crate) fn classify_resume(op: &HandleOp) -> ResumeUse {
    let aliases = resume_set(op.resume);
    let tail = strip_resume(&op.body, &aliases).is_some();

    let mut body = &op.body;
    loop {
        match body {
            Comp::Lam(_, inner) => body = inner,
            Comp::Return(Value::Thunk(thunk)) => match thunk.as_ref() {
                Comp::Lam(_, inner) => body = inner,
                _ => break,
            },
            _ => break,
        }
    }

    let mut calls = 0usize;
    let mut escapes = false;
    scan_resume(body, &aliases, &mut calls, &mut escapes);
    ResumeUse {
        tail,
        multishot: escapes || calls > 1,
        in_thunk: resume_in_thunk(&op.body, op.resume),
    }
}

fn scan_resume(comp: &Comp, aliases: &BTreeSet<Sym>, calls: &mut usize, escapes: &mut bool) {
    match comp {
        Comp::Force(Value::Var(name)) if aliases.contains(name) => {
            *calls += 1;
            return;
        }
        Comp::Bind(bound, binder, body) => {
            if let Comp::Return(Value::Var(name)) = bound.as_ref() {
                if aliases.contains(name) {
                    let mut inner = aliases.clone();
                    inner.insert(*binder);
                    scan_resume(body, &inner, calls, escapes);
                    return;
                }
            }
            scan_resume(bound, aliases, calls, escapes);
            if aliases.contains(binder) {
                let mut inner = aliases.clone();
                inner.remove(binder);
                scan_resume(body, &inner, calls, escapes);
            } else {
                scan_resume(body, aliases, calls, escapes);
            }
            return;
        }
        _ => {}
    }
    each_value(comp, &mut |value| {
        if aliases.iter().any(|alias| value_uses(value, *alias) > 0) {
            *escapes = true;
        }
    });
    each_subcomp(comp, &mut |child| {
        scan_resume(child, aliases, calls, escapes);
    });
}

fn resume_in_thunk(comp: &Comp, resume: Sym) -> bool {
    let mut found = false;
    each_value(comp, &mut |value| {
        let mut thunks = Vec::new();
        thunks_in_value(value, &mut thunks);
        for thunk in thunks {
            found |= fv::comp(thunk).contains(&resume);
        }
    });
    each_subcomp(comp, &mut |child| {
        found |= resume_in_thunk(child, resume);
    });
    found
}

fn value_uses(value: &Value, name: Sym) -> usize {
    match value {
        Value::Var(found) => usize::from(*found == name),
        Value::Thunk(comp) => comp_uses(comp, name),
        Value::Ctor(_, _, fields) | Value::Tuple(fields) => {
            fields.iter().map(|field| value_uses(field, name)).sum()
        }
        _ => 0,
    }
}

fn comp_uses(comp: &Comp, name: Sym) -> usize {
    let mut uses = 0;
    each_value(comp, &mut |value| uses += value_uses(value, name));
    each_subcomp(comp, &mut |child| uses += comp_uses(child, name));
    uses
}

fn strip_resume(comp: &Comp, aliases: &BTreeSet<Sym>) -> Option<Comp> {
    let stripped = strip_resume_go(comp, aliases)?;
    fv::comp(&stripped).is_disjoint(aliases).then_some(stripped)
}

fn strip_resume_go(comp: &Comp, aliases: &BTreeSet<Sym>) -> Option<Comp> {
    match comp {
        Comp::App(function, args)
            if matches!(
                function.as_ref(),
                Comp::Force(Value::Var(name)) if aliases.contains(name)
            ) =>
        {
            let [argument] = args.as_slice() else {
                return None;
            };
            fv::value(argument)
                .is_disjoint(aliases)
                .then(|| Comp::Return(argument.clone()))
        }
        Comp::Bind(bound, binder, body) => {
            if let Comp::Return(Value::Var(name)) = bound.as_ref() {
                if aliases.contains(name) {
                    let mut inner = aliases.clone();
                    inner.insert(*binder);
                    return strip_resume(body, &inner);
                }
            }
            if !fv::comp(bound).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Bind(
                bound.clone(),
                *binder,
                Box::new(strip_resume(body, aliases)?),
            ))
        }
        Comp::If(value, then_branch, else_branch) => {
            if !fv::value(value).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::If(
                value.clone(),
                Box::new(strip_resume(then_branch, aliases)?),
                Box::new(strip_resume(else_branch, aliases)?),
            ))
        }
        Comp::Case(value, arms) => {
            if !fv::value(value).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Case(
                value.clone(),
                arms.iter()
                    .map(|(pattern, body)| Some((pattern.clone(), strip_resume(body, aliases)?)))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        _ => None,
    }
}

/// The resume argument shape accepted by state fusion.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum FoldAKind {
    Unit,
    Acc,
}

/// Whether a forwarding handler has the identity return clause.
pub(crate) fn is_id_return(return_var: Option<Sym>, return_body: Option<&Comp>) -> bool {
    matches!(
        (return_var, return_body),
        (Some(expected), Some(Comp::Return(Value::Var(actual)))) if *actual == expected
    )
}

/// Whether a fold has the identity state-transformer return clause.
pub(crate) fn is_id_transformer(return_body: &Comp) -> bool {
    matches!(return_body, Comp::Return(Value::Thunk(thunk))
        if matches!(thunk.as_ref(), Comp::Lam(params, body)
            if params.len() == 1
                && matches!(body.as_ref(), Comp::Return(Value::Var(value))
                    if value == &params[0])))
}

/// Whether a return clause is a one-parameter state transformer.
pub(crate) fn is_state_transformer(return_body: &Comp) -> bool {
    matches!(return_body, Comp::Return(Value::Thunk(thunk))
        if matches!(thunk.as_ref(), Comp::Lam(params, _) if params.len() == 1))
}

/// Classify a parameter-passing fold clause.
pub(crate) fn is_fold(op: &HandleOp, resume: ResumeUse) -> Option<FoldAKind> {
    if resume.tail {
        return None;
    }
    let Comp::Return(Value::Thunk(thunk)) = &op.body else {
        return None;
    };
    let Comp::Lam(params, body) = thunk.as_ref() else {
        return None;
    };
    let [accumulator] = params.as_slice() else {
        return None;
    };
    strip_state(body, &resume_set(op.resume), *accumulator).map(|(_, kind)| kind)
}

fn resume_set(resume: Sym) -> BTreeSet<Sym> {
    BTreeSet::from([resume])
}

fn fold_argument(value: &Value, accumulator: Sym) -> Option<FoldAKind> {
    match value {
        Value::Unit => Some(FoldAKind::Unit),
        Value::Var(name) if *name == accumulator => Some(FoldAKind::Acc),
        _ => None,
    }
}

fn strip_state(
    comp: &Comp,
    aliases: &BTreeSet<Sym>,
    accumulator: Sym,
) -> Option<(Comp, FoldAKind)> {
    strip_state_go(comp, aliases, accumulator, &BTreeMap::new())
}

fn strip_state_go(
    comp: &Comp,
    aliases: &BTreeSet<Sym>,
    accumulator: Sym,
    substitutions: &BTreeMap<Sym, Value>,
) -> Option<(Comp, FoldAKind)> {
    match comp {
        Comp::Bind(bound, binder, body) => {
            if let Comp::Return(Value::Var(name)) = bound.as_ref() {
                if aliases.contains(name) {
                    let mut inner = aliases.clone();
                    inner.insert(*binder);
                    return strip_state_go(body, &inner, accumulator, substitutions);
                }
            }
            if let Some(argument) = resume_argument(bound, aliases, substitutions) {
                let kind = fold_argument(&argument, accumulator)?;
                let Comp::App(function, args) = body.as_ref() else {
                    return None;
                };
                if !matches!(
                    function.as_ref(),
                    Comp::Force(Value::Var(name)) if name == binder
                ) {
                    return None;
                }
                let [state] = args.as_slice() else {
                    return None;
                };
                if !fv::value(state).is_disjoint(aliases) {
                    return None;
                }
                return Some((Comp::Return(state.clone()), kind));
            }
            if !fv::comp(bound).is_disjoint(aliases) {
                return None;
            }
            let mut inner = substitutions.clone();
            if let Comp::Return(value) = bound.as_ref() {
                inner.insert(*binder, value.clone());
            }
            let (tail, kind) = strip_state_go(body, aliases, accumulator, &inner)?;
            Some((Comp::Bind(bound.clone(), *binder, Box::new(tail)), kind))
        }
        Comp::If(value, then_branch, else_branch) => {
            if !fv::value(value).is_disjoint(aliases) {
                return None;
            }
            let (then_branch, then_kind) =
                strip_state_go(then_branch, aliases, accumulator, substitutions)?;
            let (else_branch, else_kind) =
                strip_state_go(else_branch, aliases, accumulator, substitutions)?;
            (then_kind == else_kind).then(|| {
                (
                    Comp::If(value.clone(), Box::new(then_branch), Box::new(else_branch)),
                    then_kind,
                )
            })
        }
        Comp::Case(value, arms) => {
            if !fv::value(value).is_disjoint(aliases) {
                return None;
            }
            let mut expected = None;
            let mut lowered = Vec::with_capacity(arms.len());
            for (pattern, body) in arms {
                let (body, kind) = strip_state_go(body, aliases, accumulator, substitutions)?;
                match expected {
                    Some(previous) if previous != kind => return None,
                    _ => expected = Some(kind),
                }
                lowered.push((pattern.clone(), body));
            }
            Some((Comp::Case(value.clone(), lowered), expected?))
        }
        _ => None,
    }
}

fn resume_argument(
    comp: &Comp,
    aliases: &BTreeSet<Sym>,
    substitutions: &BTreeMap<Sym, Value>,
) -> Option<Value> {
    match comp {
        Comp::App(function, args) => {
            if !matches!(
                function.as_ref(),
                Comp::Force(Value::Var(name)) if aliases.contains(name)
            ) {
                return None;
            }
            let [argument] = args.as_slice() else {
                return None;
            };
            fv::value(argument)
                .is_disjoint(aliases)
                .then(|| resolve_value(argument, substitutions))
        }
        Comp::Bind(bound, binder, body) => {
            if let Comp::Return(Value::Var(name)) = bound.as_ref() {
                if aliases.contains(name) {
                    let mut inner = aliases.clone();
                    inner.insert(*binder);
                    return resume_argument(body, &inner, substitutions);
                }
            }
            if !fv::comp(bound).is_disjoint(aliases) {
                return None;
            }
            let mut inner = substitutions.clone();
            if let Comp::Return(value) = bound.as_ref() {
                inner.insert(*binder, value.clone());
            }
            resume_argument(body, aliases, &inner)
        }
        _ => None,
    }
}

fn resolve_value(value: &Value, substitutions: &BTreeMap<Sym, Value>) -> Value {
    match value {
        Value::Var(name) => substitutions.get(name).map_or_else(
            || value.clone(),
            |inner| resolve_value(inner, substitutions),
        ),
        _ => value.clone(),
    }
}

fn thunks_in_value<'a>(value: &'a Value, thunks: &mut Vec<&'a Comp>) {
    match value {
        Value::Thunk(comp) => thunks.push(comp),
        Value::Ctor(_, _, fields) | Value::Tuple(fields) => {
            for field in fields {
                thunks_in_value(field, thunks);
            }
        }
        _ => {}
    }
}

fn each_value<'a>(comp: &'a Comp, visit: &mut impl FnMut(&'a Value)) {
    match comp {
        Comp::Return(value)
        | Comp::Force(value)
        | Comp::Error(value)
        | Comp::FloatBuiltin(_, value)
        | Comp::Neg(_, value)
        | Comp::Dup(value)
        | Comp::Drop(value)
        | Comp::WithReuse { freed: value, .. }
        | Comp::Reuse(_, value)
        | Comp::RefNew(value)
        | Comp::RefGet(value)
        | Comp::UnboxedProject(value, _)
        | Comp::If(value, ..)
        | Comp::Case(value, _) => visit(value),
        Comp::Prim(_, left, right) | Comp::RefSet(left, right) | Comp::InitAt(left, right) => {
            visit(left);
            visit(right);
        }
        Comp::App(_, args)
        | Comp::Call(_, args)
        | Comp::Do(_, args)
        | Comp::StrBuiltin(_, args)
        | Comp::Io(_, args) => {
            for argument in args {
                visit(argument);
            }
        }
        Comp::Bind(..) | Comp::Lam(..) | Comp::Mask(..) | Comp::Handle { .. } => {}
    }
}

fn each_subcomp<'a>(comp: &'a Comp, visit: &mut impl FnMut(&'a Comp)) {
    match comp {
        Comp::Bind(bound, _, body) => {
            visit(bound);
            visit(body);
        }
        Comp::Lam(_, body) | Comp::Mask(_, body) | Comp::WithReuse { body, .. } => visit(body),
        Comp::App(function, _) => visit(function),
        Comp::If(_, then_branch, else_branch) => {
            visit(then_branch);
            visit(else_branch);
        }
        Comp::Case(_, arms) => {
            for (_, body) in arms {
                visit(body);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            visit(body);
            if let Some(return_body) = return_body {
                visit(return_body);
            }
            for op in ops {
                visit(&op.body);
            }
        }
        Comp::Return(_)
        | Comp::Force(_)
        | Comp::Error(_)
        | Comp::FloatBuiltin(..)
        | Comp::Neg(..)
        | Comp::UnboxedProject(..)
        | Comp::Dup(_)
        | Comp::Drop(_)
        | Comp::Reuse(..)
        | Comp::InitAt(..)
        | Comp::RefNew(_)
        | Comp::RefGet(_)
        | Comp::RefSet(..)
        | Comp::Prim(..)
        | Comp::Call(..)
        | Comp::Do(..)
        | Comp::StrBuiltin(..)
        | Comp::Io(..) => {}
    }
}
