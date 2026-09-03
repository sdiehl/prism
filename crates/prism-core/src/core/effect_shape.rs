//! Pure erased-Core shape facts shared by Core construction and typed lowering.
//!
//! The functions here classify handler resumptions and state-fold clauses. They
//! never rewrite a program or select a lowering strategy.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use prism_common::sym::Sym;

use crate::core::cbpv::{Comp, HandleOp, Value};
use crate::core::fv;

/// How one handler clause uses its resumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResumeUse {
    /// The only use is one tail `resume(value)`.
    pub tail: bool,
    /// The resumption escapes or may be called more than once.
    pub multishot: bool,
    /// The resumption occurs free inside a thunk.
    pub in_thunk: bool,
}

/// Classify one clause. `CheckedHandler` is the sole durable owner of this
/// derived fact and recomputes it whenever a handler is rebuilt.
#[must_use]
pub fn classify_resume(op: &HandleOp) -> ResumeUse {
    let aliases = Rc::new(resume_set(op.resume));
    let tail = tail_resumptive(&op.body, &aliases);

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

    let (calls, escapes) = scan_resume(body, &aliases);
    ResumeUse {
        tail,
        multishot: escapes || calls > 1,
        in_thunk: resume_in_thunk(&op.body, op.resume),
    }
}

struct ResumeFrame<'a> {
    comp: &'a Comp,
    aliases: Rc<BTreeSet<Sym>>,
}

fn scan_resume(comp: &Comp, aliases: &Rc<BTreeSet<Sym>>) -> (usize, bool) {
    let mut frames = vec![ResumeFrame {
        comp,
        aliases: Rc::clone(aliases),
    }];
    let mut calls = 0usize;
    let mut escapes = false;
    while let Some(ResumeFrame { comp, aliases }) = frames.pop() {
        match comp {
            Comp::Force(Value::Var(name)) if aliases.contains(name) => {
                calls += 1;
                continue;
            }
            Comp::Bind(bound, binder, body) => {
                if matches!(bound.as_ref(), Comp::Return(Value::Var(name))
                    if aliases.contains(name))
                {
                    let mut inner = aliases.as_ref().clone();
                    inner.insert(*binder);
                    frames.push(ResumeFrame {
                        comp: body,
                        aliases: Rc::new(inner),
                    });
                    continue;
                }

                let body_aliases = if aliases.contains(binder) {
                    let mut inner = aliases.as_ref().clone();
                    inner.remove(binder);
                    Rc::new(inner)
                } else {
                    Rc::clone(&aliases)
                };
                frames.push(ResumeFrame {
                    comp: body,
                    aliases: body_aliases,
                });
                frames.push(ResumeFrame {
                    comp: bound,
                    aliases,
                });
                continue;
            }
            _ => {}
        }

        each_value(comp, &mut |value| {
            escapes |= value_uses_alias(value, &aliases);
        });
        each_subcomp(comp, &mut |child| {
            frames.push(ResumeFrame {
                comp: child,
                aliases: Rc::clone(&aliases),
            });
        });
    }
    (calls, escapes)
}

enum UseNode<'a> {
    Comp(&'a Comp),
    Value(&'a Value),
}

fn value_uses_alias(value: &Value, aliases: &BTreeSet<Sym>) -> bool {
    let mut nodes = vec![UseNode::Value(value)];
    while let Some(node) = nodes.pop() {
        match node {
            UseNode::Comp(comp) => {
                each_value(comp, &mut |value| nodes.push(UseNode::Value(value)));
                each_subcomp(comp, &mut |child| nodes.push(UseNode::Comp(child)));
            }
            UseNode::Value(Value::Var(name)) if aliases.contains(name) => return true,
            UseNode::Value(Value::Thunk(comp)) => nodes.push(UseNode::Comp(comp)),
            UseNode::Value(
                Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields),
            ) => {
                for field in fields {
                    nodes.push(UseNode::Value(field));
                }
            }
            UseNode::Value(Value::UnboxedRecord(fields)) => {
                for (_, field) in fields {
                    nodes.push(UseNode::Value(field));
                }
            }
            UseNode::Value(_) => {}
        }
    }
    false
}

fn resume_in_thunk(comp: &Comp, resume: Sym) -> bool {
    let mut comps = vec![comp];
    let mut thunks = Vec::new();
    while let Some(comp) = comps.pop() {
        each_value(comp, &mut |value| thunks_in_value(value, &mut thunks));
        if thunks
            .iter()
            .copied()
            .any(|thunk| fv::comp(thunk).contains(&resume))
        {
            return true;
        }
        thunks.clear();
        each_subcomp(comp, &mut |child| comps.push(child));
    }
    false
}

fn tail_resumptive(comp: &Comp, aliases: &Rc<BTreeSet<Sym>>) -> bool {
    let mut frames = vec![ResumeFrame {
        comp,
        aliases: Rc::clone(aliases),
    }];
    while let Some(ResumeFrame { comp, aliases }) = frames.pop() {
        match comp {
            Comp::App(function, args)
                if matches!(function.as_ref(), Comp::Force(Value::Var(name))
                    if aliases.contains(name)) =>
            {
                let [argument] = args.as_slice() else {
                    return false;
                };
                if !fv::value(argument).is_disjoint(&aliases) {
                    return false;
                }
            }
            Comp::Bind(bound, binder, body) => {
                if matches!(bound.as_ref(), Comp::Return(Value::Var(name))
                    if aliases.contains(name))
                {
                    let mut inner = aliases.as_ref().clone();
                    inner.insert(*binder);
                    frames.push(ResumeFrame {
                        comp: body,
                        aliases: Rc::new(inner),
                    });
                } else {
                    if !fv::comp(bound).is_disjoint(&aliases) {
                        return false;
                    }
                    frames.push(ResumeFrame {
                        comp: body,
                        aliases,
                    });
                }
            }
            Comp::If(value, then_branch, else_branch) => {
                if !fv::value(value).is_disjoint(&aliases) {
                    return false;
                }
                frames.push(ResumeFrame {
                    comp: else_branch,
                    aliases: Rc::clone(&aliases),
                });
                frames.push(ResumeFrame {
                    comp: then_branch,
                    aliases,
                });
            }
            Comp::Case(value, arms) => {
                if !fv::value(value).is_disjoint(&aliases) {
                    return false;
                }
                for (_, body) in arms.iter().rev() {
                    frames.push(ResumeFrame {
                        comp: body,
                        aliases: Rc::clone(&aliases),
                    });
                }
            }
            _ => return false,
        }
    }
    true
}

/// The resume argument shape accepted by state fusion.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FoldAKind {
    Unit,
    Acc,
}

/// Whether a forwarding handler has the identity return clause.
#[must_use]
pub fn is_id_return(return_var: Option<Sym>, return_body: Option<&Comp>) -> bool {
    matches!(
        (return_var, return_body),
        (Some(expected), Some(Comp::Return(Value::Var(actual)))) if *actual == expected
    )
}

/// Whether a fold has the identity state-transformer return clause.
#[must_use]
pub fn is_id_transformer(return_body: &Comp) -> bool {
    matches!(return_body, Comp::Return(Value::Thunk(thunk))
        if matches!(thunk.as_ref(), Comp::Lam(params, body)
            if params.len() == 1
                && matches!(body.as_ref(), Comp::Return(Value::Var(value))
                    if value == &params[0])))
}

/// Whether a return clause is a one-parameter state transformer.
#[must_use]
pub fn is_state_transformer(return_body: &Comp) -> bool {
    matches!(return_body, Comp::Return(Value::Thunk(thunk))
        if matches!(thunk.as_ref(), Comp::Lam(params, _) if params.len() == 1))
}

/// Classify a parameter-passing fold clause.
#[must_use]
pub fn is_fold(op: &HandleOp, resume: ResumeUse) -> Option<FoldAKind> {
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
    fold_kind(body, Rc::new(resume_set(op.resume)), *accumulator)
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

type Substitutions<'a> = BTreeMap<Sym, &'a Value>;

enum FoldFrame<'a> {
    Comp {
        comp: &'a Comp,
        aliases: Rc<BTreeSet<Sym>>,
        substitutions: Rc<Substitutions<'a>>,
    },
    Join {
        mark: usize,
        branches: usize,
    },
}

fn fold_kind(comp: &Comp, aliases: Rc<BTreeSet<Sym>>, accumulator: Sym) -> Option<FoldAKind> {
    let mut frames = vec![FoldFrame::Comp {
        comp,
        aliases,
        substitutions: Rc::new(BTreeMap::new()),
    }];
    let mut kinds = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            FoldFrame::Comp {
                comp,
                aliases,
                substitutions,
            } => match comp {
                Comp::Bind(bound, binder, body) => {
                    if matches!(bound.as_ref(), Comp::Return(Value::Var(name))
                        if aliases.contains(name))
                    {
                        let mut inner = aliases.as_ref().clone();
                        inner.insert(*binder);
                        frames.push(FoldFrame::Comp {
                            comp: body,
                            aliases: Rc::new(inner),
                            substitutions,
                        });
                        continue;
                    }

                    if let Some(kind) =
                        resume_argument_kind(bound, &aliases, &substitutions, accumulator)
                    {
                        let Comp::App(function, args) = body.as_ref() else {
                            return None;
                        };
                        if !matches!(function.as_ref(), Comp::Force(Value::Var(name))
                            if name == binder)
                        {
                            return None;
                        }
                        let [state] = args.as_slice() else {
                            return None;
                        };
                        if !fv::value(state).is_disjoint(&aliases) {
                            return None;
                        }
                        kinds.push(kind);
                        continue;
                    }

                    if !fv::comp(bound).is_disjoint(&aliases) {
                        return None;
                    }
                    let substitutions = if let Comp::Return(value) = bound.as_ref() {
                        let mut inner = substitutions.as_ref().clone();
                        inner.insert(*binder, value);
                        Rc::new(inner)
                    } else {
                        substitutions
                    };
                    frames.push(FoldFrame::Comp {
                        comp: body,
                        aliases,
                        substitutions,
                    });
                }
                Comp::If(value, then_branch, else_branch) => {
                    if !fv::value(value).is_disjoint(&aliases) {
                        return None;
                    }
                    let mark = kinds.len();
                    frames.push(FoldFrame::Join { mark, branches: 2 });
                    frames.push(FoldFrame::Comp {
                        comp: else_branch,
                        aliases: Rc::clone(&aliases),
                        substitutions: Rc::clone(&substitutions),
                    });
                    frames.push(FoldFrame::Comp {
                        comp: then_branch,
                        aliases,
                        substitutions,
                    });
                }
                Comp::Case(value, arms) => {
                    if arms.is_empty() || !fv::value(value).is_disjoint(&aliases) {
                        return None;
                    }
                    let mark = kinds.len();
                    frames.push(FoldFrame::Join {
                        mark,
                        branches: arms.len(),
                    });
                    for (_, body) in arms.iter().rev() {
                        frames.push(FoldFrame::Comp {
                            comp: body,
                            aliases: Rc::clone(&aliases),
                            substitutions: Rc::clone(&substitutions),
                        });
                    }
                }
                _ => return None,
            },
            FoldFrame::Join { mark, branches } => {
                assert_eq!(
                    kinds.len(),
                    mark + branches,
                    "each fold branch produces one kind"
                );
                let expected = kinds[mark];
                if kinds[mark..].iter().any(|kind| *kind != expected) {
                    return None;
                }
                kinds.truncate(mark);
                kinds.push(expected);
            }
        }
    }
    let [kind] = kinds.as_slice() else {
        return None;
    };
    Some(*kind)
}

fn resume_argument_kind<'a>(
    mut comp: &'a Comp,
    initial_aliases: &Rc<BTreeSet<Sym>>,
    initial_substitutions: &Rc<Substitutions<'a>>,
    accumulator: Sym,
) -> Option<FoldAKind> {
    let mut aliases = Rc::clone(initial_aliases);
    let mut substitutions = Rc::clone(initial_substitutions);
    loop {
        match comp {
            Comp::App(function, args) => {
                if !matches!(function.as_ref(), Comp::Force(Value::Var(name))
                    if aliases.contains(name))
                {
                    return None;
                }
                let [argument] = args.as_slice() else {
                    return None;
                };
                if !fv::value(argument).is_disjoint(&aliases) {
                    return None;
                }
                return resolve_fold_argument(argument, &substitutions, accumulator);
            }
            Comp::Bind(bound, binder, body) => {
                if matches!(bound.as_ref(), Comp::Return(Value::Var(name))
                    if aliases.contains(name))
                {
                    let mut inner = aliases.as_ref().clone();
                    inner.insert(*binder);
                    aliases = Rc::new(inner);
                    comp = body;
                    continue;
                }
                if !fv::comp(bound).is_disjoint(&aliases) {
                    return None;
                }
                if let Comp::Return(value) = bound.as_ref() {
                    let mut inner = substitutions.as_ref().clone();
                    inner.insert(*binder, value);
                    substitutions = Rc::new(inner);
                }
                comp = body;
            }
            _ => return None,
        }
    }
}

fn resolve_fold_argument<'a>(
    mut value: &'a Value,
    substitutions: &Substitutions<'a>,
    accumulator: Sym,
) -> Option<FoldAKind> {
    let mut seen = BTreeSet::new();
    while let Value::Var(name) = value {
        let Some(inner) = substitutions.get(name) else {
            break;
        };
        if !seen.insert(*name) {
            return None;
        }
        value = inner;
    }
    fold_argument(value, accumulator)
}

fn thunks_in_value<'a>(value: &'a Value, thunks: &mut Vec<&'a Comp>) {
    let mut values = vec![value];
    while let Some(value) = values.pop() {
        match value {
            Value::Thunk(comp) => thunks.push(comp),
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                for field in fields {
                    values.push(field);
                }
            }
            Value::UnboxedRecord(fields) => {
                for (_, field) in fields {
                    values.push(field);
                }
            }
            _ => {}
        }
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

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;
    use crate::core::CorePat;

    const DEEP_COMP_COUNT: usize = 25_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn mixed_path(mut body: Comp) -> Comp {
        let ignored = Sym::new("ignored");
        for depth in 0..DEEP_COMP_COUNT {
            if depth % 2 == 0 {
                let suspended = Value::Thunk(Box::new(Comp::Return(Value::Int(0))));
                body = Comp::Bind(
                    Box::new(Comp::Return(Value::Tuple(vec![suspended]))),
                    ignored,
                    Box::new(body),
                );
            } else {
                body = Comp::Case(Value::Unit, vec![(CorePat::Wild, body)]);
            }
        }
        body
    }

    fn mixed_value(mut value: Value) -> Value {
        let constructor = Sym::new("Deep.Value");
        let field = Sym::new("field");
        for depth in 0..DEEP_COMP_COUNT {
            value = match depth % 4 {
                0 => Value::Tuple(vec![value]),
                1 => Value::Ctor(constructor, 0, vec![value]),
                2 => Value::UnboxedTuple(vec![value]),
                _ => Value::UnboxedRecord(vec![(field, value)]),
            };
        }
        value
    }

    fn resume_call(resume: Sym, argument: Value) -> Comp {
        Comp::App(Box::new(Comp::Force(Value::Var(resume))), vec![argument])
    }

    fn fold_path(resume: Sym, accumulator: Sym) -> Comp {
        let state_alias = Sym::new("state_alias");
        let continuation = Sym::new("continuation");
        let tail = Comp::Bind(
            Box::new(resume_call(resume, Value::Var(state_alias))),
            continuation,
            Box::new(Comp::App(
                Box::new(Comp::Force(Value::Var(continuation))),
                vec![Value::Int(0)],
            )),
        );
        mixed_path(Comp::Bind(
            Box::new(Comp::Return(Value::Var(accumulator))),
            state_alias,
            Box::new(tail),
        ))
    }

    #[test]
    fn resume_classification_handles_deep_mixed_paths_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-resume-classification".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let resume = Sym::new("resume");
                let body = Comp::If(
                    Value::Bool(true),
                    Box::new(mixed_path(resume_call(
                        resume,
                        mixed_value(Value::Thunk(Box::new(Comp::Return(Value::Int(0))))),
                    ))),
                    Box::new(mixed_path(resume_call(
                        resume,
                        mixed_value(Value::Thunk(Box::new(Comp::Return(Value::Int(1))))),
                    ))),
                );
                let op = HandleOp {
                    name: Sym::new("Deep.resume"),
                    params: Vec::new(),
                    resume,
                    body,
                };

                assert_eq!(
                    classify_resume(&op),
                    ResumeUse {
                        tail: true,
                        multishot: true,
                        in_thunk: false,
                    }
                );
                mem::forget(op);
            })
            .expect("spawn deep resume-classification test")
            .join()
            .expect("deep resume-classification test panicked");
    }

    #[test]
    fn unboxed_products_do_not_hide_resumptions() {
        let resume = Sym::new("resume");
        let captured = Value::Thunk(Box::new(Comp::Return(Value::Var(resume))));
        let op = HandleOp {
            name: Sym::new("Unboxed.resume"),
            params: Vec::new(),
            resume,
            body: Comp::Return(Value::UnboxedRecord(vec![
                (
                    Sym::new("escaped"),
                    Value::UnboxedTuple(vec![Value::Var(resume)]),
                ),
                (Sym::new("captured"), captured),
            ])),
        };

        assert_eq!(
            classify_resume(&op),
            ResumeUse {
                tail: false,
                multishot: true,
                in_thunk: true,
            }
        );
    }

    #[test]
    fn fold_classification_handles_deep_mixed_paths_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-fold-classification".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let resume = Sym::new("resume");
                let accumulator = Sym::new("accumulator");
                let body = Comp::If(
                    Value::Bool(true),
                    Box::new(fold_path(resume, accumulator)),
                    Box::new(fold_path(resume, accumulator)),
                );
                let op = HandleOp {
                    name: Sym::new("Deep.fold"),
                    params: Vec::new(),
                    resume,
                    body: Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                        vec![accumulator],
                        Box::new(body),
                    )))),
                };

                assert_eq!(
                    is_fold(
                        &op,
                        ResumeUse {
                            tail: false,
                            multishot: false,
                            in_thunk: false,
                        }
                    ),
                    Some(FoldAKind::Acc)
                );
                mem::forget(op);
            })
            .expect("spawn deep fold-classification test")
            .join()
            .expect("deep fold-classification test panicked");
    }
}
