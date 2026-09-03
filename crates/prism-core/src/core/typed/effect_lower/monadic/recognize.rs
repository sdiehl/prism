//! Recognition judgments for resumptions and state-shaped answers.

use super::{
    free_comp_vars, free_value_vars, BTreeSet, Sym, TypedBinder, TypedComp, TypedCompKind,
    TypedHandleOp, TypedValue, TypedValueKind,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ResumeRepresentation {
    Continuation,
    Queue,
}

#[derive(Clone)]
pub(super) struct StateClause {
    pub(super) state: TypedBinder,
    pub(super) prefix: Vec<(TypedComp, TypedBinder)>,
    pub(super) resumed: TypedValue,
    pub(super) next_state: TypedValue,
}

pub(super) enum FnAnswerLowering {
    Declined,
    Lowered(Box<TypedComp>),
}

pub(super) fn forced_var(comp: &TypedComp) -> Option<Sym> {
    let TypedCompKind::Force(value) = comp.kind() else {
        return None;
    };
    let TypedValueKind::Var {
        name,
        instantiation,
    } = &value.kind
    else {
        return None;
    };
    instantiation.is_empty().then_some(*name)
}

/// The thunk a clause answers with, when its body has the parameter-passing
/// shape: a thunk over a lambda that the code around the handle applies once the
/// handle has returned. It is the one answer whose value is a computation rather
/// than a result, which is why the state path and the refusal below both ask for
/// it here rather than each re-reading the shape.
pub(super) fn answered_thunk(
    body: &TypedComp,
) -> Option<(&TypedValue, &[TypedBinder], &TypedComp)> {
    let TypedCompKind::Return(value) = body.kind() else {
        return None;
    };
    let TypedValueKind::Thunk(lambda) = &value.kind else {
        return None;
    };
    let TypedCompKind::Lam(parameters, body) = lambda.kind() else {
        return None;
    };
    Some((value, parameters, body))
}

/// [`answered_thunk`](answered_thunk) without the value, for the state path,
/// which asks about the transformer's shape and never about its convention.
pub(super) fn answered_lambda(body: &TypedComp) -> Option<(&[TypedBinder], &TypedComp)> {
    let (_, parameters, body) = answered_thunk(body)?;
    Some((parameters, body))
}

pub(super) fn state_return(return_body: Option<&TypedComp>) -> Option<(TypedBinder, TypedComp)> {
    let (parameters, body) = answered_lambda(return_body?)?;
    let [state] = parameters else {
        return None;
    };
    Some((state.clone(), body.clone()))
}

pub(super) fn state_apply_tail(comp: &TypedComp, result: Sym) -> Option<TypedValue> {
    let mut aliases = BTreeSet::from([result]);
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = forced_var(callee)?;
                let [argument] = args.as_slice() else {
                    return None;
                };
                return (instantiation.is_empty()
                    && aliases.contains(&callee)
                    && free_value_vars(argument).is_disjoint(&aliases))
                .then(|| argument.clone());
            }
            TypedCompKind::Bind(head, binder, tail) => {
                let TypedCompKind::Return(value) = head.kind() else {
                    return None;
                };
                let TypedValueKind::Var {
                    name,
                    instantiation,
                } = &value.kind
                else {
                    return None;
                };
                if !instantiation.is_empty() || !aliases.contains(name) {
                    return None;
                }
                aliases.insert(binder.name());
                current = tail;
            }
            _ => return None,
        }
    }
}

pub(super) fn resume_app(
    comp: &TypedComp,
    aliases: &BTreeSet<Sym>,
) -> Option<(Vec<(TypedComp, TypedBinder)>, TypedValue)> {
    let mut local = aliases.clone();
    let mut prefix = Vec::new();
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = forced_var(callee)?;
                let [argument] = args.as_slice() else {
                    return None;
                };
                return (instantiation.is_empty()
                    && local.contains(&callee)
                    && free_value_vars(argument).is_disjoint(&local))
                .then(|| (prefix, argument.clone()));
            }
            TypedCompKind::Bind(head, binder, tail) => {
                if let TypedCompKind::Return(value) = head.kind() {
                    if let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = &value.kind
                    {
                        if instantiation.is_empty() && local.contains(name) {
                            local.insert(binder.name());
                            current = tail;
                            continue;
                        }
                    }
                }
                if !matches!(
                    head.kind(),
                    TypedCompKind::Return(_) | TypedCompKind::Prim(..)
                ) || !free_comp_vars(head).is_disjoint(&local)
                {
                    return None;
                }
                prefix.push(((**head).clone(), binder.clone()));
                current = tail;
            }
            _ => return None,
        }
    }
}

pub(super) fn state_clause(operation: &TypedHandleOp) -> Option<StateClause> {
    let (parameters, body) = answered_lambda(operation.body())?;
    let [state] = parameters else {
        return None;
    };
    let mut aliases = BTreeSet::from([operation.resume().name()]);
    let mut prefix = Vec::new();
    let mut current = body;
    loop {
        let TypedCompKind::Bind(head, binder, tail) = current.kind() else {
            return None;
        };
        if let Some((resume_prefix, resumed)) = resume_app(head, &aliases) {
            let next_state = state_apply_tail(tail, binder.name())?;
            prefix.extend(resume_prefix);
            let escaped = !free_value_vars(&resumed).is_disjoint(&aliases)
                || !free_value_vars(&next_state).is_disjoint(&aliases)
                || prefix
                    .iter()
                    .any(|(head, _)| !free_comp_vars(head).is_disjoint(&aliases));
            if escaped {
                return None;
            }
            return Some(StateClause {
                state: state.clone(),
                prefix,
                resumed,
                next_state,
            });
        }
        if let TypedCompKind::Return(value) = head.kind() {
            if let TypedValueKind::Var {
                name,
                instantiation,
            } = &value.kind
            {
                if instantiation.is_empty() && aliases.contains(name) {
                    aliases.insert(binder.name());
                    current = tail;
                    continue;
                }
            }
        }
        if !matches!(
            head.kind(),
            TypedCompKind::Return(_) | TypedCompKind::Prim(..)
        ) || !free_comp_vars(head).is_disjoint(&aliases)
        {
            return None;
        }
        prefix.push(((**head).clone(), binder.clone()));
        current = tail;
    }
}

pub(super) fn function_applied_once_tail(comp: &TypedComp, function: Sym) -> bool {
    let mut aliases = BTreeSet::from([function]);
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let Some(callee) = forced_var(callee) else {
                    return false;
                };
                return instantiation.is_empty()
                    && aliases.contains(&callee)
                    && args.len() == 1
                    && free_value_vars(&args[0]).is_disjoint(&aliases);
            }
            TypedCompKind::Bind(head, binder, tail) => {
                if let TypedCompKind::Return(value) = head.kind() {
                    if let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = &value.kind
                    {
                        if instantiation.is_empty() && aliases.contains(name) {
                            aliases.insert(binder.name());
                            current = tail;
                            continue;
                        }
                    }
                }
                if !free_comp_vars(head).is_disjoint(&aliases) {
                    return false;
                }
                current = tail;
            }
            _ => return false,
        }
    }
}
