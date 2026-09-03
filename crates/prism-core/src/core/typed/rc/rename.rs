//! In-place alpha-renaming for case fields that shadow tracked references.

use std::{collections::BTreeMap, rc::Rc};

use prism_common::sym::Sym;

use super::super::verify::discard_core_instantiation;
use super::super::{TypedComp, TypedCompKind, TypedPattern, TypedValue, TypedValueKind};

type Renames = Rc<BTreeMap<Sym, Sym>>;

enum Node<'a> {
    Comp(&'a mut TypedComp, Renames),
    Value(&'a mut TypedValue, Renames),
}

pub(super) fn comp(comp: &mut TypedComp, renames: BTreeMap<Sym, Sym>) {
    let mut nodes = vec![Node::Comp(comp, Rc::new(renames))];
    while let Some(node) = nodes.pop() {
        match node {
            Node::Comp(comp, renames) => push_comp(&mut nodes, comp, renames),
            Node::Value(value, renames) => push_value(&mut nodes, value, renames),
        }
    }
}

fn scoped(renames: &Renames, binders: impl IntoIterator<Item = Sym>) -> Renames {
    let binders: Vec<Sym> = binders.into_iter().collect();
    if !binders.iter().any(|name| renames.contains_key(name)) {
        return Rc::clone(renames);
    }
    let mut inner = (**renames).clone();
    for name in binders {
        inner.remove(&name);
    }
    Rc::new(inner)
}

fn pattern_names(pattern: &TypedPattern) -> Vec<Sym> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.name],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().map(|binder| binder.name).collect()
        }
    }
}

fn push_comp<'a>(nodes: &mut Vec<Node<'a>>, comp: &'a mut TypedComp, renames: Renames) {
    match &mut comp.kind {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::Reuse(_, value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => nodes.push(Node::Value(value, renames)),
        TypedCompKind::Bind(first, binder, rest) => {
            nodes.push(Node::Comp(rest, scoped(&renames, [binder.name])));
            nodes.push(Node::Comp(first, renames));
        }
        TypedCompKind::Lam(params, body) => nodes.push(Node::Comp(
            body,
            scoped(&renames, params.iter().map(|binder| binder.name)),
        )),
        TypedCompKind::App { callee, args, .. } => {
            for argument in args.iter_mut().rev() {
                nodes.push(Node::Value(argument, Rc::clone(&renames)));
            }
            nodes.push(Node::Comp(callee, renames));
        }
        TypedCompKind::If(condition, yes, no) => {
            nodes.push(Node::Comp(no, Rc::clone(&renames)));
            nodes.push(Node::Comp(yes, Rc::clone(&renames)));
            nodes.push(Node::Value(condition, renames));
        }
        TypedCompKind::Prim(_, left, right)
        | TypedCompKind::RefSet(left, right)
        | TypedCompKind::InitAt(left, right) => {
            nodes.push(Node::Value(right, Rc::clone(&renames)));
            nodes.push(Node::Value(left, renames));
        }
        TypedCompKind::Call { args, .. }
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. }
        | TypedCompKind::Io(_, args) => {
            for argument in args.iter_mut().rev() {
                nodes.push(Node::Value(argument, Rc::clone(&renames)));
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            for (pattern, body) in arms.iter_mut().rev() {
                nodes.push(Node::Comp(body, scoped(&renames, pattern_names(pattern))));
            }
            nodes.push(Node::Value(scrutinee, renames));
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            for arm in ops.arms.iter_mut().rev() {
                nodes.push(Node::Comp(
                    &mut arm.body,
                    scoped(
                        &renames,
                        arm.params
                            .iter()
                            .map(|binder| binder.name)
                            .chain([arm.resume.name]),
                    ),
                ));
            }
            if let Some(return_body) = return_body {
                nodes.push(Node::Comp(
                    return_body,
                    scoped(&renames, return_binder.iter().map(|binder| binder.name)),
                ));
            }
            nodes.push(Node::Comp(body, renames));
        }
        TypedCompKind::Mask(_, body) => nodes.push(Node::Comp(body, renames)),
        TypedCompKind::WithReuse { token, freed, body } => {
            nodes.push(Node::Comp(body, scoped(&renames, [token.name])));
            nodes.push(Node::Value(freed, renames));
        }
    }
}

fn push_value<'a>(nodes: &mut Vec<Node<'a>>, value: &'a mut TypedValue, renames: Renames) {
    match &mut value.kind {
        TypedValueKind::Var {
            name,
            instantiation,
        } => {
            if let Some(rebound) = renames.get(name) {
                *name = *rebound;
                for argument in instantiation.drain(..) {
                    discard_core_instantiation(argument);
                }
            }
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            nodes.push(Node::Value(inner, renames));
        }
        TypedValueKind::Thunk(body) => nodes.push(Node::Comp(body, renames)),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields.iter_mut().rev() {
                nodes.push(Node::Value(field, Rc::clone(&renames)));
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields.iter_mut().rev() {
                nodes.push(Node::Value(field, Rc::clone(&renames)));
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
