use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::build::lower_value_type;
use super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType};
use super::compat::union_rows;

#[derive(Clone, Copy)]
enum RawRename {
    None,
    Type { old: Sym, fresh: Sym, active: bool },
    Row { old: Sym, fresh: Sym, active: bool },
}

impl RawRename {
    fn under_type_binder(self, binder: Sym) -> Self {
        match self {
            Self::Type { old, fresh, .. } if old == binder => Self::Type {
                old,
                fresh,
                active: false,
            },
            other => other,
        }
    }

    fn under_row_binder(self, binder: Sym) -> Self {
        match self {
            Self::Row { old, fresh, .. } if old == binder => Self::Row {
                old,
                fresh,
                active: false,
            },
            other => other,
        }
    }

    const fn reduces_apps(self) -> bool {
        !matches!(self, Self::None)
    }
}

enum TypeCloneTask<'a> {
    Type(&'a Type, RawRename),
    Row(&'a EffRow, RawRename),
    Forall(Sym),
    RowForall(Sym),
    Fun(usize),
    Con(Sym, usize),
    App(bool),
    Tuple(usize),
    UnboxedTuple(usize),
    UnboxedRecord(Vec<Sym>),
    OrNull,
    TypeRow,
    Coeffect(crate::types::coeffect::CoeffectRow),
    RowExtend(Sym, usize),
}

enum ClonedTypeNode {
    Type(Type),
    Row(EffRow),
}

impl ClonedTypeNode {
    fn into_row(self) -> EffRow {
        let Self::Row(row) = self else {
            unreachable!("row root produces a row")
        };
        row
    }
}

fn pop_cloned_type(output: &mut Vec<ClonedTypeNode>) -> Type {
    let Some(ClonedTypeNode::Type(ty)) = output.pop() else {
        unreachable!("type-clone worklist preserves result kinds")
    };
    ty
}

fn pop_cloned_row(output: &mut Vec<ClonedTypeNode>) -> EffRow {
    let Some(ClonedTypeNode::Row(row)) = output.pop() else {
        unreachable!("type-clone worklist preserves result kinds")
    };
    row
}

fn pop_cloned_types(output: &mut Vec<ClonedTypeNode>, count: usize) -> Vec<Type> {
    let start = output.len() - count;
    output
        .drain(start..)
        .map(|node| {
            let ClonedTypeNode::Type(ty) = node else {
                unreachable!("type-clone worklist preserves result kinds")
            };
            ty
        })
        .collect()
}

fn clone_type_or_row(root: TypeCloneTask<'_>) -> ClonedTypeNode {
    let mut work = vec![root];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            TypeCloneTask::Type(ty, rename) => match ty {
                Type::Unit => output.push(ClonedTypeNode::Type(Type::Unit)),
                Type::Int => output.push(ClonedTypeNode::Type(Type::Int)),
                Type::I64 => output.push(ClonedTypeNode::Type(Type::I64)),
                Type::U64 => output.push(ClonedTypeNode::Type(Type::U64)),
                Type::Bool => output.push(ClonedTypeNode::Type(Type::Bool)),
                Type::Float => output.push(ClonedTypeNode::Type(Type::Float)),
                Type::Char => output.push(ClonedTypeNode::Type(Type::Char)),
                Type::Str => output.push(ClonedTypeNode::Type(Type::Str)),
                Type::Var(name) => {
                    let name = match rename {
                        RawRename::Type {
                            old,
                            fresh,
                            active: true,
                        } if *name == old => fresh,
                        _ => *name,
                    };
                    output.push(ClonedTypeNode::Type(Type::Var(name)));
                }
                Type::Exist(id) => output.push(ClonedTypeNode::Type(Type::Exist(*id))),
                Type::Forall(name, body) => {
                    work.push(TypeCloneTask::Forall(*name));
                    work.push(TypeCloneTask::Type(body, rename.under_type_binder(*name)));
                }
                Type::RowForall(name, body) => {
                    work.push(TypeCloneTask::RowForall(*name));
                    work.push(TypeCloneTask::Type(body, rename.under_row_binder(*name)));
                }
                Type::Fun(params, effects, result) => {
                    work.push(TypeCloneTask::Fun(params.len()));
                    work.push(TypeCloneTask::Type(result, rename));
                    work.push(TypeCloneTask::Row(effects, rename));
                    work.extend(
                        params
                            .iter()
                            .rev()
                            .map(|param| TypeCloneTask::Type(param, rename)),
                    );
                }
                Type::Con(name, arguments) => {
                    work.push(TypeCloneTask::Con(*name, arguments.len()));
                    work.extend(
                        arguments
                            .iter()
                            .rev()
                            .map(|argument| TypeCloneTask::Type(argument, rename)),
                    );
                }
                Type::App(head, argument) => {
                    work.push(TypeCloneTask::App(rename.reduces_apps()));
                    work.push(TypeCloneTask::Type(argument, rename));
                    work.push(TypeCloneTask::Type(head, rename));
                }
                Type::Tuple(fields) => {
                    work.push(TypeCloneTask::Tuple(fields.len()));
                    work.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|field| TypeCloneTask::Type(field, rename)),
                    );
                }
                Type::UnboxedTuple(fields) => {
                    work.push(TypeCloneTask::UnboxedTuple(fields.len()));
                    work.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|field| TypeCloneTask::Type(field, rename)),
                    );
                }
                Type::UnboxedRecord(fields) => {
                    work.push(TypeCloneTask::UnboxedRecord(
                        fields.iter().map(|(name, _)| *name).collect(),
                    ));
                    work.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|(_, field)| TypeCloneTask::Type(field, rename)),
                    );
                }
                Type::OrNull(inner) => {
                    work.push(TypeCloneTask::OrNull);
                    work.push(TypeCloneTask::Type(inner, rename));
                }
                Type::Row(row) => {
                    work.push(TypeCloneTask::TypeRow);
                    work.push(TypeCloneTask::Row(row, rename));
                }
                Type::Nat(value) => output.push(ClonedTypeNode::Type(Type::Nat(*value))),
                Type::Coeffect(inner, row) => {
                    work.push(TypeCloneTask::Coeffect(row.clone()));
                    work.push(TypeCloneTask::Type(inner, rename));
                }
            },
            TypeCloneTask::Row(row, rename) => match row {
                EffRow::Empty => output.push(ClonedTypeNode::Row(EffRow::Empty)),
                EffRow::Var(name) => {
                    let name = match rename {
                        RawRename::Row {
                            old,
                            fresh,
                            active: true,
                        } if *name == old => fresh,
                        _ => *name,
                    };
                    output.push(ClonedTypeNode::Row(EffRow::Var(name)));
                }
                EffRow::Exist(id) => output.push(ClonedTypeNode::Row(EffRow::Exist(*id))),
                EffRow::Extend(label, rest) => {
                    work.push(TypeCloneTask::RowExtend(label.name, label.args.len()));
                    work.push(TypeCloneTask::Row(rest, rename));
                    work.extend(
                        label
                            .args
                            .iter()
                            .rev()
                            .map(|argument| TypeCloneTask::Type(argument, rename)),
                    );
                }
            },
            TypeCloneTask::Forall(name) => {
                let body = pop_cloned_type(&mut output);
                output.push(ClonedTypeNode::Type(Type::Forall(name, Box::new(body))));
            }
            TypeCloneTask::RowForall(name) => {
                let body = pop_cloned_type(&mut output);
                output.push(ClonedTypeNode::Type(Type::RowForall(name, Box::new(body))));
            }
            TypeCloneTask::Fun(param_count) => {
                let result = pop_cloned_type(&mut output);
                let effects = pop_cloned_row(&mut output);
                let params = pop_cloned_types(&mut output, param_count);
                output.push(ClonedTypeNode::Type(Type::Fun(
                    params,
                    effects,
                    Box::new(result),
                )));
            }
            TypeCloneTask::Con(name, argument_count) => {
                let arguments = pop_cloned_types(&mut output, argument_count);
                output.push(ClonedTypeNode::Type(Type::Con(name, arguments)));
            }
            TypeCloneTask::App(reduce) => {
                let argument = pop_cloned_type(&mut output);
                let head = pop_cloned_type(&mut output);
                output.push(ClonedTypeNode::Type(if reduce {
                    Type::app(head, argument)
                } else {
                    Type::App(Box::new(head), Box::new(argument))
                }));
            }
            TypeCloneTask::Tuple(field_count) => {
                let fields = pop_cloned_types(&mut output, field_count);
                output.push(ClonedTypeNode::Type(Type::Tuple(fields)));
            }
            TypeCloneTask::UnboxedTuple(field_count) => {
                let fields = pop_cloned_types(&mut output, field_count);
                output.push(ClonedTypeNode::Type(Type::UnboxedTuple(fields)));
            }
            TypeCloneTask::UnboxedRecord(names) => {
                let fields = pop_cloned_types(&mut output, names.len());
                output.push(ClonedTypeNode::Type(Type::UnboxedRecord(
                    names.into_iter().zip(fields).collect(),
                )));
            }
            TypeCloneTask::OrNull => {
                let inner = pop_cloned_type(&mut output);
                output.push(ClonedTypeNode::Type(Type::OrNull(Box::new(inner))));
            }
            TypeCloneTask::TypeRow => {
                let row = pop_cloned_row(&mut output);
                output.push(ClonedTypeNode::Type(Type::Row(row)));
            }
            TypeCloneTask::Coeffect(row) => {
                let inner = pop_cloned_type(&mut output);
                output.push(ClonedTypeNode::Type(Type::Coeffect(Box::new(inner), row)));
            }
            TypeCloneTask::RowExtend(name, argument_count) => {
                let rest = pop_cloned_row(&mut output);
                let args = pop_cloned_types(&mut output, argument_count);
                output.push(ClonedTypeNode::Row(EffRow::Extend(
                    Label { name, args },
                    Box::new(rest),
                )));
            }
        }
    }
    output
        .pop()
        .expect("type-clone worklist produces one result")
}

#[must_use]
pub(crate) fn clone_type(ty: &Type) -> Type {
    let ClonedTypeNode::Type(ty) = clone_type_or_row(TypeCloneTask::Type(ty, RawRename::None))
    else {
        unreachable!("type root produces a type")
    };
    ty
}

#[must_use]
pub(crate) fn clone_effect_row(row: &EffRow) -> EffRow {
    let ClonedTypeNode::Row(row) = clone_type_or_row(TypeCloneTask::Row(row, RawRename::None))
    else {
        unreachable!("row root produces a row")
    };
    row
}

pub(crate) fn rename_type_variable(ty: &Type, old: Sym, fresh: Sym) -> Type {
    let ClonedTypeNode::Type(ty) = clone_type_or_row(TypeCloneTask::Type(
        ty,
        RawRename::Type {
            old,
            fresh,
            active: true,
        },
    )) else {
        unreachable!("type root produces a type")
    };
    ty
}

pub(crate) fn rename_row_variable_in_type(ty: &Type, old: Sym, fresh: Sym) -> Type {
    let ClonedTypeNode::Type(ty) = clone_type_or_row(TypeCloneTask::Type(
        ty,
        RawRename::Row {
            old,
            fresh,
            active: true,
        },
    )) else {
        unreachable!("type root produces a type")
    };
    ty
}

pub(crate) fn rename_type_variable_in_row(row: &EffRow, old: Sym, fresh: Sym) -> EffRow {
    let ClonedTypeNode::Row(row) = clone_type_or_row(TypeCloneTask::Row(
        row,
        RawRename::Type {
            old,
            fresh,
            active: true,
        },
    )) else {
        unreachable!("row root produces a row")
    };
    row
}

pub(crate) fn rename_row_variable_in_row(row: &EffRow, old: Sym, fresh: Sym) -> EffRow {
    let ClonedTypeNode::Row(row) = clone_type_or_row(TypeCloneTask::Row(
        row,
        RawRename::Row {
            old,
            fresh,
            active: true,
        },
    )) else {
        unreachable!("row root produces a row")
    };
    row
}

#[derive(Clone, Copy)]
enum CoreRename {
    None,
    Type { old: Sym, fresh: Sym },
    Row { old: Sym, fresh: Sym },
}

impl CoreRename {
    const fn raw(self) -> RawRename {
        match self {
            Self::None => RawRename::None,
            Self::Type { old, fresh } => RawRename::Type {
                old,
                fresh,
                active: true,
            },
            Self::Row { old, fresh } => RawRename::Row {
                old,
                fresh,
                active: true,
            },
        }
    }

    fn shadowed_by(self, quantifiers: &[CoreQuantifier]) -> bool {
        quantifiers.iter().any(|quantifier| {
            matches!(
                (self, quantifier),
                (Self::Type { old, .. }, CoreQuantifier::Type(bound))
                    | (Self::Row { old, .. }, CoreQuantifier::Row(bound)) if old == *bound
            )
        })
    }
}

enum CoreCloneTask<'a> {
    Type(&'a CoreType, CoreRename),
    Sig(&'a CompSig, CoreRename),
    FnSig(&'a CoreFnSig, CoreRename),
    Thunk,
    Function,
    Ref,
    ReuseToken,
    FinishSig(EffRow),
    FinishFnSig(Vec<CoreQuantifier>, usize),
}

enum ClonedCoreNode {
    Type(CoreType),
    Sig(CompSig),
    FnSig(CoreFnSig),
}

fn clone_core_node(root: CoreCloneTask<'_>) -> ClonedCoreNode {
    let mut work = vec![root];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            CoreCloneTask::Type(ty, rename) => match ty {
                CoreType::Source(ty) => {
                    let ty = match rename {
                        CoreRename::None => clone_type(ty),
                        CoreRename::Type { old, fresh } => rename_type_variable(ty, old, fresh),
                        CoreRename::Row { old, fresh } => {
                            rename_row_variable_in_type(ty, old, fresh)
                        }
                    };
                    output.push(ClonedCoreNode::Type(CoreType::Source(ty)));
                }
                CoreType::Thunk(signature) => {
                    work.push(CoreCloneTask::Thunk);
                    work.push(CoreCloneTask::Sig(signature, rename));
                }
                CoreType::Function(signature) => {
                    work.push(CoreCloneTask::Function);
                    let rename = if rename.shadowed_by(signature.quantifiers()) {
                        CoreRename::None
                    } else {
                        rename
                    };
                    work.push(CoreCloneTask::FnSig(signature, rename));
                }
                CoreType::Ref(inner) => {
                    work.push(CoreCloneTask::Ref);
                    work.push(CoreCloneTask::Type(inner, rename));
                }
                CoreType::ReuseToken(inner) => {
                    work.push(CoreCloneTask::ReuseToken);
                    work.push(CoreCloneTask::Type(inner, rename));
                }
                CoreType::Lowered(kind) => {
                    let kind = match kind {
                        LoweredType::Word => LoweredType::Word,
                        LoweredType::Eff(row) => LoweredType::Eff(
                            clone_type_or_row(TypeCloneTask::Row(row, rename.raw())).into_row(),
                        ),
                        LoweredType::Queue(row) => LoweredType::Queue(
                            clone_type_or_row(TypeCloneTask::Row(row, rename.raw())).into_row(),
                        ),
                        LoweredType::QueueView(row) => LoweredType::QueueView(
                            clone_type_or_row(TypeCloneTask::Row(row, rename.raw())).into_row(),
                        ),
                    };
                    output.push(ClonedCoreNode::Type(CoreType::Lowered(kind)));
                }
            },
            CoreCloneTask::Sig(signature, rename) => {
                let ClonedTypeNode::Row(effects) =
                    clone_type_or_row(TypeCloneTask::Row(signature.effects(), rename.raw()))
                else {
                    unreachable!("row root produces a row")
                };
                work.push(CoreCloneTask::FinishSig(effects));
                work.push(CoreCloneTask::Type(signature.result(), rename));
            }
            CoreCloneTask::FnSig(signature, rename) => {
                work.push(CoreCloneTask::FinishFnSig(
                    signature.quantifiers().to_vec(),
                    signature.params().len(),
                ));
                work.push(CoreCloneTask::Sig(signature.body(), rename));
                work.extend(
                    signature
                        .params()
                        .iter()
                        .rev()
                        .map(|ty| CoreCloneTask::Type(ty, rename)),
                );
            }
            CoreCloneTask::Thunk => {
                let Some(ClonedCoreNode::Sig(signature)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Thunk(Box::new(signature))));
            }
            CoreCloneTask::Function => {
                let Some(ClonedCoreNode::FnSig(signature)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Function(Box::new(
                    signature,
                ))));
            }
            CoreCloneTask::Ref => {
                let Some(ClonedCoreNode::Type(inner)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Ref(Box::new(inner))));
            }
            CoreCloneTask::ReuseToken => {
                let Some(ClonedCoreNode::Type(inner)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::ReuseToken(Box::new(inner))));
            }
            CoreCloneTask::FinishSig(effects) => {
                let Some(ClonedCoreNode::Type(result)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Sig(CompSig::new(result, effects)));
            }
            CoreCloneTask::FinishFnSig(quantifiers, param_count) => {
                let Some(ClonedCoreNode::Sig(body)) = output.pop() else {
                    unreachable!("core-clone worklist preserves result kinds")
                };
                let start = output.len() - param_count;
                let params = output
                    .drain(start..)
                    .map(|node| {
                        let ClonedCoreNode::Type(ty) = node else {
                            unreachable!("core-clone worklist preserves result kinds")
                        };
                        ty
                    })
                    .collect();
                output.push(ClonedCoreNode::FnSig(CoreFnSig::new(
                    quantifiers,
                    params,
                    body,
                )));
            }
        }
    }
    output
        .pop()
        .expect("core-clone worklist produces one result")
}

#[must_use]
pub(crate) fn clone_core_type(ty: &CoreType) -> CoreType {
    let ClonedCoreNode::Type(ty) = clone_core_node(CoreCloneTask::Type(ty, CoreRename::None))
    else {
        unreachable!("CoreType root produces a CoreType")
    };
    ty
}

#[must_use]
pub(crate) fn clone_comp_sig(signature: &CompSig) -> CompSig {
    let ClonedCoreNode::Sig(signature) =
        clone_core_node(CoreCloneTask::Sig(signature, CoreRename::None))
    else {
        unreachable!("CompSig root produces a CompSig")
    };
    signature
}

#[must_use]
pub(crate) fn clone_core_fn_sig(signature: &CoreFnSig) -> CoreFnSig {
    let ClonedCoreNode::FnSig(signature) =
        clone_core_node(CoreCloneTask::FnSig(signature, CoreRename::None))
    else {
        unreachable!("CoreFnSig root produces a CoreFnSig")
    };
    signature
}

#[must_use]
pub(crate) fn clone_core_instantiation(instantiation: &CoreInstantiation) -> CoreInstantiation {
    match instantiation {
        CoreInstantiation::Type(ty) => CoreInstantiation::Type(clone_type(ty)),
        CoreInstantiation::Row(row) => CoreInstantiation::Row(clone_effect_row(row)),
    }
}

enum TypeDiscardTask {
    Type(Type),
    Row(EffRow),
}

fn discard_type_or_row(root: TypeDiscardTask) {
    let mut work = vec![root];
    while let Some(task) = work.pop() {
        match task {
            TypeDiscardTask::Type(ty) => match ty {
                Type::Forall(_, body)
                | Type::RowForall(_, body)
                | Type::OrNull(body)
                | Type::Coeffect(body, _) => work.push(TypeDiscardTask::Type(*body)),
                Type::Fun(params, effects, result) => {
                    work.push(TypeDiscardTask::Type(*result));
                    work.push(TypeDiscardTask::Row(effects));
                    work.extend(params.into_iter().rev().map(TypeDiscardTask::Type));
                }
                Type::Con(_, arguments)
                | Type::Tuple(arguments)
                | Type::UnboxedTuple(arguments) => {
                    work.extend(arguments.into_iter().rev().map(TypeDiscardTask::Type));
                }
                Type::App(head, argument) => {
                    work.push(TypeDiscardTask::Type(*argument));
                    work.push(TypeDiscardTask::Type(*head));
                }
                Type::UnboxedRecord(fields) => work.extend(
                    fields
                        .into_iter()
                        .rev()
                        .map(|(_, ty)| TypeDiscardTask::Type(ty)),
                ),
                Type::Row(row) => work.push(TypeDiscardTask::Row(row)),
                Type::Unit
                | Type::Int
                | Type::I64
                | Type::U64
                | Type::Bool
                | Type::Float
                | Type::Char
                | Type::Str
                | Type::Var(_)
                | Type::Exist(_)
                | Type::Nat(_) => {}
            },
            TypeDiscardTask::Row(row) => match row {
                EffRow::Extend(label, rest) => {
                    work.push(TypeDiscardTask::Row(*rest));
                    work.extend(label.args.into_iter().rev().map(TypeDiscardTask::Type));
                }
                EffRow::Empty | EffRow::Var(_) | EffRow::Exist(_) => {}
            },
        }
    }
}

pub(crate) fn discard_type(ty: Type) {
    discard_type_or_row(TypeDiscardTask::Type(ty));
}

pub(crate) fn discard_effect_row(row: EffRow) {
    discard_type_or_row(TypeDiscardTask::Row(row));
}

enum CoreDiscardTask {
    Type(CoreType),
    Sig(CompSig),
    FnSig(CoreFnSig),
}

fn discard_core_node(root: CoreDiscardTask) {
    let mut work = vec![root];
    while let Some(task) = work.pop() {
        match task {
            CoreDiscardTask::Type(ty) => match ty {
                CoreType::Source(ty) => discard_type(ty),
                CoreType::Thunk(signature) => work.push(CoreDiscardTask::Sig(*signature)),
                CoreType::Function(signature) => work.push(CoreDiscardTask::FnSig(*signature)),
                CoreType::Ref(inner) | CoreType::ReuseToken(inner) => {
                    work.push(CoreDiscardTask::Type(*inner));
                }
                CoreType::Lowered(kind) => match kind {
                    LoweredType::Word => {}
                    LoweredType::Eff(row)
                    | LoweredType::Queue(row)
                    | LoweredType::QueueView(row) => discard_effect_row(row),
                },
            },
            CoreDiscardTask::Sig(signature) => {
                let CompSig { result, effects } = signature;
                discard_effect_row(effects);
                work.push(CoreDiscardTask::Type(result));
            }
            CoreDiscardTask::FnSig(signature) => {
                let CoreFnSig {
                    quantifiers: _,
                    params,
                    body,
                } = signature;
                work.push(CoreDiscardTask::Sig(body));
                work.extend(params.into_iter().rev().map(CoreDiscardTask::Type));
            }
        }
    }
}

pub(crate) fn discard_core_type(ty: CoreType) {
    discard_core_node(CoreDiscardTask::Type(ty));
}

pub(crate) fn discard_comp_sig(signature: CompSig) {
    discard_core_node(CoreDiscardTask::Sig(signature));
}

pub(crate) fn discard_core_fn_sig(signature: CoreFnSig) {
    discard_core_node(CoreDiscardTask::FnSig(signature));
}

pub(crate) fn discard_core_instantiation(instantiation: CoreInstantiation) {
    match instantiation {
        CoreInstantiation::Type(ty) => discard_type(ty),
        CoreInstantiation::Row(row) => discard_effect_row(row),
    }
}

#[derive(Clone)]
struct Substitution<'a> {
    pairs: Vec<(&'a CoreQuantifier, &'a CoreInstantiation)>,
}

impl<'a> Substitution<'a> {
    fn new(quantifiers: &'a [CoreQuantifier], arguments: &'a [CoreInstantiation]) -> Self {
        Self {
            pairs: quantifiers.iter().zip(arguments).collect(),
        }
    }

    fn without_shadowed(&self, signature: &CoreFnSig) -> Self {
        let shadowed: BTreeSet<_> = signature
            .quantifiers()
            .iter()
            .map(|quantifier| match quantifier {
                CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => *name,
            })
            .collect();
        Self {
            pairs: self
                .pairs
                .iter()
                .copied()
                .filter(|(quantifier, _)| match quantifier {
                    CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => {
                        !shadowed.contains(name)
                    }
                })
                .collect(),
        }
    }

    fn maps(&self) -> (BTreeMap<Sym, Type>, BTreeMap<Sym, EffRow>) {
        let mut types = BTreeMap::new();
        let mut rows = BTreeMap::new();
        for (quantifier, argument) in &self.pairs {
            match (quantifier, argument) {
                (CoreQuantifier::Type(name), CoreInstantiation::Type(argument)) => {
                    types.insert(*name, clone_type(argument));
                }
                (CoreQuantifier::Row(name), CoreInstantiation::Row(argument)) => {
                    rows.insert(*name, clone_effect_row(argument));
                }
                _ => {}
            }
        }
        (types, rows)
    }
}

fn substitute_type_in(ty: &Type, substitution: &Substitution<'_>) -> Type {
    let (types, rows) = substitution.maps();
    substitute_type_with(ty, &types, &rows, &BTreeSet::new(), &BTreeSet::new())
}

fn substitute_row_in(row: &EffRow, substitution: &Substitution<'_>) -> EffRow {
    let (types, rows) = substitution.maps();
    substitute_row_with(row, &types, &rows, &BTreeSet::new(), &BTreeSet::new())
}

fn prepare_fn_signature<'a>(
    mut signature: CoreFnSig,
    substitution: &Substitution<'a>,
) -> (CoreFnSig, Substitution<'a>) {
    // Drop substitutions shadowed by the signature's own quantifiers FIRST. A
    // shadowed outer quantifier is not substituted into this inner scope, so its
    // argument must not drive capture-avoidance: otherwise an inner rank-2 binder
    // that deliberately reuses an outer quantifier's name (a state-fusion
    // producer thunk) is spuriously renamed out of sync with its references.
    let substitution = substitution.without_shadowed(&signature);

    let mut inserted_types = BTreeSet::new();
    let mut inserted_rows = BTreeSet::new();
    for (_, argument) in &substitution.pairs {
        match argument {
            CoreInstantiation::Type(ty) => {
                ty.free_ty_vars(&mut inserted_types);
                ty.free_row_vars(&mut inserted_rows);
            }
            CoreInstantiation::Row(row) => {
                if let EffRow::Var(name) = row.tail() {
                    inserted_rows.insert(*name);
                }
                for label in row.labels() {
                    for argument in &label.args {
                        argument.free_ty_vars(&mut inserted_types);
                        argument.free_row_vars(&mut inserted_rows);
                    }
                }
            }
        }
    }
    for index in 0..signature.quantifiers().len() {
        let (name, collision) = match &signature.quantifiers()[index] {
            CoreQuantifier::Type(name) => (*name, inserted_types.contains(name)),
            CoreQuantifier::Row(name) => (*name, inserted_rows.contains(name)),
        };
        if collision {
            let mut suffix = 0;
            let fresh = loop {
                let candidate = Sym::from(names::typed_quantifier(name.as_str(), suffix));
                suffix += 1;
                if !inserted_types.contains(&candidate)
                    && !inserted_rows.contains(&candidate)
                    && !signature.quantifiers().iter().any(|quantifier| {
                        matches!(
                            quantifier,
                            CoreQuantifier::Type(bound) | CoreQuantifier::Row(bound)
                                if *bound == candidate
                        )
                    })
                {
                    break candidate;
                }
            };
            let renamed = rename_fn_quantifier(&signature, index, fresh);
            discard_core_fn_sig(signature);
            signature = renamed;
        }
    }
    (signature, substitution)
}

enum CoreSubstitutionTask<'a> {
    Type(CoreType, Substitution<'a>),
    Sig(CompSig, Substitution<'a>),
    FnSig(CoreFnSig, Substitution<'a>),
    Thunk,
    Function,
    Ref,
    ReuseToken,
    FinishSig(EffRow),
    FinishFnSig(Vec<CoreQuantifier>, usize),
}

fn substitute_core_node(root: CoreSubstitutionTask<'_>) -> ClonedCoreNode {
    let mut work = vec![root];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            CoreSubstitutionTask::Type(ty, substitution) => match ty {
                CoreType::Source(ty) => {
                    let substituted = substitute_type_in(&ty, &substitution);
                    discard_type(ty);
                    let lowered = lower_value_type(&substituted);
                    discard_type(substituted);
                    output.push(ClonedCoreNode::Type(lowered));
                }
                CoreType::Thunk(signature) => {
                    work.push(CoreSubstitutionTask::Thunk);
                    work.push(CoreSubstitutionTask::Sig(*signature, substitution));
                }
                CoreType::Function(signature) => {
                    work.push(CoreSubstitutionTask::Function);
                    work.push(CoreSubstitutionTask::FnSig(*signature, substitution));
                }
                CoreType::Ref(inner) => {
                    work.push(CoreSubstitutionTask::Ref);
                    work.push(CoreSubstitutionTask::Type(*inner, substitution));
                }
                CoreType::ReuseToken(inner) => {
                    work.push(CoreSubstitutionTask::ReuseToken);
                    work.push(CoreSubstitutionTask::Type(*inner, substitution));
                }
                CoreType::Lowered(kind) => {
                    let kind = match kind {
                        LoweredType::Word => LoweredType::Word,
                        LoweredType::Eff(row) => {
                            let substituted = substitute_row_in(&row, &substitution);
                            discard_effect_row(row);
                            LoweredType::Eff(substituted)
                        }
                        LoweredType::Queue(row) => {
                            let substituted = substitute_row_in(&row, &substitution);
                            discard_effect_row(row);
                            LoweredType::Queue(substituted)
                        }
                        LoweredType::QueueView(row) => {
                            let substituted = substitute_row_in(&row, &substitution);
                            discard_effect_row(row);
                            LoweredType::QueueView(substituted)
                        }
                    };
                    output.push(ClonedCoreNode::Type(CoreType::Lowered(kind)));
                }
            },
            CoreSubstitutionTask::Sig(signature, substitution) => {
                let CompSig { result, effects } = signature;
                let substituted_effects = substitute_row_in(&effects, &substitution);
                discard_effect_row(effects);
                work.push(CoreSubstitutionTask::FinishSig(substituted_effects));
                work.push(CoreSubstitutionTask::Type(result, substitution));
            }
            CoreSubstitutionTask::FnSig(signature, substitution) => {
                let (signature, substitution) = prepare_fn_signature(signature, &substitution);
                let CoreFnSig {
                    quantifiers,
                    params,
                    body,
                } = signature;
                work.push(CoreSubstitutionTask::FinishFnSig(quantifiers, params.len()));
                work.push(CoreSubstitutionTask::Sig(body, substitution.clone()));
                work.extend(
                    params
                        .into_iter()
                        .rev()
                        .map(|ty| CoreSubstitutionTask::Type(ty, substitution.clone())),
                );
            }
            CoreSubstitutionTask::Thunk => {
                let Some(ClonedCoreNode::Sig(signature)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Thunk(Box::new(signature))));
            }
            CoreSubstitutionTask::Function => {
                let Some(ClonedCoreNode::FnSig(signature)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Function(Box::new(
                    signature,
                ))));
            }
            CoreSubstitutionTask::Ref => {
                let Some(ClonedCoreNode::Type(inner)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::Ref(Box::new(inner))));
            }
            CoreSubstitutionTask::ReuseToken => {
                let Some(ClonedCoreNode::Type(inner)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Type(CoreType::ReuseToken(Box::new(inner))));
            }
            CoreSubstitutionTask::FinishSig(effects) => {
                let Some(ClonedCoreNode::Type(result)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                output.push(ClonedCoreNode::Sig(CompSig::new(result, effects)));
            }
            CoreSubstitutionTask::FinishFnSig(quantifiers, param_count) => {
                let Some(ClonedCoreNode::Sig(body)) = output.pop() else {
                    unreachable!("core-substitution worklist preserves result kinds")
                };
                let start = output.len() - param_count;
                let params = output
                    .drain(start..)
                    .map(|node| {
                        let ClonedCoreNode::Type(ty) = node else {
                            unreachable!("core-substitution worklist preserves result kinds")
                        };
                        ty
                    })
                    .collect();
                output.push(ClonedCoreNode::FnSig(CoreFnSig::new(
                    quantifiers,
                    params,
                    body,
                )));
            }
        }
    }
    output.pop().expect("core substitution produces one result")
}

#[must_use]
pub fn substitute_core_type(
    ty: &CoreType,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreType {
    let root = clone_core_type(ty);
    let ClonedCoreNode::Type(ty) = substitute_core_node(CoreSubstitutionTask::Type(
        root,
        Substitution::new(quantifiers, arguments),
    )) else {
        unreachable!("CoreType root produces a CoreType")
    };
    ty
}

#[must_use]
pub fn substitute_fn_sig(
    signature: &CoreFnSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreFnSig {
    let root = clone_core_fn_sig(signature);
    let ClonedCoreNode::FnSig(signature) = substitute_core_node(CoreSubstitutionTask::FnSig(
        root,
        Substitution::new(quantifiers, arguments),
    )) else {
        unreachable!("CoreFnSig root produces a CoreFnSig")
    };
    signature
}

#[must_use]
pub fn substitute_sig(
    signature: &CompSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CompSig {
    let root = clone_comp_sig(signature);
    let ClonedCoreNode::Sig(signature) = substitute_core_node(CoreSubstitutionTask::Sig(
        root,
        Substitution::new(quantifiers, arguments),
    )) else {
        unreachable!("CompSig root produces a CompSig")
    };
    signature
}

pub(super) fn rename_fn_quantifier(signature: &CoreFnSig, index: usize, fresh: Sym) -> CoreFnSig {
    let old = signature.quantifiers()[index].clone();
    let mut quantifiers = signature.quantifiers().to_vec();
    quantifiers[index] = match old {
        CoreQuantifier::Type(_) => CoreQuantifier::Type(fresh),
        CoreQuantifier::Row(_) => CoreQuantifier::Row(fresh),
    };
    CoreFnSig::new(
        quantifiers,
        signature
            .params()
            .iter()
            .map(|ty| rename_bound_core(ty, &old, fresh))
            .collect(),
        CompSig::new(
            rename_bound_core(signature.body().result(), &old, fresh),
            rename_bound_row(signature.body().effects(), &old, fresh),
        ),
    )
}

#[must_use]
pub fn rename_bound_core(ty: &CoreType, old: &CoreQuantifier, fresh: Sym) -> CoreType {
    let rename = match old {
        CoreQuantifier::Type(old) => CoreRename::Type { old: *old, fresh },
        CoreQuantifier::Row(old) => CoreRename::Row { old: *old, fresh },
    };
    let ClonedCoreNode::Type(ty) = clone_core_node(CoreCloneTask::Type(ty, rename)) else {
        unreachable!("CoreType root produces a CoreType")
    };
    ty
}

fn rename_bound_row(row: &EffRow, old: &CoreQuantifier, fresh: Sym) -> EffRow {
    match old {
        CoreQuantifier::Type(name) => rename_type_variable_in_row(row, *name, fresh),
        CoreQuantifier::Row(name) => rename_row_variable_in_row(row, *name, fresh),
    }
}

#[must_use]
pub fn substitute_type(
    ty: &Type,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Type {
    substitute_type_in(ty, &Substitution::new(quantifiers, arguments))
}

#[must_use]
pub fn substitute_row(
    row: &EffRow,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> EffRow {
    substitute_row_in(row, &Substitution::new(quantifiers, arguments))
}

enum SubstitutionTask<'a> {
    Type(&'a Type),
    LeaveTypeBinder(Sym, bool),
    LeaveRowBinder(Sym, bool),
    Forall(Sym),
    RowForall(Sym),
    Fun(usize, EffRow),
    Con(Sym, usize),
    App,
    Tuple(usize),
    UnboxedTuple(usize),
    UnboxedRecord(Vec<Sym>),
    OrNull,
    Coeffect(crate::types::coeffect::CoeffectRow),
}

fn substitute_type_with(
    ty: &Type,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    initial_bound_types: &BTreeSet<Sym>,
    initial_bound_rows: &BTreeSet<Sym>,
) -> Type {
    let mut bound_types = initial_bound_types.clone();
    let mut bound_rows = initial_bound_rows.clone();
    let mut work = vec![SubstitutionTask::Type(ty)];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            SubstitutionTask::Type(ty) => match ty {
                Type::Var(name) if !bound_types.contains(name) => output.push(
                    types
                        .get(name)
                        .map_or_else(|| Type::Var(*name), normalize_type_rows),
                ),
                Type::Unit => output.push(Type::Unit),
                Type::Int => output.push(Type::Int),
                Type::I64 => output.push(Type::I64),
                Type::U64 => output.push(Type::U64),
                Type::Bool => output.push(Type::Bool),
                Type::Float => output.push(Type::Float),
                Type::Char => output.push(Type::Char),
                Type::Str => output.push(Type::Str),
                Type::Var(name) => output.push(Type::Var(*name)),
                Type::Exist(id) => output.push(Type::Exist(*id)),
                Type::Forall(name, body) => {
                    let inserted = bound_types.insert(*name);
                    work.push(SubstitutionTask::Forall(*name));
                    work.push(SubstitutionTask::LeaveTypeBinder(*name, inserted));
                    work.push(SubstitutionTask::Type(body));
                }
                Type::RowForall(name, body) => {
                    let inserted = bound_rows.insert(*name);
                    work.push(SubstitutionTask::RowForall(*name));
                    work.push(SubstitutionTask::LeaveRowBinder(*name, inserted));
                    work.push(SubstitutionTask::Type(body));
                }
                Type::Fun(params, effects, result) => {
                    let effects =
                        substitute_row_with(effects, types, rows, &bound_types, &bound_rows);
                    work.push(SubstitutionTask::Fun(params.len(), effects));
                    work.push(SubstitutionTask::Type(result));
                    work.extend(params.iter().rev().map(SubstitutionTask::Type));
                }
                Type::Con(name, arguments) => {
                    work.push(SubstitutionTask::Con(*name, arguments.len()));
                    work.extend(arguments.iter().rev().map(SubstitutionTask::Type));
                }
                Type::App(head, argument) => {
                    work.push(SubstitutionTask::App);
                    work.push(SubstitutionTask::Type(argument));
                    work.push(SubstitutionTask::Type(head));
                }
                Type::Tuple(fields) => {
                    work.push(SubstitutionTask::Tuple(fields.len()));
                    work.extend(fields.iter().rev().map(SubstitutionTask::Type));
                }
                Type::UnboxedTuple(fields) => {
                    work.push(SubstitutionTask::UnboxedTuple(fields.len()));
                    work.extend(fields.iter().rev().map(SubstitutionTask::Type));
                }
                Type::UnboxedRecord(fields) => {
                    work.push(SubstitutionTask::UnboxedRecord(
                        fields.iter().map(|(name, _)| *name).collect(),
                    ));
                    work.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|(_, ty)| SubstitutionTask::Type(ty)),
                    );
                }
                Type::OrNull(inner) => {
                    work.push(SubstitutionTask::OrNull);
                    work.push(SubstitutionTask::Type(inner));
                }
                Type::Row(row) => output.push(Type::Row(substitute_row_with(
                    row,
                    types,
                    rows,
                    &bound_types,
                    &bound_rows,
                ))),
                Type::Nat(value) => output.push(Type::Nat(*value)),
                Type::Coeffect(inner, row) => {
                    work.push(SubstitutionTask::Coeffect(row.clone()));
                    work.push(SubstitutionTask::Type(inner));
                }
            },
            SubstitutionTask::LeaveTypeBinder(name, inserted) => {
                if inserted {
                    bound_types.remove(&name);
                }
            }
            SubstitutionTask::LeaveRowBinder(name, inserted) => {
                if inserted {
                    bound_rows.remove(&name);
                }
            }
            SubstitutionTask::Forall(name) => {
                let body = output.pop().expect("forall body is available");
                output.push(Type::Forall(name, Box::new(body)));
            }
            SubstitutionTask::RowForall(name) => {
                let body = output.pop().expect("row-forall body is available");
                output.push(Type::RowForall(name, Box::new(body)));
            }
            SubstitutionTask::Fun(param_count, effects) => {
                let result = output.pop().expect("function result is available");
                let start = output.len() - param_count;
                let params = output.drain(start..).collect();
                output.push(Type::Fun(params, effects, Box::new(result)));
            }
            SubstitutionTask::Con(name, argument_count) => {
                let start = output.len() - argument_count;
                let arguments = output.drain(start..).collect();
                output.push(Type::Con(name, arguments));
            }
            SubstitutionTask::App => {
                let argument = output.pop().expect("application argument is available");
                let head = output.pop().expect("application head is available");
                output.push(Type::app(head, argument));
            }
            SubstitutionTask::Tuple(field_count) => {
                let start = output.len() - field_count;
                let fields = output.drain(start..).collect();
                output.push(Type::Tuple(fields));
            }
            SubstitutionTask::UnboxedTuple(field_count) => {
                let start = output.len() - field_count;
                let fields = output.drain(start..).collect();
                output.push(Type::UnboxedTuple(fields));
            }
            SubstitutionTask::UnboxedRecord(names) => {
                let start = output.len() - names.len();
                let fields = names.into_iter().zip(output.drain(start..)).collect();
                output.push(Type::UnboxedRecord(fields));
            }
            SubstitutionTask::OrNull => {
                let inner = output.pop().expect("nullable inner type is available");
                output.push(Type::OrNull(Box::new(inner)));
            }
            SubstitutionTask::Coeffect(row) => {
                let inner = output.pop().expect("coeffect inner type is available");
                output.push(Type::Coeffect(Box::new(inner), row));
            }
        }
    }
    output.pop().expect("substitution produces one type")
}

fn substitute_row_with(
    row: &EffRow,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    bound_types: &BTreeSet<Sym>,
    bound_rows: &BTreeSet<Sym>,
) -> EffRow {
    // Collect the concrete head labels (substituting each label's type args),
    // then substitute the tail row-variable once and concatenate the head onto
    // it. Rows are multisets and an instantiation row is, by construction, the
    // demand BEYOND the declared head: the builder's `subsume_row` consumes
    // expected occurrences one-to-one and routes only a surplus copy into the
    // flexible tail. Substituting `e := {E | e0}` under a declared head `E`
    // must therefore stack to `{E, E | e0}`; a per-label MAX here would erase
    // the extra handler level the instantiation carries (the enclosing
    // combinator's own discharge) and understate the expected row.
    let mut head: Vec<Label> = Vec::new();
    let mut cur = row;
    loop {
        match cur {
            EffRow::Extend(label, rest) => {
                head.push(Label {
                    name: label.name,
                    args: label
                        .args
                        .iter()
                        .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                        .collect(),
                });
                cur = rest;
            }
            EffRow::Var(name) if !bound_rows.contains(name) => {
                let tail = rows
                    .get(name)
                    .map_or_else(|| EffRow::Var(*name), normalize_row);
                // An evidence-row variable is the threading's own rewidening
                // artifact: it stands for the residual ambient row, whose
                // labels are demand at the SAME handler level as the declared
                // head and may overlap it. Concatenating there would fabricate
                // a phantom extra level ({IO | %evr} at %evr := {IO} is one
                // IO handler, not two), so it merges per-label MAX instead.
                if names::is_evidence_row(name.as_str()) {
                    let head_row = EffRow::canonical(
                        head.iter().map(|label| Label {
                            name: label.name,
                            args: label.args.iter().map(clone_type).collect(),
                        }),
                        EffRow::Empty,
                    );
                    if let Ok(merged) = union_rows(&head_row, &tail) {
                        return merged;
                    }
                }
                return EffRow::canonical(
                    head.into_iter()
                        .chain(tail.labels().into_iter().map(|label| Label {
                            name: label.name,
                            args: label.args.iter().map(clone_type).collect(),
                        })),
                    match tail.tail() {
                        EffRow::Empty => EffRow::Empty,
                        EffRow::Var(name) => EffRow::Var(*name),
                        EffRow::Exist(id) => EffRow::Exist(*id),
                        EffRow::Extend(..) => unreachable!("row tail is terminal"),
                    },
                );
            }
            // Terminal tail: Empty, a bound row var, or an existential.
            EffRow::Empty | EffRow::Var(_) | EffRow::Exist(_) => {
                let tail = match cur {
                    EffRow::Empty => EffRow::Empty,
                    EffRow::Var(name) => EffRow::Var(*name),
                    EffRow::Exist(id) => EffRow::Exist(*id),
                    EffRow::Extend(..) => unreachable!("row tail is terminal"),
                };
                return EffRow::canonical(head, tail);
            }
        }
    }
}

#[must_use]
pub fn substitute_label(
    label: &Label,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Label {
    Label {
        name: label.name,
        args: label
            .args
            .iter()
            .map(|ty| substitute_type(ty, quantifiers, arguments))
            .collect(),
    }
}

fn normalize_row(row: &EffRow) -> EffRow {
    EffRow::canonical(
        row.labels().into_iter().map(|label| Label {
            name: label.name,
            args: label.args.iter().map(normalize_type_rows).collect(),
        }),
        match row.tail() {
            EffRow::Empty => EffRow::Empty,
            EffRow::Var(name) => EffRow::Var(*name),
            EffRow::Exist(id) => EffRow::Exist(*id),
            EffRow::Extend(..) => unreachable!("row tail is terminal"),
        },
    )
}

enum NormalizeTask<'a> {
    Type(&'a Type),
    Forall(Sym),
    RowForall(Sym),
    Fun(usize, EffRow),
    Con(Sym, usize),
    App,
    Tuple(usize),
    UnboxedTuple(usize),
    UnboxedRecord(Vec<Sym>),
    OrNull,
    Coeffect(crate::types::coeffect::CoeffectRow),
}

fn normalize_type_rows(ty: &Type) -> Type {
    let mut work = vec![NormalizeTask::Type(ty)];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            NormalizeTask::Type(ty) => match ty {
                Type::Unit => output.push(Type::Unit),
                Type::Int => output.push(Type::Int),
                Type::I64 => output.push(Type::I64),
                Type::U64 => output.push(Type::U64),
                Type::Bool => output.push(Type::Bool),
                Type::Float => output.push(Type::Float),
                Type::Char => output.push(Type::Char),
                Type::Str => output.push(Type::Str),
                Type::Var(name) => output.push(Type::Var(*name)),
                Type::Exist(id) => output.push(Type::Exist(*id)),
                Type::Forall(name, body) => {
                    work.push(NormalizeTask::Forall(*name));
                    work.push(NormalizeTask::Type(body));
                }
                Type::RowForall(name, body) => {
                    work.push(NormalizeTask::RowForall(*name));
                    work.push(NormalizeTask::Type(body));
                }
                Type::Fun(params, row, result) => {
                    work.push(NormalizeTask::Fun(params.len(), normalize_row(row)));
                    work.push(NormalizeTask::Type(result));
                    work.extend(params.iter().rev().map(NormalizeTask::Type));
                }
                Type::Con(name, arguments) => {
                    work.push(NormalizeTask::Con(*name, arguments.len()));
                    work.extend(arguments.iter().rev().map(NormalizeTask::Type));
                }
                Type::App(head, argument) => {
                    work.push(NormalizeTask::App);
                    work.push(NormalizeTask::Type(argument));
                    work.push(NormalizeTask::Type(head));
                }
                Type::Tuple(fields) => {
                    work.push(NormalizeTask::Tuple(fields.len()));
                    work.extend(fields.iter().rev().map(NormalizeTask::Type));
                }
                Type::UnboxedTuple(fields) => {
                    work.push(NormalizeTask::UnboxedTuple(fields.len()));
                    work.extend(fields.iter().rev().map(NormalizeTask::Type));
                }
                Type::UnboxedRecord(fields) => {
                    work.push(NormalizeTask::UnboxedRecord(
                        fields.iter().map(|(name, _)| *name).collect(),
                    ));
                    work.extend(fields.iter().rev().map(|(_, ty)| NormalizeTask::Type(ty)));
                }
                Type::OrNull(inner) => {
                    work.push(NormalizeTask::OrNull);
                    work.push(NormalizeTask::Type(inner));
                }
                Type::Row(row) => output.push(Type::Row(normalize_row(row))),
                Type::Nat(value) => output.push(Type::Nat(*value)),
                Type::Coeffect(inner, row) => {
                    work.push(NormalizeTask::Coeffect(row.clone()));
                    work.push(NormalizeTask::Type(inner));
                }
            },
            NormalizeTask::Forall(name) => {
                let body = output.pop().expect("forall body is available");
                output.push(Type::Forall(name, Box::new(body)));
            }
            NormalizeTask::RowForall(name) => {
                let body = output.pop().expect("row-forall body is available");
                output.push(Type::RowForall(name, Box::new(body)));
            }
            NormalizeTask::Fun(param_count, row) => {
                let result = output.pop().expect("function result is available");
                let start = output.len() - param_count;
                let params = output.drain(start..).collect();
                output.push(Type::Fun(params, row, Box::new(result)));
            }
            NormalizeTask::Con(name, argument_count) => {
                let start = output.len() - argument_count;
                let arguments = output.drain(start..).collect();
                output.push(Type::Con(name, arguments));
            }
            NormalizeTask::App => {
                let argument = output.pop().expect("application argument is available");
                let head = output.pop().expect("application head is available");
                output.push(Type::app(head, argument));
            }
            NormalizeTask::Tuple(field_count) => {
                let start = output.len() - field_count;
                let fields = output.drain(start..).collect();
                output.push(Type::Tuple(fields));
            }
            NormalizeTask::UnboxedTuple(field_count) => {
                let start = output.len() - field_count;
                let fields = output.drain(start..).collect();
                output.push(Type::UnboxedTuple(fields));
            }
            NormalizeTask::UnboxedRecord(names) => {
                let start = output.len() - names.len();
                let fields = names.into_iter().zip(output.drain(start..)).collect();
                output.push(Type::UnboxedRecord(fields));
            }
            NormalizeTask::OrNull => {
                let inner = output.pop().expect("nullable inner type is available");
                output.push(Type::OrNull(Box::new(inner)));
            }
            NormalizeTask::Coeffect(row) => {
                let inner = output.pop().expect("coeffect inner type is available");
                output.push(Type::Coeffect(Box::new(inner), row));
            }
        }
    }
    output.pop().expect("normalization produces one type")
}
