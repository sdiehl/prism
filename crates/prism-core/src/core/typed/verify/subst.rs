use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::build::lower_value_type;
use super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType};

#[must_use]
pub fn substitute_core_type(
    ty: &CoreType,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreType {
    match ty {
        CoreType::Source(ty) => lower_value_type(&substitute_type(ty, quantifiers, arguments)),
        CoreType::Thunk(signature) => {
            CoreType::Thunk(Box::new(substitute_sig(signature, quantifiers, arguments)))
        }
        CoreType::Function(signature) => CoreType::Function(Box::new(substitute_fn_sig(
            signature,
            quantifiers,
            arguments,
        ))),
        CoreType::Ref(inner) => CoreType::Ref(Box::new(substitute_core_type(
            inner,
            quantifiers,
            arguments,
        ))),
        CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(substitute_core_type(
            inner,
            quantifiers,
            arguments,
        ))),
        CoreType::Lowered(kind) => CoreType::Lowered(match kind {
            LoweredType::Word => LoweredType::Word,
            LoweredType::Eff(row) => LoweredType::Eff(substitute_row(row, quantifiers, arguments)),
            LoweredType::Queue(row) => {
                LoweredType::Queue(substitute_row(row, quantifiers, arguments))
            }
            LoweredType::QueueView(row) => {
                LoweredType::QueueView(substitute_row(row, quantifiers, arguments))
            }
        }),
    }
}

#[must_use]
pub fn substitute_fn_sig(
    signature: &CoreFnSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreFnSig {
    // Drop substitutions shadowed by the signature's own quantifiers FIRST. A
    // shadowed outer quantifier is not substituted into this inner scope, so its
    // argument must not drive capture-avoidance: otherwise an inner rank-2 binder
    // that deliberately reuses an outer quantifier's name (a state-fusion
    // producer thunk) is spuriously renamed out of sync with its references.
    let shadowed: BTreeSet<_> = signature
        .quantifiers()
        .iter()
        .map(|quantifier| match quantifier {
            CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => *name,
        })
        .collect();
    let (quantifiers, arguments): (Vec<_>, Vec<_>) = quantifiers
        .iter()
        .zip(arguments)
        .filter(|(quantifier, _)| match quantifier {
            CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => !shadowed.contains(name),
        })
        .map(|(quantifier, argument)| (quantifier.clone(), argument.clone()))
        .unzip();

    let mut inserted_types = BTreeSet::new();
    let mut inserted_rows = BTreeSet::new();
    for argument in &arguments {
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
    let mut signature = signature.clone();
    for index in 0..signature.quantifiers().len() {
        let quantifier = signature.quantifiers()[index].clone();
        let collision = match quantifier {
            CoreQuantifier::Type(name) => inserted_types.contains(&name),
            CoreQuantifier::Row(name) => inserted_rows.contains(&name),
        };
        if collision {
            let name = match quantifier {
                CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => name,
            };
            let mut suffix = 0;
            let fresh = loop {
                let candidate = Sym::from(format!("{name}$typedq{suffix}"));
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
            signature = rename_fn_quantifier(&signature, index, fresh);
        }
    }

    CoreFnSig::new(
        signature.quantifiers().to_vec(),
        signature
            .params()
            .iter()
            .map(|ty| substitute_core_type(ty, &quantifiers, &arguments))
            .collect(),
        substitute_sig(signature.body(), &quantifiers, &arguments),
    )
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
    match ty {
        CoreType::Source(ty) => CoreType::Source(match old {
            CoreQuantifier::Type(name) => ty.subst_var(*name, &Type::Var(fresh)),
            CoreQuantifier::Row(name) => ty.subst_row_var(*name, &EffRow::Var(fresh)),
        }),
        CoreType::Thunk(signature) => CoreType::Thunk(Box::new(CompSig::new(
            rename_bound_core(signature.result(), old, fresh),
            rename_bound_row(signature.effects(), old, fresh),
        ))),
        CoreType::Function(signature) => {
            let shadowed = signature.quantifiers().iter().any(|quantifier| {
                matches!(
                    (old, quantifier),
                    (CoreQuantifier::Type(a), CoreQuantifier::Type(b))
                        | (CoreQuantifier::Row(a), CoreQuantifier::Row(b)) if a == b
                )
            });
            if shadowed {
                CoreType::Function(signature.clone())
            } else {
                CoreType::Function(Box::new(CoreFnSig::new(
                    signature.quantifiers().to_vec(),
                    signature
                        .params()
                        .iter()
                        .map(|ty| rename_bound_core(ty, old, fresh))
                        .collect(),
                    CompSig::new(
                        rename_bound_core(signature.body().result(), old, fresh),
                        rename_bound_row(signature.body().effects(), old, fresh),
                    ),
                )))
            }
        }
        CoreType::Ref(inner) => CoreType::Ref(Box::new(rename_bound_core(inner, old, fresh))),
        CoreType::ReuseToken(inner) => {
            CoreType::ReuseToken(Box::new(rename_bound_core(inner, old, fresh)))
        }
        CoreType::Lowered(kind) => CoreType::Lowered(match kind {
            LoweredType::Word => LoweredType::Word,
            LoweredType::Eff(row) => LoweredType::Eff(rename_bound_row(row, old, fresh)),
            LoweredType::Queue(row) => LoweredType::Queue(rename_bound_row(row, old, fresh)),
            LoweredType::QueueView(row) => {
                LoweredType::QueueView(rename_bound_row(row, old, fresh))
            }
        }),
    }
}

fn rename_bound_row(row: &EffRow, old: &CoreQuantifier, fresh: Sym) -> EffRow {
    match old {
        CoreQuantifier::Type(name) => row.map_args(&|ty| ty.subst_var(*name, &Type::Var(fresh))),
        CoreQuantifier::Row(name) => row.subst_row_var(*name, &EffRow::Var(fresh)),
    }
}

#[must_use]
pub fn substitute_sig(
    signature: &CompSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CompSig {
    CompSig::new(
        substitute_core_type(signature.result(), quantifiers, arguments),
        substitute_row(signature.effects(), quantifiers, arguments),
    )
}

#[must_use]
pub fn substitute_type(
    ty: &Type,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Type {
    let (types, rows) = substitution_maps(quantifiers, arguments);
    let substituted = substitute_type_with(
        ty,
        &types,
        &rows,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
    );
    normalize_type_rows(&substituted)
}

#[must_use]
pub fn substitute_row(
    row: &EffRow,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> EffRow {
    let (types, rows) = substitution_maps(quantifiers, arguments);
    let substituted = substitute_row_with(
        row,
        &types,
        &rows,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
    );
    normalize_row(&substituted)
}

fn substitution_maps(
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> (BTreeMap<Sym, Type>, BTreeMap<Sym, EffRow>) {
    let mut types = BTreeMap::new();
    let mut rows = BTreeMap::new();
    for (quantifier, argument) in quantifiers.iter().zip(arguments) {
        match (quantifier, argument) {
            (CoreQuantifier::Type(name), CoreInstantiation::Type(argument)) => {
                types.insert(*name, argument.clone());
            }
            (CoreQuantifier::Row(name), CoreInstantiation::Row(argument)) => {
                rows.insert(*name, argument.clone());
            }
            _ => {}
        }
    }
    (types, rows)
}

fn substitute_type_with(
    ty: &Type,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    bound_types: &mut BTreeSet<Sym>,
    bound_rows: &mut BTreeSet<Sym>,
) -> Type {
    match ty {
        Type::Var(name) if !bound_types.contains(name) => {
            types.get(name).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::Forall(name, body) => {
            let inserted = bound_types.insert(*name);
            let body = substitute_type_with(body, types, rows, bound_types, bound_rows);
            if inserted {
                bound_types.remove(name);
            }
            Type::Forall(*name, Box::new(body))
        }
        Type::RowForall(name, body) => {
            let inserted = bound_rows.insert(*name);
            let body = substitute_type_with(body, types, rows, bound_types, bound_rows);
            if inserted {
                bound_rows.remove(name);
            }
            Type::RowForall(*name, Box::new(body))
        }
        Type::Fun(params, effects, result) => Type::Fun(
            params
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
            substitute_row_with(effects, types, rows, bound_types, bound_rows),
            Box::new(substitute_type_with(
                result,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
        ),
        Type::Con(name, arguments) => Type::Con(
            *name,
            arguments
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::App(head, argument) => Type::app(
            substitute_type_with(head, types, rows, bound_types, bound_rows),
            substitute_type_with(argument, types, rows, bound_types, bound_rows),
        ),
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::UnboxedTuple(fields) => Type::UnboxedTuple(
            fields
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::UnboxedRecord(fields) => Type::UnboxedRecord(
            fields
                .iter()
                .map(|(name, ty)| {
                    (
                        *name,
                        substitute_type_with(ty, types, rows, bound_types, bound_rows),
                    )
                })
                .collect(),
        ),
        Type::OrNull(inner) => Type::OrNull(Box::new(substitute_type_with(
            inner,
            types,
            rows,
            bound_types,
            bound_rows,
        ))),
        Type::Row(row) => Type::Row(substitute_row_with(
            row,
            types,
            rows,
            bound_types,
            bound_rows,
        )),
        Type::Coeffect(inner, row) => Type::Coeffect(
            Box::new(substitute_type_with(
                inner,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
            row.clone(),
        ),
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
        | Type::Nat(_) => ty.clone(),
    }
}

fn substitute_row_with(
    row: &EffRow,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    bound_types: &mut BTreeSet<Sym>,
    bound_rows: &mut BTreeSet<Sym>,
) -> EffRow {
    match row {
        EffRow::Var(name) if !bound_rows.contains(name) => {
            rows.get(name).cloned().unwrap_or_else(|| row.clone())
        }
        EffRow::Extend(label, rest) => EffRow::Extend(
            Label {
                name: label.name,
                args: label
                    .args
                    .iter()
                    .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                    .collect(),
            },
            Box::new(substitute_row_with(
                rest,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
        ),
        EffRow::Empty | EffRow::Var(_) | EffRow::Exist(_) => row.clone(),
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
        row.tail().clone(),
    )
}

fn normalize_type_rows(ty: &Type) -> Type {
    match ty {
        Type::Forall(name, body) => Type::Forall(*name, Box::new(normalize_type_rows(body))),
        Type::RowForall(name, body) => Type::RowForall(*name, Box::new(normalize_type_rows(body))),
        Type::Fun(params, row, result) => Type::Fun(
            params.iter().map(normalize_type_rows).collect(),
            normalize_row(row),
            Box::new(normalize_type_rows(result)),
        ),
        Type::Con(name, arguments) => {
            Type::Con(*name, arguments.iter().map(normalize_type_rows).collect())
        }
        Type::App(head, argument) => {
            Type::app(normalize_type_rows(head), normalize_type_rows(argument))
        }
        Type::Tuple(fields) => Type::Tuple(fields.iter().map(normalize_type_rows).collect()),
        Type::UnboxedTuple(fields) => {
            Type::UnboxedTuple(fields.iter().map(normalize_type_rows).collect())
        }
        Type::UnboxedRecord(fields) => Type::UnboxedRecord(
            fields
                .iter()
                .map(|(name, ty)| (*name, normalize_type_rows(ty)))
                .collect(),
        ),
        Type::OrNull(inner) => Type::OrNull(Box::new(normalize_type_rows(inner))),
        Type::Row(row) => Type::Row(normalize_row(row)),
        Type::Coeffect(inner, row) => {
            Type::Coeffect(Box::new(normalize_type_rows(inner)), row.clone())
        }
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
        | Type::Nat(_) => ty.clone(),
    }
}
