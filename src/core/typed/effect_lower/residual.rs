//! Ambient direct effects retained around the reified operation runtime.

use std::collections::{BTreeMap, BTreeSet};

use crate::names;
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label};

use super::super::verify::VerifyEnv;
use super::super::{TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind};
use super::evidence::OpIds;
use super::walk::{each_subcomp, each_value};

/// The direct effects retained by each declaration around its reified
/// operation runtime.
pub(super) struct ResidualRows(BTreeMap<Sym, EffRow>);

pub(super) trait Rows {
    fn row(&self, function: Sym) -> Option<EffRow>;
}

impl Rows for ResidualRows {
    fn row(&self, function: Sym) -> Option<EffRow> {
        self.0.get(&function).cloned()
    }
}

impl Rows for EffRow {
    fn row(&self, _function: Sym) -> Option<EffRow> {
        Some(self.clone())
    }
}

/// Collect each declaration's direct-effect row. Algebraic operations become
/// `EOp` cells and leave these rows; intrinsic IO and any other direct effect
/// remain observable while the runtime drives those cells.
pub(super) fn plan(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    env: &VerifyEnv,
) -> Result<ResidualRows, String> {
    let reified: BTreeSet<Sym> = ops
        .iter()
        .map(|(operation, _)| {
            env.operation(operation)
                .map(|signature| signature.effect().name)
                .ok_or_else(|| format!("effect operation `{operation}` has no typed signature"))
        })
        .collect::<Result<_, _>>()?;
    let mut labels = BTreeMap::<Sym, BTreeSet<Label>>::new();
    let mut calls = BTreeMap::<Sym, BTreeSet<Sym>>::new();
    for function in functions {
        let mut rows = Vec::new();
        collect_comp(function.body(), &mut rows);
        labels.insert(
            function.name(),
            rows.iter()
                .flat_map(|row| row.labels().into_iter().cloned())
                .filter(|label| !reified.contains(&label.name))
                .collect(),
        );
        let mut callees = BTreeSet::new();
        collect_calls(function.body(), &mut callees);
        calls.insert(function.name(), callees);
    }
    loop {
        let mut changed = false;
        for function in functions {
            let inherited: Vec<Label> = calls[&function.name()]
                .iter()
                .filter_map(|callee| labels.get(callee))
                .flat_map(BTreeSet::iter)
                .cloned()
                .collect();
            let current = labels.get_mut(&function.name()).ok_or_else(|| {
                format!("function `{}` has no residual-row plan", function.name())
            })?;
            let before = current.len();
            current.extend(inherited);
            changed |= current.len() != before;
        }
        if !changed {
            break;
        }
    }

    let mut planned = BTreeMap::new();
    for function in functions {
        planned.insert(
            function.name(),
            EffRow::canonical(
                labels.remove(&function.name()).unwrap_or_default(),
                EffRow::Var(Sym::from(names::FREE_MONAD_ROW)),
            ),
        );
    }
    Ok(ResidualRows(planned))
}

fn collect_calls(comp: &TypedComp, calls: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = comp.kind() {
        calls.insert(*callee);
    }
    each_value(comp, &mut |value| collect_value_calls(value, calls));
    each_subcomp(comp, &mut |child| collect_calls(child, calls));
}

fn collect_value_calls(value: &TypedValue, calls: &mut BTreeSet<Sym>) {
    match &value.kind {
        TypedValueKind::Thunk(body) => collect_calls(body, calls),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => collect_value_calls(inner, calls),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_value_calls(field, calls);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_value_calls(field, calls);
            }
        }
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

fn collect_comp(comp: &TypedComp, rows: &mut Vec<EffRow>) {
    rows.push(comp.sig().effects().clone());
    each_value(comp, &mut |value| collect_value(value, rows));
    each_subcomp(comp, &mut |child| collect_comp(child, rows));
}

fn collect_value(value: &TypedValue, rows: &mut Vec<EffRow>) {
    match &value.kind {
        TypedValueKind::Thunk(body) => collect_comp(body, rows),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => collect_value(inner, rows),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_value(field, rows);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_value(field, rows);
            }
        }
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
