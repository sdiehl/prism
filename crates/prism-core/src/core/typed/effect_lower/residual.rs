//! Ambient direct effects retained around the reified operation runtime.

use std::collections::{BTreeMap, BTreeSet};

use crate::types::ty::{EffRow, Label};
use prism_common::sym::Sym;
use prism_syntax::names;

use super::super::traverse::Visit;
use super::super::verify::VerifyEnv;
use super::super::{TypedComp, TypedCoreFn};
use super::evidence::OpIds;
use super::plan::collect_calls;

/// The direct effects retained by each declaration around its reified
/// operation runtime.
#[derive(Debug)]
pub struct ResidualRows(BTreeMap<Sym, EffRow>);

pub trait Rows {
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

/// Collect each declaration's direct-effect row.
///
/// Algebraic operations become `EOp` cells and leave these rows; intrinsic IO
/// and any other direct effect remain observable while the runtime drives those
/// cells.
///
/// # Errors
/// A message naming an operation that has no typed signature in `env`, which
/// leaves its effect label unattributable.
pub fn plan(
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
        let mut collector = LabelCollector {
            reified: &reified,
            labels: BTreeSet::new(),
        };
        collector.walk_comp(function.body());
        labels.insert(function.name(), collector.labels);
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

struct LabelCollector<'a> {
    reified: &'a BTreeSet<Sym>,
    labels: BTreeSet<Label>,
}

impl Visit for LabelCollector<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        self.labels.extend(
            comp.sig()
                .effects()
                .labels()
                .into_iter()
                .filter(|label| !self.reified.contains(&label.name))
                .cloned(),
        );
        true
    }
}
