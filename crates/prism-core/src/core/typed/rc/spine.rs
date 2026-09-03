//! State for the linear right-spine ownership pass.

use std::collections::{BTreeMap, VecDeque};

use prism_common::sym::Sym;

use super::super::specialize_support::{free_comp_var_witnesses, free_comp_vars};
use super::super::{CompSig, TypedBinder, TypedComp, TypedCompKind, TypedValue};
use super::scope::ScopeUndo;
use super::{referenced_binding, Set};

pub(super) struct SpineStep {
    pub(super) sig: CompSig,
    pub(super) first: Option<TypedComp>,
    pub(super) binder: TypedBinder,
    pub(super) first_refs: BTreeMap<Sym, TypedValue>,
    pub(super) prev_count: u32,
}

pub(super) struct SpineLevel {
    pub(super) sig: CompSig,
    pub(super) binder: TypedBinder,
    pub(super) first: TypedComp,
    pub(super) shared_ops: Vec<TypedValue>,
    pub(super) dead_ops: Vec<TypedValue>,
}

pub(super) struct SpineState {
    pub(super) steps: VecDeque<SpineStep>,
    pub(super) tail: Option<TypedComp>,
    pub(super) live: BTreeMap<Sym, u32>,
    pub(super) owned: Set,
    pub(super) borrowed: Set,
    pub(super) undo: ScopeUndo,
    pub(super) levels: Vec<SpineLevel>,
}

impl SpineState {
    pub(super) fn new(mut comp: TypedComp, owned: Set, borrowed: Set) -> Self {
        let mut steps = VecDeque::new();
        loop {
            let TypedComp { sig, kind } = comp;
            match kind {
                TypedCompKind::Bind(first, binder, rest) => {
                    steps.push_back(SpineStep {
                        sig,
                        first_refs: free_comp_var_witnesses(&first),
                        first: Some(*first),
                        binder,
                        prev_count: 0,
                    });
                    comp = *rest;
                }
                kind => {
                    comp = TypedComp::new(sig, kind);
                    break;
                }
            }
        }

        let mut live: BTreeMap<Sym, u32> = free_comp_vars(&comp)
            .into_iter()
            .map(|name| (name, 1))
            .collect();
        for step in steps.iter_mut().rev() {
            step.prev_count = live.remove(&step.binder.name).unwrap_or(0);
            for name in step.first_refs.keys() {
                *live.entry(*name).or_insert(0) += 1;
            }
        }
        Self {
            steps,
            tail: Some(comp),
            live,
            owned,
            borrowed,
            undo: Vec::new(),
            levels: Vec::new(),
        }
    }

    pub(super) fn remove_first_contribution(&mut self, first_refs: &BTreeMap<Sym, TypedValue>) {
        for name in first_refs.keys() {
            match self.live.get_mut(name) {
                Some(count) if *count > 1 => *count -= 1,
                Some(_) => {
                    self.live.remove(name);
                }
                None => {}
            }
        }
    }
}

pub(super) fn alias_source(comp: &TypedComp) -> Option<Sym> {
    match &comp.kind {
        TypedCompKind::Return(value) => referenced_binding(value),
        _ => None,
    }
}
