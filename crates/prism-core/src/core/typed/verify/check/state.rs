//! Lexical, diagnostic, and reuse-credit state for the typed Core checker.

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use prism_common::sym::Sym;
use prism_syntax::names;

use super::super::super::reuse::reuse_cell_capacity;
use super::super::super::violation::{RcSequenceFault, ReuseFault, Violation};
use super::super::super::{
    BinderErasure, CoreFnSig, CoreQuantifier, CoreType, TypedBinder, TypedPattern, TypedValue,
    TypedValueKind,
};
use super::super::{CoreViolation, VerifyEnv};
use super::phase::TypedCorePhase;
use super::Checker;

impl<'a, P: TypedCorePhase> Checker<'a, P> {
    pub(super) fn new(
        function: Sym,
        env: &'a VerifyEnv,
        globals: &'a BTreeMap<Sym, CoreFnSig>,
    ) -> Self {
        Self {
            function,
            env,
            globals,
            locals: BTreeMap::new(),
            thunk_depth: 0,
            token_uses: BTreeMap::new(),
            token_capacities: BTreeMap::new(),
            reuse_shells: BTreeMap::new(),
            allowed_types: BTreeSet::new(),
            allowed_rows: BTreeSet::new(),
            path: vec!["body".into()],
            violations: Vec::new(),
            phase: PhantomData,
        }
    }

    pub(super) fn fail(&mut self, kind: Violation) {
        self.violations.push(CoreViolation {
            function: self.function,
            path: self.path.join("."),
            kind,
        });
    }

    pub(super) fn at(&mut self, segment: impl Into<String>, f: impl FnOnce(&mut Self)) {
        self.path.push(segment.into());
        f(self);
        self.path.pop();
    }

    pub(super) fn bind(&mut self, binder: &TypedBinder) {
        if binder.erasure == BinderErasure::RcSequence {
            self.fail(Violation::RcSequence(
                RcSequenceFault::OutsideAdministrativeBind,
            ));
        }
        if binder.name() == Sym::new(names::RC_SEQUENCE_BINDER) {
            self.fail(Violation::RcSequence(
                RcSequenceFault::MissingErasureWitness,
            ));
        }
        self.check_core_type(binder.ty());
        self.locals
            .entry(binder.name())
            .or_default()
            .push((binder.ty().clone(), self.thunk_depth));
    }

    fn unbind(&mut self, name: Sym) {
        if let Some(stack) = self.locals.get_mut(&name) {
            stack.pop();
            if stack.is_empty() {
                self.locals.remove(&name);
            }
        }
    }

    pub(super) fn local(&self, name: Sym) -> Option<CoreType> {
        self.locals
            .get(&name)
            .and_then(|stack| stack.last())
            .map(|(ty, _)| ty.clone())
    }

    // Whether a reference to `name` crosses a suspension boundary: the binder
    // was introduced outside the thunk being checked, so at runtime the
    // reference reads a closure capture slot rather than a live binding.
    pub(super) fn captured(&self, name: Sym) -> bool {
        self.locals
            .get(&name)
            .and_then(|stack| stack.last())
            .is_some_and(|(_, depth)| *depth < self.thunk_depth)
    }

    pub(super) fn scoped_binders(&mut self, binders: &[&TypedBinder], f: impl FnOnce(&mut Self)) {
        let mut names = BTreeSet::new();
        for binder in binders {
            if !names.insert(binder.name()) {
                self.fail(Violation::DuplicateBinder {
                    name: binder.name(),
                });
            }
            self.bind(binder);
        }
        f(self);
        for binder in binders.iter().rev() {
            self.unbind(binder.name());
        }
    }

    pub(super) fn case_reuse_shell(
        &self,
        scrutinee: &TypedValue,
        pattern: &TypedPattern,
    ) -> Option<(Sym, ReuseShell)> {
        let capacity = reuse_cell_capacity(pattern, scrutinee.ty())?;
        let TypedValueKind::Var { name, .. } = scrutinee.kind() else {
            return None;
        };
        let binding_depth = self.locals.get(name)?.len();
        Some((
            *name,
            ReuseShell {
                scrutinee: scrutinee.clone(),
                binding_depth,
                capacity,
                remaining: 1,
            },
        ))
    }

    pub(super) fn claim_reuse_shell(&mut self, freed: &TypedValue) -> Result<usize, ReuseFault> {
        let TypedValueKind::Var { name, .. } = freed.kind() else {
            return Err(ReuseFault::ScrutineeNotActive);
        };
        let binding_depth = self.locals.get(name).map_or(0, Vec::len);
        let Some(shell) = self
            .reuse_shells
            .get_mut(name)
            .and_then(|shells| shells.last_mut())
            .filter(|shell| shell.scrutinee == *freed && shell.binding_depth == binding_depth)
        else {
            return Err(ReuseFault::ScrutineeNotActive);
        };
        if shell.remaining == 0 {
            return Err(ReuseFault::ScrutineeFreedTwice);
        }
        shell.remaining = 0;
        Ok(shell.capacity)
    }

    pub(super) fn scoped_quantifiers(
        &mut self,
        quantifiers: &[CoreQuantifier],
        f: impl FnOnce(&mut Self),
    ) {
        let old_types = self.allowed_types.clone();
        let old_rows = self.allowed_rows.clone();
        for quantifier in quantifiers {
            match quantifier {
                CoreQuantifier::Type(name) => {
                    self.allowed_types.insert(*name);
                }
                CoreQuantifier::Row(name) => {
                    self.allowed_rows.insert(*name);
                }
            }
        }
        f(self);
        self.allowed_types = old_types;
        self.allowed_rows = old_rows;
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct ReuseShell {
    scrutinee: TypedValue,
    pub(super) binding_depth: usize,
    capacity: usize,
    remaining: u8,
}

pub(super) fn pop_scoped<T>(scopes: &mut BTreeMap<Sym, Vec<T>>, name: Sym) -> Option<T> {
    let (value, empty) = {
        let stack = scopes.get_mut(&name)?;
        let value = stack.pop();
        (value, stack.is_empty())
    };
    if empty {
        scopes.remove(&name);
    }
    value
}

pub(super) fn merge_token_states(
    left: &BTreeMap<Sym, Vec<u8>>,
    right: &BTreeMap<Sym, Vec<u8>>,
) -> BTreeMap<Sym, Vec<u8>> {
    left.iter()
        .map(|(name, credits)| {
            (
                *name,
                credits
                    .iter()
                    .enumerate()
                    .map(|(index, credit)| {
                        (*credit).min(
                            right
                                .get(name)
                                .and_then(|other| other.get(index))
                                .copied()
                                .unwrap_or_default(),
                        )
                    })
                    .collect(),
            )
        })
        .collect()
}

pub(super) fn merge_shell_states(
    left: &BTreeMap<Sym, Vec<ReuseShell>>,
    right: &BTreeMap<Sym, Vec<ReuseShell>>,
) -> BTreeMap<Sym, Vec<ReuseShell>> {
    let mut merged = left.clone();
    for (name, shells) in &mut merged {
        for (index, shell) in shells.iter_mut().enumerate() {
            let other = right.get(name).and_then(|others| others.get(index));
            shell.remaining = other.map_or(0, |other| {
                if shell.scrutinee == other.scrutinee
                    && shell.binding_depth == other.binding_depth
                    && shell.capacity == other.capacity
                {
                    shell.remaining.min(other.remaining)
                } else {
                    0
                }
            });
        }
    }
    merged
}
