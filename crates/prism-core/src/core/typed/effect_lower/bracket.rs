//! Pure brackets as plain sequencing.
//!
//! A handler with no operation clauses and no `finally` clause catches nothing
//! and owes nothing on exit, so it is `x <- body; return(x)` wherever it sits;
//! [`sequence_transparent`] rewrites every one so, before any rung sees it.
//!
//! A handler with no operation clauses and a `finally` clause is a bracket: it
//! catches nothing, so it is left either through its `return` clause or by an
//! operation of its body that a handler outside drops. In a program that
//! performs no operation at all the second path does not exist, and the bracket
//! is exactly `x <- body; r <- return(x); cleanup; r`. Rewriting it so lets such
//! a program classify pure rather than paying for a driver that has nothing to
//! drive.

use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use crate::types::ty::EffRow;

use super::super::specialize_support::Rewrite;
use super::super::{CompSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn};
use super::plan::raw_effects;
use super::{binder_var, union_effects};

/// The program with every handler that catches nothing and has no cleanup
/// sequenced as its body followed by its `return` clause.
#[must_use]
pub(super) fn sequence_transparent(fns: &[TypedCoreFn]) -> Vec<TypedCoreFn> {
    fns.iter()
        .map(|function| Transparent.function(function, &()))
        .collect()
}

struct Transparent;

impl Rewrite for Transparent {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, (): &()) -> TypedComp {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            finally_body: None,
            ops,
        } = comp.kind()
        else {
            return self.descend_comp(comp, &());
        };
        if !ops.arms().is_empty() {
            return self.descend_comp(comp, &());
        }
        let body = self.comp(body, &());
        match (return_binder, return_body) {
            (Some(binder), Some(return_body)) => {
                let return_body = self.comp(return_body, &());
                then(body, binder.clone(), return_body)
            }
            _ => body,
        }
    }
}

/// The program with every pure bracket sequenced, when that leaves it with no
/// raw effect; `None` keeps the program as written for the rungs that honour
/// the clause with an operation in flight.
#[must_use]
pub(super) fn sequence_pure(fns: &[TypedCoreFn]) -> Option<Vec<TypedCoreFn>> {
    let mut sequencer = Sequencer {
        fresh: Fresh::new(),
        found: false,
    };
    let rewritten: Vec<TypedCoreFn> = fns
        .iter()
        .map(|function| sequencer.function(function, &()))
        .collect();
    (sequencer.found && !rewritten.iter().any(|f| raw_effects(f.body()))).then_some(rewritten)
}

struct Sequencer {
    fresh: Fresh,
    found: bool,
}

impl Sequencer {
    fn binder(&mut self, ty: &CoreType) -> TypedBinder {
        TypedBinder::new(
            Sym::from(names::lowered("bracket", self.fresh.bump())),
            ty.clone(),
        )
    }
}

fn then(first: TypedComp, binder: TypedBinder, rest: TypedComp) -> TypedComp {
    let sig = CompSig::new(
        rest.sig().result().clone(),
        union_effects(first.sig().effects(), rest.sig().effects()),
    );
    TypedComp::new(
        sig,
        TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
    )
}

impl Rewrite for Sequencer {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, (): &()) -> TypedComp {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            finally_body: Some(cleanup),
            ops,
        } = comp.kind()
        else {
            return self.descend_comp(comp, &());
        };
        if !ops.arms().is_empty() {
            return self.descend_comp(comp, &());
        }
        self.found = true;
        let body = self.comp(body, &());
        let cleanup = self.comp(cleanup, &());
        let answered = match (return_binder, return_body) {
            (Some(binder), Some(return_body)) => {
                let return_body = self.comp(return_body, &());
                then(body, binder.clone(), return_body)
            }
            _ => body,
        };
        let answer = self.binder(answered.sig().result());
        let ignored = self.binder(cleanup.sig().result());
        let result = TypedComp::new(
            CompSig::new(answer.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(binder_var(&answer)),
        );
        let tail = then(cleanup, ignored, result);
        then(answered, answer, tail)
    }
}
