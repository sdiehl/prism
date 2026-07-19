//! Neutral erased-Core effect analysis used before typed lowering.
//!
//! This computes the latent operation set used to reconcile checker and Core
//! facts. It does not choose or execute a lowering strategy.

use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{Comp, Core, HandleOp, Value};
use crate::sym::Sym;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MaskedOp {
    id: Sym,
    depth: u32,
}

type Latent = BTreeMap<Sym, BTreeSet<MaskedOp>>;

/// Per-function effect operations that remain latent in its erased Core body.
#[must_use]
pub(crate) fn latent_ops(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
    latent_map(core)
        .into_iter()
        .map(|(function, operations)| {
            (
                function,
                operations
                    .into_iter()
                    .map(|operation| operation.id)
                    .collect(),
            )
        })
        .collect()
}

fn latent_map(core: &Core) -> Latent {
    let seed = core
        .fns
        .iter()
        .map(|function| (function.name, BTreeSet::new()))
        .collect();
    let bodies: BTreeMap<Sym, &Comp> = core
        .fns
        .iter()
        .map(|function| (function.name, &function.body))
        .collect();
    crate::util::fixpoint::least_fixpoint(seed, |name, current| {
        let mut operations = BTreeSet::new();
        latent(bodies[name], current, &mut operations);
        operations
    })
}

fn latent(comp: &Comp, functions: &Latent, operations: &mut BTreeSet<MaskedOp>) {
    match comp {
        Comp::Do(operation, _) => {
            operations.insert(MaskedOp {
                id: *operation,
                depth: 0,
            });
        }
        Comp::Call(function, _) => {
            if let Some(callee) = functions.get(function) {
                operations.extend(callee.iter().copied());
            }
        }
        Comp::Bind(bound, _, body) => {
            latent(bound, functions, operations);
            latent(body, functions, operations);
        }
        Comp::If(_, then_branch, else_branch) => {
            latent(then_branch, functions, operations);
            latent(else_branch, functions, operations);
        }
        Comp::Case(_, arms) => {
            for (_, body) in arms {
                latent(body, functions, operations);
            }
        }
        Comp::App(function, _) => latent(function, functions, operations),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => handle_escapes(body, return_body.as_deref(), ops, functions, operations),
        Comp::Mask(masked, body) => {
            let mut inner = BTreeSet::new();
            latent(body, functions, &mut inner);
            operations.extend(inner.into_iter().map(|operation| {
                if masked.contains(&operation.id) {
                    MaskedOp {
                        id: operation.id,
                        depth: operation.depth + 1,
                    }
                } else {
                    operation
                }
            }));
        }
        _ => {}
    }
}

fn handle_escapes(
    body: &Comp,
    return_body: Option<&Comp>,
    clauses: &[HandleOp],
    functions: &Latent,
    operations: &mut BTreeSet<MaskedOp>,
) {
    let mut inner = BTreeSet::new();
    latent(body, functions, &mut inner);
    for clause in clauses {
        inner.remove(&MaskedOp {
            id: clause.name,
            depth: 0,
        });
    }
    operations.extend(inner.into_iter().map(|operation| {
        if clauses.iter().any(|clause| clause.name == operation.id) {
            MaskedOp {
                id: operation.id,
                depth: operation.depth - 1,
            }
        } else {
            operation
        }
    }));
    if let Some(return_body) = return_body {
        latent(return_body, functions, operations);
    }
    for clause in clauses {
        match &clause.body {
            Comp::Return(Value::Thunk(thunk)) => {
                let inner = if let Comp::Lam(_, body) = thunk.as_ref() {
                    body
                } else {
                    thunk
                };
                latent(inner, functions, operations);
            }
            _ => latent(&clause.body, functions, operations),
        }
    }
}
