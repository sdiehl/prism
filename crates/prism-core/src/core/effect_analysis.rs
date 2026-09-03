//! Neutral erased-Core effect analysis used before typed lowering.
//!
//! This computes the latent operation set used to reconcile checker and Core
//! facts. It does not choose or execute a lowering strategy.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use crate::core::cbpv::{Comp, Core, HandleOp, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MaskedOp {
    id: Sym,
    depth: u32,
}

type Latent = BTreeMap<Sym, BTreeSet<MaskedOp>>;

/// Per-function effect operations that remain latent in its erased Core body.
#[must_use]
pub fn latent_ops(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
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
    prism_common::fixpoint::least_fixpoint(seed, |name, current| latent(bodies[name], current))
}

enum Frame<'a> {
    Enter(&'a Comp),
    Merge {
        result_mark: usize,
    },
    Mask {
        masked: &'a [Sym],
        result_mark: usize,
    },
    Handle {
        clauses: &'a [HandleOp],
        result_mark: usize,
    },
}

fn clause_effect_body(clause: &HandleOp) -> &Comp {
    match &clause.body {
        Comp::Return(Value::Thunk(thunk)) => match thunk.as_ref() {
            Comp::Lam(_, body) => body,
            thunk => thunk,
        },
        body => body,
    }
}

fn latent(comp: &Comp, functions: &Latent) -> BTreeSet<MaskedOp> {
    let mut frames = vec![Frame::Enter(comp)];
    let mut results = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Enter(comp) => match comp {
                Comp::Do(operation, _) => {
                    results.push(BTreeSet::from([MaskedOp {
                        id: *operation,
                        depth: 0,
                    }]));
                }
                Comp::Call(function, _) => {
                    results.push(functions.get(function).cloned().unwrap_or_default());
                }
                Comp::Bind(bound, _, body) => {
                    frames.push(Frame::Merge {
                        result_mark: results.len(),
                    });
                    frames.push(Frame::Enter(body));
                    frames.push(Frame::Enter(bound));
                }
                Comp::If(_, then_branch, else_branch) => {
                    frames.push(Frame::Merge {
                        result_mark: results.len(),
                    });
                    frames.push(Frame::Enter(else_branch));
                    frames.push(Frame::Enter(then_branch));
                }
                Comp::Case(_, arms) => {
                    frames.push(Frame::Merge {
                        result_mark: results.len(),
                    });
                    for (_, body) in arms.iter().rev() {
                        frames.push(Frame::Enter(body));
                    }
                }
                Comp::App(function, _) => frames.push(Frame::Enter(function)),
                Comp::Handle {
                    body,
                    return_body,
                    ops,
                    ..
                } => {
                    frames.push(Frame::Handle {
                        clauses: ops,
                        result_mark: results.len(),
                    });
                    for clause in ops.iter().rev() {
                        frames.push(Frame::Enter(clause_effect_body(clause)));
                    }
                    if let Some(return_body) = return_body {
                        frames.push(Frame::Enter(return_body));
                    }
                    frames.push(Frame::Enter(body));
                }
                Comp::Mask(masked, body) => {
                    frames.push(Frame::Mask {
                        masked,
                        result_mark: results.len(),
                    });
                    frames.push(Frame::Enter(body));
                }
                _ => results.push(BTreeSet::new()),
            },
            Frame::Merge { result_mark } => {
                let mut merged = BTreeSet::new();
                for operations in results.drain(result_mark..) {
                    merged.extend(operations);
                }
                results.push(merged);
            }
            Frame::Mask {
                masked,
                result_mark,
            } => {
                let inner = results.pop().expect("mask effect result follows its body");
                debug_assert_eq!(results.len(), result_mark);
                results.push(
                    inner
                        .into_iter()
                        .map(|operation| {
                            if masked.contains(&operation.id) {
                                MaskedOp {
                                    id: operation.id,
                                    depth: operation.depth + 1,
                                }
                            } else {
                                operation
                            }
                        })
                        .collect(),
                );
            }
            Frame::Handle {
                clauses,
                result_mark,
            } => {
                let mut nested = results.drain(result_mark..);
                let mut body = nested
                    .next()
                    .expect("handler effect results start with its body");
                for clause in clauses {
                    body.remove(&MaskedOp {
                        id: clause.name,
                        depth: 0,
                    });
                }
                let mut escaped: BTreeSet<_> = body
                    .into_iter()
                    .map(|operation| {
                        if clauses.iter().any(|clause| clause.name == operation.id) {
                            MaskedOp {
                                id: operation.id,
                                depth: operation.depth - 1,
                            }
                        } else {
                            operation
                        }
                    })
                    .collect();
                for operations in nested {
                    escaped.extend(operations);
                }
                results.push(escaped);
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    results
        .pop()
        .expect("effect traversal produces one root result")
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;
    use crate::core::cbpv::{CheckedHandler, CoreFn};

    const DEEP_EFFECT_LAYER_COUNT: usize = 5_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    #[test]
    fn latent_effects_handle_deep_masks_and_handlers_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-latent-effects".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let operation = Sym::new("handled_operation");
                let buried_operation = Sym::new("buried_operation");
                let clause_operation = Sym::new("clause_operation");
                let return_operation = Sym::new("return_operation");
                let callee_operation = Sym::new("callee_operation");
                let callee = Sym::new("effect_callee");
                let function = Sym::new("deep_effects");

                let handler = CheckedHandler::new(vec![HandleOp {
                    name: operation,
                    params: Vec::new(),
                    resume: Sym::new("resume"),
                    body: Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                        Vec::new(),
                        Box::new(Comp::Do(clause_operation, Vec::new())),
                    )))),
                }])
                .expect("the deep fixture has one handler clause");
                let mut body = Comp::Bind(
                    Box::new(Comp::Do(operation, Vec::new())),
                    Sym::new("_handled"),
                    Box::new(Comp::Bind(
                        Box::new(Comp::Do(buried_operation, Vec::new())),
                        Sym::new("_buried"),
                        Box::new(Comp::Call(callee, Vec::new())),
                    )),
                );
                for _ in 0..DEEP_EFFECT_LAYER_COUNT {
                    body = Comp::If(
                        Value::Bool(true),
                        Box::new(body),
                        Box::new(Comp::Return(Value::Unit)),
                    );
                    body = Comp::Mask(vec![operation, buried_operation], Box::new(body));
                    body = Comp::Handle {
                        body: Box::new(body),
                        return_var: Some(Sym::new("returned")),
                        return_body: Some(Box::new(Comp::Do(return_operation, Vec::new()))),
                        ops: handler.clone(),
                    };
                    body = Comp::Bind(
                        Box::new(Comp::Return(Value::Unit)),
                        Sym::new("_"),
                        Box::new(body),
                    );
                }
                let core = Core {
                    fns: vec![
                        CoreFn {
                            name: callee,
                            params: Vec::new(),
                            body: Comp::Do(callee_operation, Vec::new()),
                            dict_arity: 0,
                        },
                        CoreFn {
                            name: function,
                            params: Vec::new(),
                            body,
                            dict_arity: 0,
                        },
                    ],
                };

                let masked_depth = u32::try_from(DEEP_EFFECT_LAYER_COUNT)
                    .expect("the test depth fits the analysis counter");
                assert_eq!(
                    latent_map(&core)[&function],
                    BTreeSet::from([
                        MaskedOp {
                            id: operation,
                            depth: 0,
                        },
                        MaskedOp {
                            id: buried_operation,
                            depth: masked_depth,
                        },
                        MaskedOp {
                            id: clause_operation,
                            depth: 0,
                        },
                        MaskedOp {
                            id: return_operation,
                            depth: 0,
                        },
                        MaskedOp {
                            id: callee_operation,
                            depth: 0,
                        },
                    ])
                );
                assert_eq!(
                    latent_ops(&core)[&function],
                    BTreeSet::from([
                        operation,
                        buried_operation,
                        clause_operation,
                        return_operation,
                        callee_operation,
                    ])
                );
                mem::forget(core);
            })
            .expect("spawn deep latent-effect test")
            .join()
            .expect("deep latent-effect test panicked");
    }
}
