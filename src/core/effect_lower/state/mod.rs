//! Full stream fusion: pure state threading.
//!
//! A fold consumer handles `emit` by parameter passing. Its clause returns a
//! state transformer `\(acc) -> resume(())(f(acc, x))`, making the handled block
//! `Acc -> R`. That is not tail-resumptive, so the
//! [`evidence`](super::evidence) path cannot take it. This pass instead compiles
//! the chain to an explicit left fold. `emit`'s evidence becomes `\(x, acc) ->
//! acc'`, and every producer (a function or escaping thunk latent in `emit`)
//! gains a trailing accumulator parameter `st@` it threads and returns. `do
//! emit(x)` becomes `force(ev@<id>)(x, acc)` and a unit return becomes `return
//! acc`. The handle collapses to `\(acc0) -> <body threaded>`, applied to the
//! initial accumulator at its call site. The producer loop is the fold loop,
//! with no `EOp` cell, continuation, or intermediate list.
//!
//! Escaping producer thunks (`srange(lo,hi) = \u -> srange_go(lo,hi)`) are
//! tracked as in the [`evidence`](super::evidence) and [`flow`] paths. The thunk
//! gains `ev@<id>` and `st@` parameters and each force site appends the active
//! evidence and accumulator.
//!
//! Re-emitting transformers (`smap`/`skeep`) fuse as producers, tail-resumptive
//! but re-performing `emit`. The clause becomes the source's evidence, a fresh
//! name shadowing the op while the body re-emits into the outer evidence with the
//! accumulator threaded through. Producer, smap, skeep, and fold collapse to one
//! loop.
//!
//! A tail-resumptive control consumer (a `for`/print loop) fuses as a fold over a
//! unit state whose evidence runs the body for effect. With both admitted, a
//! program mixing folds and control consumers over distinct streams fuses in one
//! pass. The evidence path runs first, so a pure-control program never reaches
//! here.
//!
//! `stake` (early termination) fuses via a `Step` protocol. With a take handler
//! present (`early`), every producer threads `Step S` and stops on `SDone` after
//! each emit. A take's evidence pairs its counter with the downstream step,
//! re-emits into `dstep` while resuming, and yields `SDone` when it drops the
//! continuation. Fold and control evidences become `Step`-aware (`step_map`) and
//! the seed and result wrap and unwrap the `Step`.
//!
//! This pass fires only when `emit` is the sole effect op and every handler is a
//! fold consumer, re-emitting forwarder, control consumer, or take, with at least
//! one fold or take. Anything else returns None and falls back to the free monad.

use std::collections::{BTreeMap, BTreeSet};

use super::flow::Loc;
use super::Lowerer;
use crate::core::cbpv::{Comp, Core, CoreFn};
use crate::names::ev;
use crate::sym::Sym;

mod anf;
mod classify;
mod consumer;
mod producer;
mod take;

pub(super) use anf::AKind;

// The threaded accumulator parameter every state-mode producer gains.
pub(super) const ST: &str = "st@";

impl Lowerer {
    // Lower a fold-uniform program by state threading, or None to fall back.
    pub(super) fn try_lower_state(&mut self, core: &Core) -> Option<Core> {
        let ops = self.fold_uniform(core)?;
        // The canonical evidence name per fused op; the producer/consumer threading
        // dispatches each `do op` to `evs[op]` and appends evidence in op-id order.
        let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
        for o in &ops {
            evs.insert(*o, ev(self.op_id(*o).ok()?).into());
        }
        // In state mode the threaded loop yields the accumulator but the answer is
        // the producer value, so fuse only when the two coincide: every fold
        // handle's body must be value-coincident (its result is a read or a
        // producer tail-call, not a `return` of a non-state value). Otherwise fall
        // back to the (correct) `@region`/free-monad path.
        if self.state_mode {
            for h in self.fusion_handles(core)? {
                let Comp::Handle {
                    body, ops: clauses, ..
                } = h
                else {
                    continue;
                };
                if !clauses.is_empty()
                    && clauses.iter().all(|c| Self::is_fold(c).is_some())
                    && !self.value_coincident(body, &evs, &core.fns, &mut BTreeSet::new())
                {
                    return None;
                }
            }
        }
        let mut fns = Vec::with_capacity(core.fns.len());
        for f in &core.fns {
            let loc: Loc = f
                .params
                .iter()
                .copied()
                .zip(self.flow.param[&f.name].iter().cloned())
                .collect();
            let folds = self
                .latent
                .get(&f.name)
                .is_some_and(|s| s.iter().any(|m| ops.contains(&m.id)));
            let cf = if folds {
                // A producer: thread the accumulator from trailing parameters, one
                // `ev@<id>` per fused op (in op-id order) plus the accumulator.
                let st: Sym = ST.into();
                let mut params = f.params.clone();
                params.extend(self.ev_order(&evs)?.into_iter().map(|o| evs[&o]));
                params.push(st);
                CoreFn {
                    name: f.name,
                    params,
                    body: self.thread_st(&f.body, &evs, &loc, st)?,
                }
            } else {
                // A consumer (or plain code): rewrite the fold handles inside.
                CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    body: self.rewrite(&f.body, &loc, &evs)?,
                }
            };
            fns.push(cf);
        }
        Some(Core { fns })
    }
}
