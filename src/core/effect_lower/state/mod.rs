//! Full stream fusion: pure state threading.
//!
//! A fold consumer handles `emit` by parameter passing: its clause returns a
//! state transformer `\(acc) -> resume(())(f(acc, x))`, so the whole handled
//! block is `Acc -> R` and resuming threads the accumulator forward. That is
//! not tail-resumptive (`resume` is applied, then its result applied again), so
//! the [`evidence`](super::evidence) path cannot take it. Instead this pass
//! compiles the chain to an explicit left fold: `emit`'s evidence becomes the
//! state transformer `\(x, acc) -> acc'`, and every producer (a function or
//! escaping thunk latent in `emit`) gains a trailing accumulator parameter `st@`
//! it threads through and returns. `do emit(x)` becomes `force(ev@<id>)(x, acc)`
//! yielding the new accumulator; a producer's unit return becomes `return acc`.
//! The handle collapses to a state transformer `\(acc0) -> <body threaded>` and
//! is applied to the initial accumulator at its call site. No `EOp` cell, no
//! continuation, no intermediate list: the producer loop is the fold loop.
//!
//! Escaping producer thunks (`srange(lo,hi) = \u -> srange_go(lo,hi)`) are
//! tracked exactly as in the [`evidence`](super::evidence) and [`flow`] paths:
//! the thunk gains `ev@<id>` and `st@` parameters and each force site appends
//! the active evidence and accumulator.
//!
//! Re-emitting transformers (`smap`/`skeep`) fuse too: such a handler is
//! tail-resumptive but re-performs `emit`, so it is itself a producer. Its
//! clause becomes the source's evidence `\(x.., acc) -> acc'`, a fresh name
//! shadowing the op for the source while the clause body re-emits into the
//! outer evidence with the accumulator threaded through. Producer -> smap ->
//! skeep -> fold collapses to one loop.
//!
//! A tail-resumptive control consumer (a `for`/print loop) fuses too, as a fold
//! over a unit state whose evidence runs the loop body for effect. With both
//! folds and control consumers admitted, a program mixing them over distinct
//! streams fuses in one pass (the evidence path runs first, so a pure-control
//! program never reaches here).
//!
//! `stake` (early termination) fuses via a `Step` protocol: when a take handler
//! is present (`early`), every producer threads `Step S` and checks it after
//! each emit, stopping on `SDone`. A take's evidence pairs its counter with the
//! downstream step `\(x, Step (dstep, cnt)) -> ...`, re-emits into `dstep` while
//! resuming, and yields `SDone` when it drops the continuation. Fold and control
//! evidences become `Step`-aware (`step_map`), and the seed/result wrap and
//! unwrap the `Step`.
//!
//! This pass fires only when `emit` is the sole effect op and every handler is a
//! fold consumer, a re-emitting forwarder, a control consumer, or a take, with
//! at least one fold or take. Anything else returns None and falls back to the
//! free monad.

use super::evidence::ev_name;
use super::flow::Loc;
use super::Lowerer;
use crate::core::cbpv::{Core, CoreFn};
use crate::sym::Sym;

mod anf;
mod classify;
mod consumer;
mod producer;
mod take;

// The threaded accumulator parameter every state-mode producer gains.
pub(super) const ST: &str = "st@";

impl Lowerer {
    // Lower a fold-uniform program by state threading, or None to fall back.
    pub(super) fn try_lower_state(&mut self, core: &Core) -> Option<Core> {
        let op = self.fold_uniform(core)?;
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
                .is_some_and(|s| s.iter().any(|m| m.id == op));
            let cf = if folds {
                // A producer: thread the accumulator from trailing parameters.
                let ev: Sym = ev_name(self.op_id(op).ok()?).into();
                let st: Sym = ST.into();
                let mut params = f.params.clone();
                params.push(ev);
                params.push(st);
                CoreFn {
                    name: f.name,
                    params,
                    body: self.thread_st(&f.body, ev, &loc, op, st)?,
                }
            } else {
                // A consumer (or plain code): rewrite the fold handles inside.
                CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    body: self.rewrite(&f.body, &loc, op)?,
                }
            };
            fns.push(cf);
        }
        Some(Core { fns })
    }
}
