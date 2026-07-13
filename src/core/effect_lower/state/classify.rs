//! Fold-uniformity check and per-clause classification: decide whether the
//! whole program streams a single op through fold/forward/control/take
//! handlers, and recognise each clause shape.

use std::collections::{BTreeMap, BTreeSet};

use super::super::evidence::resume_set;
use super::super::flow::{self, Loc};
use super::super::resume_use::ResumeUse;
use super::super::{EarlyExitMode, Lowerer, StateAnswerMode};
use crate::core::cbpv::{Comp, Core, CoreFn, HandleOp, Value};
use crate::sym::Sym;

use super::anf::{
    branch_resumes, is_id_return, is_id_transformer, is_state_transformer, strip_state, tail_if,
    AKind,
};

// Functions that force a thunk-valued parameter outside any handle: generic loop
// combinators (`repeat_while`, `for_range`) that drive their thunk at a fixed
// arity. A fold consumer forces its thunk inside a handle body, where the consumer
// lowering threads it, so it is not such a forcer. Passing one of these an
// effectful thunk is an un-threadable escape for the state path.
fn generic_forcers(fns: &[CoreFn]) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| {
            let ps: BTreeSet<Sym> = f.params.iter().copied().collect();
            forces_param_bare(&f.body, &ps, false)
        })
        .map(|f| f.name)
        .collect()
}

// Whether `c` forces one of `params` (or an ANF alias of one) while not inside a
// handle body. `params` grows with `return p to x` aliases as the walk descends.
fn forces_param_bare(c: &Comp, params: &BTreeSet<Sym>, in_handle: bool) -> bool {
    match c {
        Comp::App(f, _) => {
            (!in_handle && matches!(f.as_ref(), Comp::Force(Value::Var(v)) if params.contains(v)))
                || forces_param_bare(f, params, in_handle)
        }
        Comp::Bind(m, x, n) => {
            if forces_param_bare(m, params, in_handle) {
                return true;
            }
            // Track `return p to x` so a forced alias resolves back to the param.
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if params.contains(v) {
                    let mut ps = params.clone();
                    ps.insert(*x);
                    return forces_param_bare(n, &ps, in_handle);
                }
            }
            forces_param_bare(n, params, in_handle)
        }
        Comp::If(_, t, e) => {
            forces_param_bare(t, params, in_handle) || forces_param_bare(e, params, in_handle)
        }
        Comp::Case(_, arms) => arms
            .iter()
            .any(|(_, b)| forces_param_bare(b, params, in_handle)),
        Comp::Lam(_, b) | Comp::Mask(_, b) => forces_param_bare(b, params, in_handle),
        // A handle drives any thunk forced in its body/clauses through the consumer
        // lowering, which threads it, so those forces are not bare.
        Comp::Handle {
            body,
            ops,
            return_body,
            ..
        } => {
            forces_param_bare(body, params, true)
                || ops.iter().any(|o| forces_param_bare(&o.body, params, true))
                || return_body
                    .as_ref()
                    .is_some_and(|rb| forces_param_bare(rb, params, true))
        }
        _ => false,
    }
}

impl Lowerer {
    // The set of ops streamed through fold/forward/control/take handlers, or None
    // when the program is not fold-uniform: a mask, an escaping effectful thunk the
    // flow cannot track, an open (non-main) latent escape, no handles, an unhandled
    // op, or any handler that is not a fold consumer (with a state-transformer
    // return clause), a re-emitting forwarder, a control consumer, or a take. A
    // single handler may carry several fold clauses over distinct ops (a `State`
    // handler's `get`/`put`), each threading the one shared accumulator.
    pub(super) fn fold_uniform(&mut self, core: &Core) -> Option<BTreeSet<Sym>> {
        // The op set is over the functions actually being fused, not the global
        // table: under local monadification `core` is the fusable rest, whose
        // streamed ops coexist with the region's disjoint ops elsewhere.
        let mut ops = BTreeSet::new();
        for f in &core.fns {
            super::super::collect_ops(&f.body, &mut ops);
        }
        if ops.is_empty() {
            return None;
        }
        let handles = self.fusion_handles(core)?;
        self.state_a.clear();
        self.state_answer = StateAnswerMode::Accumulator;
        let mut consumed: BTreeSet<Sym> = BTreeSet::new();
        let mut folds = 0u32;
        let mut takes = 0u32;
        for h in &handles {
            let Comp::Handle {
                ops: clauses,
                return_var,
                return_body,
                ..
            } = h
            else {
                return None;
            };
            // A fold handle may have several clauses (e.g. `get` and `put`); a
            // forward/consumer/take handle is single-clause.
            if !clauses.is_empty()
                && clauses
                    .iter_with_use()
                    .all(|(c, ru)| Self::is_fold(c, ru).is_some())
            {
                // The return clause is a state transformer `\s -> body`; the
                // identity transformer is the writer special case, a get-style
                // `\s -> r` the general one (applied to the final accumulator).
                if !return_body.as_deref().is_some_and(is_state_transformer) {
                    return None;
                }
                if !return_body.as_deref().is_some_and(is_id_transformer) {
                    self.state_answer = StateAnswerMode::Producer;
                }
                for (clause, ru) in clauses.iter_with_use() {
                    let kind = Self::is_fold(clause, ru)?;
                    self.state_a.insert(clause.name, kind);
                    consumed.insert(clause.name);
                    folds += 1;
                }
                continue;
            }
            let [clause] = clauses.arms() else {
                return None;
            };
            let ru = clauses.resume_use(0);
            if self.is_take(clause) {
                // A `stake`: parameter-passing, re-emits, and drops the
                // continuation to stop early. Its return clause is ignored (the
                // consumer above discards the producer's return value).
                takes += 1;
            } else if self.is_forward(clause, ru) {
                if !is_id_return(*return_var, return_body.as_deref()) {
                    return None;
                }
            } else if self.is_consumer(clause, ru) {
                // A tail-resumptive control consumer (a `for`/print loop): unit
                // state, side effects in the clause, any return clause. Lets a
                // fold chain and a control chain over distinct streams fuse in
                // one program (mixed mode).
            } else {
                return None;
            }
            consumed.insert(clause.name);
        }
        // Every streamed op must be handled here, and there must be at least one
        // consuming handler. A pure forwarding/control chain is the evidence path's
        // (it runs before this), so reaching here it must have a fold or a take.
        if consumed != ops || folds + takes == 0 {
            return None;
        }
        // An effectful thunk passed to a callee the state path will not thread (not
        // latent in a fused op, e.g. a generic `repeat_while` loop combinator) would
        // be threaded with `ev@`/`st@` parameters its un-threaded force site cannot
        // supply. The evidence path threads such higher-order callees via the flow
        // param analysis; the state path does not, so fall back instead.
        let forcers = generic_forcers(&core.fns);
        if core.fns.iter().any(|f| {
            let loc: Loc = f
                .params
                .iter()
                .copied()
                .zip(self.flow.param[&f.name].iter().cloned())
                .collect();
            self.state_escapes(&f.body, &loc, &ops, &forcers)
        }) {
            return None;
        }
        self.early = if takes > 0 {
            EarlyExitMode::ShortCircuit
        } else {
            EarlyExitMode::Continue
        };
        Some(ops)
    }

    // Whether the body passes an effectful (fused-op-carrying) thunk to a callee
    // the state path will not thread its force site for. A producer (latent in a
    // fused op) threads it, as does a fold consumer (its body contains the handle
    // that drives the thunk). A generic combinator that just forces the thunk (a
    // `repeat_while` loop) does neither: under fusion the thunk gains `ev@`/`st@`
    // parameters its un-threaded force cannot supply, an arity mismatch, so the
    // program must fall back.
    fn state_escapes(
        &self,
        c: &Comp,
        loc: &Loc,
        ops: &BTreeSet<Sym>,
        forcers: &BTreeSet<Sym>,
    ) -> bool {
        match c {
            Comp::Call(g, args) => {
                forcers.contains(g)
                    && args.iter().any(|a| {
                        flow::value_sig(a, loc, &self.latent)
                            .iter()
                            .any(|m| ops.contains(&m.id))
                    })
            }
            Comp::Bind(m, x, n) => {
                self.state_escapes(m, loc, ops, forcers) || {
                    let mut loc2 = loc.clone();
                    loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                    self.state_escapes(n, &loc2, ops, forcers)
                }
            }
            Comp::If(_, t, e) => {
                self.state_escapes(t, loc, ops, forcers) || self.state_escapes(e, loc, ops, forcers)
            }
            Comp::Case(_, arms) => arms
                .iter()
                .any(|(_, b)| self.state_escapes(b, loc, ops, forcers)),
            Comp::Mask(_, b) | Comp::Lam(_, b) => self.state_escapes(b, loc, ops, forcers),
            Comp::Handle {
                body,
                ops: cl,
                return_body,
                ..
            } => {
                self.state_escapes(body, loc, ops, forcers)
                    || cl
                        .iter()
                        .any(|o| self.state_escapes(&o.body, loc, ops, forcers))
                    || return_body
                        .as_ref()
                        .is_some_and(|rb| self.state_escapes(rb, loc, ops, forcers))
            }
            _ => false,
        }
    }

    // A forwarding clause (smap/skeep): tail-resumptive and re-emits its own op,
    // so it threads the accumulator straight into the outer evidence. Tail
    // eligibility is the clause's stored classification, not a re-strip.
    pub(super) fn is_forward(&self, op: &HandleOp, ru: ResumeUse) -> bool {
        ru.tail && self.folds(&op.body, op.name)
    }

    // A control consumer (a `for`/print loop): tail-resumptive but does not
    // re-emit, so its clause is a pure side effect over a unit state that the
    // producer threads unchanged. Its return clause is run on the final state.
    pub(super) fn is_consumer(&self, op: &HandleOp, ru: ResumeUse) -> bool {
        ru.tail && !self.folds(&op.body, op.name)
    }

    // A `stake`-style early-terminating handler: a parameter-passing clause
    // `\(cnt) -> if c then { do op(..); resume(next) } else <drop>` that
    // re-emits and resumes on one branch but drops the continuation on the
    // other. The threaded state gains a `Step` wrapper so the producer can stop.
    pub(super) fn is_take(&self, op: &HandleOp) -> bool {
        let Comp::Return(Value::Thunk(t)) = &op.body else {
            return false;
        };
        let Comp::Lam(ps, inner) = t.as_ref() else {
            return false;
        };
        if ps.len() != 1 {
            return false;
        }
        let Some((b1, b2)) = tail_if(inner) else {
            return false;
        };
        let aliases = resume_set(op.resume);
        self.folds(inner, op.name) && branch_resumes(b1, &aliases) != branch_resumes(b2, &aliases)
    }

    // A fold clause: `op(p.., k) => return thunk { \acc. <..; k(A)(ns)> }`, a
    // state transformer whose tail resumes once and applies the resumption to the
    // new accumulator. Returns the resume value's [`AKind`] (`Unit` for a write,
    // `Acc` for a read), or None when the clause is not a fold. A tail-resumptive
    // clause (a forwarder or for/print consumer) is not a fold and disqualifies
    // the program.
    pub(super) fn is_fold(op: &HandleOp, ru: ResumeUse) -> Option<AKind> {
        if ru.tail {
            return None;
        }
        let Comp::Return(Value::Thunk(t)) = &op.body else {
            return None;
        };
        let Comp::Lam(ps, inner) = t.as_ref() else {
            return None;
        };
        if ps.len() != 1 {
            return None;
        }
        strip_state(inner, &resume_set(op.resume), ps[0]).map(|(_, kind)| kind)
    }

    // Whether running a computation performs any fused op (so the accumulator must
    // be threaded through it): a `do op`, a call to an op-latent function, or a
    // force of a thunk whose flow signature carries a fused op, in any executed
    // position. `latent` cannot see a force of a thunk-valued variable, so this
    // augments it with the flow `loc`.
    pub(super) fn produces(&self, c: &Comp, loc: &Loc, evs: &BTreeMap<Sym, Sym>) -> bool {
        match c {
            Comp::Do(o, _) => evs.contains_key(o),
            Comp::Call(g, _) => self
                .latent
                .get(g)
                .is_some_and(|s| s.iter().any(|m| evs.contains_key(&m.id))),
            Comp::App(f, _) => {
                matches!(f.as_ref(), Comp::Force(v)
                    if flow::value_sig(v, loc, &self.latent).iter().any(|m| evs.contains_key(&m.id)))
            }
            Comp::Bind(m, x, n) => {
                self.produces(m, loc, evs) || {
                    let mut loc2 = loc.clone();
                    loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                    self.produces(n, &loc2, evs)
                }
            }
            Comp::If(_, t, e) => self.produces(t, loc, evs) || self.produces(e, loc, evs),
            Comp::Case(_, arms) => arms.iter().any(|(_, b)| self.produces(b, loc, evs)),
            Comp::Mask(_, b) => self.produces(b, loc, evs),
            _ => false,
        }
    }

    // Whether a computation's result value coincides with the threaded
    // accumulator, so the state-mode loop (which yields the accumulator) yields the
    // right answer. True when the tail is a read `do op` (a read returns the
    // state), or a tail-call to a producer (compiled to return the accumulator,
    // checked transitively). A `return` of any value, a first-class application, or
    // a write tail is not coincident: the producer value differs from the state.
    pub(super) fn value_coincident(
        &self,
        c: &Comp,
        evs: &BTreeMap<Sym, Sym>,
        fns: &[CoreFn],
        visited: &mut std::collections::BTreeSet<Sym>,
    ) -> bool {
        match c {
            Comp::Do(o, _) => self.state_a.get(o) == Some(&AKind::Acc),
            Comp::Bind(_, _, n) => self.value_coincident(n, evs, fns, visited),
            Comp::If(_, t, e) => {
                self.value_coincident(t, evs, fns, visited)
                    && self.value_coincident(e, evs, fns, visited)
            }
            Comp::Case(_, arms) => arms
                .iter()
                .all(|(_, b)| self.value_coincident(b, evs, fns, visited)),
            Comp::Mask(_, b) => self.value_coincident(b, evs, fns, visited),
            Comp::Call(g, _) if self.produces(c, &Loc::new(), evs) => {
                // A recursive cycle is coinductively fine: its non-recursive tails
                // are checked on first visit.
                if !visited.insert(*g) {
                    return true;
                }
                fns.iter()
                    .find(|f| f.name == *g)
                    .is_some_and(|f| self.value_coincident(&f.body, evs, fns, visited))
            }
            _ => false,
        }
    }

    // Whether a computation is latent in any fused op (a producer body).
    pub(super) fn folds_any(&self, c: &Comp, evs: &BTreeMap<Sym, Sym>) -> bool {
        evs.keys().any(|o| self.folds(c, *o))
    }

    // Whether a computation is latent in the streamed op (a producer body).
    pub(super) fn folds(&self, c: &Comp, op: Sym) -> bool {
        let mut s = flow::Sig::new();
        super::super::latent(c, &self.latent, &mut s);
        s.iter().any(|m| m.id == op)
    }
}
