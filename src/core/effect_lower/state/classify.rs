//! Fold-uniformity check and per-clause classification: decide whether the
//! whole program streams a single op through fold/forward/control/take
//! handlers, and recognise each clause shape.

use super::super::evidence::{resume_set, strip_resume};
use super::super::flow::{self, Loc};
use super::super::Lowerer;
use crate::core::cbpv::{Comp, Core, HandleOp, Value};
use crate::sym::Sym;

use super::anf::{branch_resumes, is_id_return, is_id_transformer, strip_state, tail_if};

impl Lowerer {
    // The single op consumed by every handler as a fold, or None when the
    // program is not fold-uniform: a mask, more than one effect op, an escaping
    // effectful thunk the flow cannot track, an open (non-main) latent escape,
    // no handles, or any handler that is not a single-op fold consumer with an
    // identity return clause.
    pub(super) fn fold_uniform(&mut self, core: &Core) -> Option<Sym> {
        if self.op_ids.len() != 1 {
            return None;
        }
        let handles = self.fusion_handles(core)?;
        let mut op: Option<Sym> = None;
        let mut folds = 0u32;
        let mut takes = 0u32;
        for h in &handles {
            let Comp::Handle {
                ops,
                return_var,
                return_body,
                ..
            } = h
            else {
                return None;
            };
            let [clause] = ops.as_slice() else {
                return None;
            };
            if Self::is_fold(clause) {
                if !return_body.as_deref().is_some_and(is_id_transformer) {
                    return None;
                }
                folds += 1;
            } else if self.is_take(clause) {
                // A `stake`: parameter-passing, re-emits, and drops the
                // continuation to stop early. Its return clause is ignored (the
                // consumer above discards the producer's return value).
                takes += 1;
            } else if self.is_forward(clause) {
                if !is_id_return(*return_var, return_body.as_deref()) {
                    return None;
                }
            } else if self.is_consumer(clause) {
                // A tail-resumptive control consumer (a `for`/print loop): unit
                // state, side effects in the clause, any return clause. Lets a
                // fold chain and a control chain over distinct streams fuse in
                // one program (mixed mode).
            } else {
                return None;
            }
            match &op {
                Some(o) if *o != clause.name => return None,
                None => op = Some(clause.name),
                _ => {}
            }
        }
        // At least one consuming handler. A pure forwarding/control chain is the
        // evidence path's (it runs before this), so reaching here it must have a
        // fold or a take that the evidence path could not handle.
        if folds + takes == 0 {
            return None;
        }
        self.early = takes > 0;
        op
    }

    // A forwarding clause (smap/skeep): tail-resumptive and re-emits its own op,
    // so it threads the accumulator straight into the outer evidence.
    pub(super) fn is_forward(&self, op: &HandleOp) -> bool {
        strip_resume(&op.body, &resume_set(op.resume)).is_some() && self.folds(&op.body, op.name)
    }

    // A control consumer (a `for`/print loop): tail-resumptive but does not
    // re-emit, so its clause is a pure side effect over a unit state that the
    // producer threads unchanged. Its return clause is run on the final state.
    pub(super) fn is_consumer(&self, op: &HandleOp) -> bool {
        strip_resume(&op.body, &resume_set(op.resume)).is_some() && !self.folds(&op.body, op.name)
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

    // A fold clause: `op(p.., k) => return thunk { \acc. <..; k(())(ns)> }`, a
    // state transformer whose tail resumes once with unit and applies the
    // resumption to the new accumulator. A tail-resumptive clause (a forwarder
    // or for/print consumer) is not a fold and disqualifies the program.
    pub(super) fn is_fold(op: &HandleOp) -> bool {
        if strip_resume(&op.body, &resume_set(op.resume)).is_some() {
            return false;
        }
        let Comp::Return(Value::Thunk(t)) = &op.body else {
            return false;
        };
        let Comp::Lam(ps, inner) = t.as_ref() else {
            return false;
        };
        ps.len() == 1 && strip_state(inner, &resume_set(op.resume)).is_some()
    }

    // Whether running a computation performs the op (so the accumulator must be
    // threaded through it): a `do op`, a call to an op-latent function, or a
    // force of a thunk whose flow signature carries the op, in any executed
    // position. `latent` cannot see a force of a thunk-valued variable, so this
    // augments it with the flow `loc`.
    pub(super) fn produces(&self, c: &Comp, loc: &Loc, op: Sym) -> bool {
        match c {
            Comp::Do(o, _) => *o == op,
            Comp::Call(g, _) => self
                .latent
                .get(g)
                .is_some_and(|s| s.iter().any(|m| m.id == op)),
            Comp::App(f, _) => {
                matches!(f.as_ref(), Comp::Force(v)
                    if flow::value_sig(v, loc, &self.latent).iter().any(|m| m.id == op))
            }
            Comp::Bind(m, x, n) => {
                self.produces(m, loc, op) || {
                    let mut loc2 = loc.clone();
                    loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                    self.produces(n, &loc2, op)
                }
            }
            Comp::If(_, t, e) => self.produces(t, loc, op) || self.produces(e, loc, op),
            Comp::Case(_, arms) => arms.iter().any(|(_, b)| self.produces(b, loc, op)),
            Comp::Mask(_, b) => self.produces(b, loc, op),
            _ => false,
        }
    }

    // Whether a computation is latent in the streamed op (a producer body).
    pub(super) fn folds(&self, c: &Comp, op: Sym) -> bool {
        let mut s = flow::Sig::new();
        super::super::latent(c, &self.latent, &mut s);
        s.iter().any(|m| m.id == op)
    }
}
