//! Producer-side accumulator threading: walk a producer body, fold each op
//! head into the active evidence, and re-emit forwarding handles under fresh
//! shadowing evidence.

use super::super::evidence::{resume_set, strip_resume};
use super::super::flow::{self, Loc};
use super::super::Lowerer;
use crate::core::cbpv::{Comp, Value};
use crate::core::fv;
use crate::sym::Sym;

use super::anf::is_id_return;

impl Lowerer {
    // Thread the accumulator through a producer body. `ev` is the evidence name
    // active for the op here (a forwarding handler shadows it for its source);
    // `st` names the accumulator currently in scope. The result is a computation
    // returning the final accumulator. A producer head (`do op`, a producer
    // call, or a force of an op-carrying thunk) folds the accumulator; a
    // forwarding handle re-emits under fresh evidence; any other tail returns it.
    pub(super) fn thread_st(
        &mut self,
        c: &Comp,
        ev: Sym,
        loc: &Loc,
        op: Sym,
        st: Sym,
    ) -> Option<Comp> {
        Some(match c {
            // `let g = handle s(()) with <stake>; g(n)`: a parameter-passing
            // early-terminating handler. Lower it via the Step protocol.
            Comp::Bind(m, g, rest) if self.take_seed(m, *g, rest).is_some() => {
                let seed = self.take_seed(m, *g, rest)?;
                self.thread_take(m, &seed, ev, loc, op, st)?
            }
            // A bind whose head performs the op: thread the accumulator through
            // it and rebind. The op's unit result is bound only if the tail
            // still needs it.
            Comp::Bind(m, x, n) if self.produces(m, loc, op) => {
                let st2 = self.fresh("st");
                let tm = self.thread_st(m, ev, loc, op, st)?;
                let mut loc2 = loc.clone();
                loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                let tn = self.thread_st(n, ev, &loc2, op, st2)?;
                let tn = if fv::comp(n).contains(x) {
                    Comp::Bind(Box::new(Comp::Return(Value::Unit)), *x, Box::new(tn))
                } else {
                    tn
                };
                // In early mode the producer stops once a stake yields SDone.
                let tn = if self.early {
                    self.step_guard(st2, tn)
                } else {
                    tn
                };
                Comp::Bind(Box::new(tm), st2, Box::new(tn))
            }
            // Pure head: the accumulator passes through.
            Comp::Bind(m, x, n) => {
                let mut loc2 = loc.clone();
                loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                Comp::Bind(
                    Box::new(self.rewrite(m, loc, op)?),
                    *x,
                    Box::new(self.thread_st(n, ev, &loc2, op, st)?),
                )
            }
            // A forwarding handler (smap/skeep): re-emit the op to the source
            // under fresh shadowing evidence that threads the accumulator into
            // the outer evidence, then thread the handled body.
            Comp::Handle { .. } => self.thread_forward(c, ev, loc, op, st)?,
            // Tail producer heads: append evidence and accumulator, returning
            // the new accumulator directly.
            Comp::Do(o, args) if *o == op => {
                let mut a = self.rewrite_values(args, loc, op)?;
                a.push(Value::Var(st));
                Comp::App(Box::new(Comp::Force(Value::Var(ev))), a)
            }
            Comp::Call(g, args) if self.produces(c, loc, op) => {
                let mut a = self.rewrite_values(args, loc, op)?;
                a.push(Value::Var(ev));
                a.push(Value::Var(st));
                Comp::Call(*g, a)
            }
            Comp::App(f, args) if self.produces(c, loc, op) => {
                let mut a = self.rewrite_values(args, loc, op)?;
                a.push(Value::Var(ev));
                a.push(Value::Var(st));
                Comp::App(Box::new(self.rewrite(f, loc, op)?), a)
            }
            Comp::Return(_) => Comp::Return(Value::Var(st)),
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.thread_st(t, ev, loc, op, st)?),
                Box::new(self.thread_st(e, ev, loc, op, st)?),
            ),
            Comp::Case(v, arms) => Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_st(b, ev, loc, op, st)?)))
                    .collect::<Option<_>>()?,
            ),
            // A pure tail computation: run it, discard, return the accumulator.
            other => {
                let d = self.fresh("d");
                Comp::Bind(
                    Box::new(self.rewrite(other, loc, op)?),
                    d,
                    Box::new(Comp::Return(Value::Var(st))),
                )
            }
        })
    }

    // Thread a forwarding handle `handle s(()) with fun op(x) => <re-emit>`. The
    // clause is tail-resumptive (its `resume` carries the re-emit's result), so
    // stripping resume leaves a body that re-emits to the outer evidence;
    // threading that body builds the source's evidence `\(x.., acc) -> acc'`,
    // bound under a fresh shadowing name. The handled body `s(())` then threads
    // the accumulator through under that fresh evidence, and the identity return
    // clause is absorbed (the threaded body already yields the accumulator).
    pub(super) fn thread_forward(
        &mut self,
        c: &Comp,
        ev: Sym,
        loc: &Loc,
        op: Sym,
        st: Sym,
    ) -> Option<Comp> {
        let Comp::Handle {
            body,
            ops,
            return_var,
            return_body,
        } = c
        else {
            return None;
        };
        let [clause] = ops.as_slice() else {
            return None;
        };
        if clause.name != op || !is_id_return(*return_var, return_body.as_deref()) {
            return None;
        }
        let stripped = strip_resume(&clause.body, &resume_set(clause.resume))?;
        let acc = self.fresh("acc");
        let ev_body = self.thread_st(&stripped, ev, loc, op, acc)?;
        let mut ev_params = clause.params.clone();
        ev_params.push(acc);
        let inner_thunk = Value::Thunk(Box::new(Comp::Lam(ev_params, Box::new(ev_body))));
        let inner = self.fresh("ev");
        let threaded = self.thread_st(body, inner, loc, op, st)?;
        Some(Comp::Bind(
            Box::new(Comp::Return(inner_thunk)),
            inner,
            Box::new(threaded),
        ))
    }
}
