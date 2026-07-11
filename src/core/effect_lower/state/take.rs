//! `stake` (early termination) via the `Step` protocol: thread `Step S` through
//! every producer, stopping on `SDone`, and the `step_*`/seed helpers that fold,
//! guard, and unwrap that wrapper.

use std::collections::{BTreeMap, BTreeSet};

use super::super::evidence::resume_set;
use super::super::flow::Loc;
use super::super::{Lowerer, SDONE, SMORE};
use crate::core::cbpv::{Comp, CorePat, Value};
use crate::core::fv;
use crate::sym::Sym;

use super::anf::{
    anf_app_arg, branch_resumes, ctor_pat1, is_alias_return, resume_call, sdone, smore,
};

// Constant threading context for the `stake` (early-termination) lowering: the
// downstream evidence, the flow env, the op, the active evidences (for rewriting
// non-producer subterms), and the live resume aliases.
#[derive(Clone, Copy)]
pub(super) struct Take<'a> {
    pub(super) ev: Sym,
    pub(super) loc: &'a Loc,
    pub(super) op: Sym,
    pub(super) evs: &'a BTreeMap<Sym, Sym>,
    pub(super) aliases: &'a BTreeSet<Sym>,
}

impl Lowerer {
    // The seed `n` of a `let g = handle s(()) with <stake>; g(n)`, or None when
    // this bind is not that shape. The handle's single clause must be a take,
    // and `g(n)` is matched through its ANF binds (`return g to g'; (force
    // g')(n')`), the seed resolved to its source value.
    pub(super) fn take_seed(&self, m: &Comp, g: Sym, rest: &Comp) -> Option<Value> {
        let Comp::Handle { ops, .. } = m else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        if !self.is_take(clause) {
            return None;
        }
        anf_app_arg(g, rest)
    }

    // Lower a `stake` via the Step protocol. The clause `\(cnt) -> if c then {
    // do op(x); resume(next) } else <drop>` becomes the source's evidence
    // `\(x.., Step (dstep, cnt)) -> ...`: it pairs its counter with the
    // downstream state `dstep`, re-emits into `dstep` while resuming, and yields
    // `SDone` when it drops the continuation. The handled body threads from the
    // combined seed `SMore (st, n)`, and `stake_go` returns the downstream
    // `dstep` it carried (its own `()` return is discarded by the consumer).
    pub(super) fn thread_take(
        &mut self,
        handle: &Comp,
        seed: &Value,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: Sym,
    ) -> Option<Comp> {
        let Comp::Handle { body, ops, .. } = handle else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        let op = clause.name;
        let ev = *evs.get(&op)?;
        let Comp::Return(Value::Thunk(t)) = &clause.body else {
            return None;
        };
        let Comp::Lam(ps, inner) = t.as_ref() else {
            return None;
        };
        let [cnt] = ps.as_slice() else {
            return None;
        };
        let cnt = *cnt;
        let aliases = resume_set(clause.resume);

        // Evidence for the source: unpack the step, then run the clause's leading
        // binds (the counter test) and branch, threading the resume side into the
        // downstream evidence and the drop side into SDone.
        let dstep = self.fresh("ds");
        let take = Take {
            ev,
            loc,
            op,
            evs,
            aliases: &aliases,
        };
        let smore_body = self.take_clause(inner, &take, dstep, cnt)?;
        let tstep = self.fresh("ts");
        let sd = self.fresh("sd");
        let evt_body = Comp::Case(
            Value::Var(tstep),
            vec![
                self.step_pair_arm(SMORE, dstep, cnt, smore_body),
                (ctor_pat1(SDONE, sd), Comp::Return(sdone(Value::Var(sd)))),
            ],
        );
        let mut evt_params = clause.params.clone();
        evt_params.push(tstep);
        let evt = self.fresh("ev");
        let evt_thunk = Value::Thunk(Box::new(Comp::Lam(evt_params, Box::new(evt_body))));

        // Thread the source from the combined seed, then return the downstream
        // step the loop carried (SMore or SDone, same payload).
        let seedvar = self.fresh("st");
        let combined = smore(Value::Tuple(vec![Value::Var(st), seed.clone()]));
        // Thread the source with the take's own evidence shadowing its op.
        let mut evs_src = evs.clone();
        evs_src.insert(op, evt);
        let threaded = self.thread_st(body, &evs_src, loc, seedvar)?;
        let fin = self.fresh("fin");
        let d1 = self.fresh("d");
        let w1 = self.fresh("w");
        let d2 = self.fresh("d");
        let w2 = self.fresh("w");
        let extract = Comp::Case(
            Value::Var(fin),
            vec![
                self.step_pair_arm(SMORE, d1, w1, Comp::Return(Value::Var(d1))),
                self.step_pair_arm(SDONE, d2, w2, Comp::Return(Value::Var(d2))),
            ],
        );
        Some(Comp::Bind(
            Box::new(Comp::Return(evt_thunk)),
            evt,
            Box::new(Comp::Bind(
                Box::new(Comp::Return(combined)),
                seedvar,
                Box::new(Comp::Bind(Box::new(threaded), fin, Box::new(extract))),
            )),
        ))
    }

    // Build the SMore arm of a take's evidence: keep the clause's leading
    // (counter-testing) binds, then transform the tail `if`: the resuming side
    // folds the downstream evidence and continues, the dropping side stops with
    // SDone carrying the current downstream step and counter.
    pub(super) fn take_clause(
        &mut self,
        c: &Comp,
        t: &Take<'_>,
        dstep: Sym,
        cnt: Sym,
    ) -> Option<Comp> {
        Some(match c {
            Comp::Bind(m, x, n) => {
                Comp::Bind(m.clone(), *x, Box::new(self.take_clause(n, t, dstep, cnt)?))
            }
            Comp::If(cond, b1, b2) => {
                let (resume_b, drop_b, invert) = if branch_resumes(b1, t.aliases) {
                    (b1, b2, false)
                } else {
                    (b2, b1, true)
                };
                let more = self.take_thread(resume_b, t, dstep)?;
                let d = self.fresh("d");
                let dropped = Comp::Bind(
                    Box::new(self.rewrite(drop_b, t.loc, t.evs)?),
                    d,
                    Box::new(Comp::Return(sdone(Value::Tuple(vec![
                        Value::Var(dstep),
                        Value::Var(cnt),
                    ])))),
                );
                if invert {
                    Comp::If(cond.clone(), Box::new(dropped), Box::new(more))
                } else {
                    Comp::If(cond.clone(), Box::new(more), Box::new(dropped))
                }
            }
            _ => return None,
        })
    }

    // Thread the resuming branch of a take clause into `SMore ((dstep'), next)`:
    // each `do op(args)` folds into the downstream evidence (advancing dstep),
    // and the parameter-passing resume `k(())(next)` becomes the new step
    // carrying the advanced dstep and the next counter value.
    pub(super) fn take_thread(&mut self, c: &Comp, t: &Take<'_>, dstep: Sym) -> Option<Comp> {
        Some(match c {
            // Right-associate a bind whose head is itself a bind, so a re-emit at
            // the tail of a sub-block (the ANF of `emit(x)`) surfaces as a
            // top-level head this pass can rewrite.
            Comp::Bind(m, x, n) if matches!(m.as_ref(), Comp::Bind(..)) => {
                let Comp::Bind(a, y, b) = m.as_ref() else {
                    return None;
                };
                let reassoc = Comp::Bind(
                    a.clone(),
                    *y,
                    Box::new(Comp::Bind(b.clone(), *x, n.clone())),
                );
                return self.take_thread(&reassoc, t, dstep);
            }
            Comp::Bind(m, x, n) if is_alias_return(m, t.aliases) => {
                let mut a2 = t.aliases.clone();
                a2.insert(*x);
                return self.take_thread(n, &Take { aliases: &a2, ..*t }, dstep);
            }
            // Re-emit: fold the downstream evidence, advancing dstep.
            Comp::Bind(m, x, n) if matches!(m.as_ref(), Comp::Do(o, _) if *o == t.op) => {
                let Comp::Do(_, args) = m.as_ref() else {
                    return None;
                };
                let mut a = self.rewrite_values(args, t.loc, t.evs)?;
                a.push(Value::Var(dstep));
                let ds2 = self.fresh("ds");
                let call = Comp::App(Box::new(Comp::Force(Value::Var(t.ev))), a);
                let mut cont = self.take_thread(n, t, ds2)?;
                if fv::comp(n).contains(x) {
                    cont = Comp::Bind(Box::new(Comp::Return(Value::Unit)), *x, Box::new(cont));
                }
                Comp::Bind(Box::new(call), ds2, Box::new(cont))
            }
            // The double application `k(())(next)`: stop with the carried dstep.
            Comp::Bind(m, kr, n) if resume_call(m, t.aliases) => {
                let Comp::App(g, gargs) = n.as_ref() else {
                    return None;
                };
                if !matches!(g.as_ref(), Comp::Force(Value::Var(k)) if k == kr) {
                    return None;
                }
                let [next] = gargs.as_slice() else {
                    return None;
                };
                if !fv::value(next).is_disjoint(t.aliases) {
                    return None;
                }
                Comp::Return(smore(Value::Tuple(vec![Value::Var(dstep), next.clone()])))
            }
            Comp::Bind(m, x, n) if fv::comp(m).is_disjoint(t.aliases) => {
                Comp::Bind(m.clone(), *x, Box::new(self.take_thread(n, t, dstep)?))
            }
            Comp::If(v, tb, e) if fv::value(v).is_disjoint(t.aliases) => Comp::If(
                v.clone(),
                Box::new(self.take_thread(tb, t, dstep)?),
                Box::new(self.take_thread(e, t, dstep)?),
            ),
            _ => return None,
        })
    }

    // `\(.., acc) -> body` lifted to operate on `Step Acc`: fold inside SMore,
    // forward SDone untouched. `body` returns the new accumulator.
    pub(super) fn step_map(&mut self, step: Sym, acc: Sym, body: Comp) -> Comp {
        let r = self.fresh("r");
        let sd = self.fresh("sd");
        Comp::Case(
            Value::Var(step),
            vec![
                (
                    ctor_pat1(SMORE, acc),
                    Comp::Bind(
                        Box::new(body),
                        r,
                        Box::new(Comp::Return(smore(Value::Var(r)))),
                    ),
                ),
                (ctor_pat1(SDONE, sd), Comp::Return(sdone(Value::Var(sd)))),
            ],
        )
    }

    // `Ctor(p) => case p of (a, b) => body`: a step over a state pair, unpacked
    // in two steps because codegen binds only flat Var subpatterns.
    pub(super) fn step_pair_arm(
        &mut self,
        ctor: &str,
        a: Sym,
        b: Sym,
        body: Comp,
    ) -> (CorePat, Comp) {
        let p = self.fresh("p");
        let inner = Comp::Case(
            Value::Var(p),
            vec![(CorePat::Tuple(vec![Some(a), Some(b)]), body)],
        );
        (ctor_pat1(ctor, p), inner)
    }

    // Stop the producer once a stake has yielded SDone, else run the rest.
    pub(super) fn step_guard(&mut self, step: Sym, cont: Comp) -> Comp {
        let m = self.fresh("_w");
        let d = self.fresh("_w");
        Comp::Case(
            Value::Var(step),
            vec![
                (ctor_pat1(SMORE, m), cont),
                (ctor_pat1(SDONE, d), Comp::Return(Value::Var(step))),
            ],
        )
    }

    // Unwrap the final `Step` of a fused loop back to its bare payload.
    pub(super) fn seed_unwrap(&mut self, threaded: Comp) -> Comp {
        let fin = self.fresh("fin");
        let a = self.fresh("a");
        let b = self.fresh("a");
        Comp::Bind(
            Box::new(threaded),
            fin,
            Box::new(Comp::Case(
                Value::Var(fin),
                vec![
                    (ctor_pat1(SMORE, a), Comp::Return(Value::Var(a))),
                    (ctor_pat1(SDONE, b), Comp::Return(Value::Var(b))),
                ],
            )),
        )
    }
}
