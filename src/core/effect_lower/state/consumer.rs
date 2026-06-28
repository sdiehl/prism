//! Consumer-side rewriting: lower fold and control handles to their state
//! transformers, and structurally rewrite non-producer code so producer thunk
//! values gain their evidence/accumulator parameters.

use std::collections::BTreeMap;

use super::super::evidence::{resume_set, strip_resume};
use super::super::flow::{self, Loc};
use super::super::Lowerer;
use crate::core::cbpv::{Comp, Value};
use crate::names::ev;
use crate::sym::Sym;

use super::anf::{is_id_transformer, smore, strip_state};

impl Lowerer {
    // Build the state-transformer evidence for a fold clause, bind it under the
    // canonical `ev@<id>` name, and return the handle as a bare state
    // transformer `\(acc0) -> <body threaded, st = acc0>; <return clause>`,
    // applied at its call site to the initial accumulator. An identity return
    // clause is absorbed (the threaded body already yields the acc); a get-style
    // `return r => \s -> body` is applied to the final accumulator.
    pub(super) fn lower_fold(
        &mut self,
        c: &Comp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
    ) -> Option<Comp> {
        let Comp::Handle {
            body,
            ops: clauses,
            return_var,
            return_body,
        } = c
        else {
            return None;
        };

        // One state-transformer evidence per clause `\(p.., acc) -> <body with
        // k(A)(ns) -> return ns>`, bound under its canonical `ev@<id>` name. A
        // `State` handler contributes both `get` and `put`, threading one acc.
        let mut ev_binds: Vec<(Sym, Value)> = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let ev_name = *evs.get(&clause.name)?;
            let Comp::Return(Value::Thunk(t)) = &clause.body else {
                return None;
            };
            let Comp::Lam(ps, inner) = t.as_ref() else {
                return None;
            };
            let [acc] = ps.as_slice() else {
                return None;
            };
            let (stripped, _kind) = strip_state(inner, &resume_set(clause.resume), *acc)?;
            let ev_body = self.rewrite(&stripped, loc, evs)?;
            let mut ev_params = clause.params.clone();
            // In early mode the state is `Step Acc`: the evidence folds inside
            // SMore and forwards SDone untouched, so a stake upstream can stop.
            let ev_body = if self.early {
                let step = self.fresh("step");
                let body = self.step_map(step, *acc, ev_body);
                ev_params.push(step);
                body
            } else {
                ev_params.push(*acc);
                ev_body
            };
            ev_binds.push((
                ev_name,
                Value::Thunk(Box::new(Comp::Lam(ev_params, Box::new(ev_body)))),
            ));
        }

        // g = \(acc0) -> <body threaded, st = acc0>, closing over the evidences.
        // In early mode the seed is wrapped `SMore(acc0)` and the threaded loop's
        // final `Step` is unwrapped back to the bare accumulator.
        let acc0 = self.fresh("acc");
        let g_body = if self.early {
            let st0 = self.fresh("st");
            let threaded = self.thread_st(body, evs, loc, st0)?;
            Comp::Bind(
                Box::new(Comp::Return(smore(Value::Var(acc0)))),
                st0,
                Box::new(self.seed_unwrap(threaded)),
            )
        } else {
            self.thread_st(body, evs, loc, acc0)?
        };
        let g_body =
            self.apply_state_return(g_body, *return_var, return_body.as_deref(), loc, evs)?;
        let g = Value::Thunk(Box::new(Comp::Lam(vec![acc0], Box::new(g_body))));
        let mut out = Comp::Return(g);
        for (name, thunk) in ev_binds.into_iter().rev() {
            out = Comp::Bind(Box::new(Comp::Return(thunk)), name, Box::new(out));
        }
        Some(out)
    }

    // Apply a fold's state-transformer return clause to the threaded body's final
    // accumulator. The identity transformer is absorbed (the threaded body already
    // yields the accumulator). A get-style `return r => \s -> body` binds both the
    // producer value `r` and the final state `s` to the final accumulator (they
    // coincide for a Moore-shaped producer, whose tail return reads the state) and
    // runs `body`. Returns None for any other return clause.
    fn apply_state_return(
        &mut self,
        threaded: Comp,
        return_var: Option<Sym>,
        return_body: Option<&Comp>,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<Comp> {
        match return_body {
            Some(rb) if is_id_transformer(rb) => Some(threaded),
            Some(Comp::Return(Value::Thunk(t))) => {
                let Comp::Lam(ps, body) = t.as_ref() else {
                    return None;
                };
                let [s] = ps.as_slice() else {
                    return None;
                };
                let rbody = self.rewrite(body, loc, evs)?;
                let fin = self.fresh("fin");
                let r = return_var.unwrap_or_else(|| self.fresh("r"));
                Some(Comp::Bind(
                    Box::new(threaded),
                    fin,
                    Box::new(Comp::Bind(
                        Box::new(Comp::Return(Value::Var(fin))),
                        r,
                        Box::new(Comp::Bind(
                            Box::new(Comp::Return(Value::Var(fin))),
                            *s,
                            Box::new(rbody),
                        )),
                    )),
                ))
            }
            _ => None,
        }
    }

    // Lower a control-consumer handle (`for x in s do ..`). The clause is a
    // side effect resuming with unit, so its evidence is `\(p.., st) -> <side
    // effects>; return st`: the unit state passes through untouched. The handled
    // body threads from a unit seed, and the return clause runs on the final
    // state (the consumer's result, typically `()`).
    pub(super) fn lower_consumer(
        &mut self,
        c: &Comp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
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
        let ev: Sym = *evs.get(&clause.name)?;

        // Evidence: run the clause's side effects, then return the state.
        let stripped = strip_resume(&clause.body, &resume_set(clause.resume))?;
        let st = self.fresh("st");
        let d = self.fresh("d");
        let ev_inner = Comp::Bind(
            Box::new(self.rewrite(&stripped, loc, evs)?),
            d,
            Box::new(Comp::Return(Value::Var(st))),
        );
        let mut ev_params = clause.params.clone();
        let ev_body = if self.early {
            let step = self.fresh("step");
            let body = self.step_map(step, st, ev_inner);
            ev_params.push(step);
            body
        } else {
            ev_params.push(st);
            ev_inner
        };
        let ev_thunk = Value::Thunk(Box::new(Comp::Lam(ev_params, Box::new(ev_body))));

        // Seed unit, thread the producer, bind its result, run the return clause.
        let st0 = self.fresh("st");
        let threaded = self.thread_st(body, evs, loc, st0)?;
        let fin = self.fresh("fin");
        let rv = (*return_var).unwrap_or_else(|| self.fresh("r"));
        let rb = match return_body {
            Some(b) => self.rewrite(b, loc, evs)?,
            None => Comp::Return(Value::Var(rv)),
        };
        let (seed, body_done) = if self.early {
            (smore(Value::Unit), self.seed_unwrap(threaded))
        } else {
            (Value::Unit, threaded)
        };
        let after = Comp::Bind(
            Box::new(body_done),
            fin,
            Box::new(Comp::Bind(
                Box::new(Comp::Return(Value::Var(fin))),
                rv,
                Box::new(rb),
            )),
        );
        Some(Comp::Bind(
            Box::new(Comp::Return(ev_thunk)),
            ev,
            Box::new(Comp::Bind(
                Box::new(Comp::Return(seed)),
                st0,
                Box::new(after),
            )),
        ))
    }

    // Rewrite non-producer code: lower fold handles to their state transformer,
    // thread producer thunk values so their force sites can supply evidence, and
    // recurse structurally. No `do op` or producer call occurs here (those live
    // inside a producer or a handle body, which `thread_st` drives).
    pub(super) fn rewrite(
        &mut self,
        c: &Comp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<Comp> {
        Some(match c {
            Comp::Handle { ops, .. } => match ops.as_slice() {
                [clause] if self.is_consumer(clause) => self.lower_consumer(c, evs, loc)?,
                _ => self.lower_fold(c, evs, loc)?,
            },
            Comp::Return(v) => Comp::Return(self.rewrite_value(v, loc, evs)?),
            Comp::Bind(m, x, n) => {
                let mut loc2 = loc.clone();
                loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                Comp::Bind(
                    Box::new(self.rewrite(m, loc, evs)?),
                    *x,
                    Box::new(self.rewrite(n, &loc2, evs)?),
                )
            }
            Comp::Call(g, args) => Comp::Call(*g, self.rewrite_values(args, loc, evs)?),
            Comp::App(f, args) => Comp::App(
                Box::new(self.rewrite(f, loc, evs)?),
                self.rewrite_values(args, loc, evs)?,
            ),
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.rewrite(t, loc, evs)?),
                Box::new(self.rewrite(e, loc, evs)?),
            ),
            Comp::Case(v, arms) => Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.rewrite(b, loc, evs)?)))
                    .collect::<Option<_>>()?,
            ),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.rewrite(b, loc, evs)?)),
            Comp::Mask(_, b) => self.rewrite(b, loc, evs)?,
            Comp::Do(..) => return None,
            other => other.clone(),
        })
    }

    pub(super) fn rewrite_values(
        &mut self,
        vs: &[Value],
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<Vec<Value>> {
        vs.iter().map(|v| self.rewrite_value(v, loc, evs)).collect()
    }

    // Rewrite a value. An escaping producer thunk (a `\..` whose body is latent
    // in a fused op) gains one `ev@<id>` parameter per fused op plus `st@` and has
    // its body threaded; its force sites supply the matching evidence and
    // accumulator. A pure thunk still has its body rewritten. Any other shape
    // carrying a fused op (a non-lambda thunk, or one buried in data) is rejected;
    // `flow::escapes` already turns the latter into a fall-back, so this is a
    // belt-and-braces guard.
    pub(super) fn rewrite_value(
        &mut self,
        v: &Value,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<Value> {
        Some(match v {
            Value::Thunk(c) => match c.as_ref() {
                Comp::Lam(ps, b) if self.folds_any(b, evs) => {
                    let st: Sym = super::ST.into();
                    let mut loc2 = loc.clone();
                    for p in ps {
                        loc2.insert(*p, flow::Sig::new());
                    }
                    let mut ps2 = ps.clone();
                    let mut evs2 = BTreeMap::new();
                    for o in self.ev_order(evs)? {
                        let e: Sym = ev(self.op_id(o).ok()?).into();
                        ps2.push(e);
                        evs2.insert(o, e);
                    }
                    ps2.push(st);
                    Value::Thunk(Box::new(Comp::Lam(
                        ps2,
                        Box::new(self.thread_st(b, &evs2, &loc2, st)?),
                    )))
                }
                Comp::Lam(ps, b) => Value::Thunk(Box::new(Comp::Lam(
                    ps.clone(),
                    Box::new(self.rewrite(b, loc, evs)?),
                ))),
                other => {
                    if self.folds_any(other, evs) {
                        return None;
                    }
                    Value::Thunk(Box::new(self.rewrite(other, loc, evs)?))
                }
            },
            Value::Ctor(n, t, fs) => Value::Ctor(*n, *t, self.rewrite_values(fs, loc, evs)?),
            Value::Tuple(fs) => Value::Tuple(self.rewrite_values(fs, loc, evs)?),
            _ => v.clone(),
        })
    }
}
