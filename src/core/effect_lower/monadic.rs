//! Free-monad translation pass.

use std::collections::{BTreeMap, BTreeSet};
use std::slice;

use super::analysis::{monadic_region, open_resume_escapes};
use super::checks::check_convention_boundaries;
use super::diagnostics::{free_monad_warning, genuine_eff};
use super::runtime::{ctor_pat, ebind_fn, epure, qapply_fn, synth_ctor};
use super::walk::handle_escapes;
use super::{
    flow, EarlyExitMode, Lowered, Lowerer, MonadicScope, ResumeMode, DONE_TAG, EBIND, EFF, EOP,
    EPURE, ERESUME, MORE_TAG, OP_TAG, PURE_TAG, QAPPLY, RESUME_TAG, SDONE, SMORE, STEP, TQ, TQCONS,
    TQCONS_TAG, TQNIL, TQNIL_TAG,
};
use crate::core::builtins::Builtin;
use crate::core::cbpv::{Comp, Core, CoreFn, CoreOp, Value};
use crate::error::TypeError;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::types::CtorInfo;

impl Lowerer {
    // A right-associative `id == k` cascade: for each op, when `scrut` equals
    // its id run the branch `make` produces, else fall through to the next. The
    // last falls through to `fallthrough`. Built back-to-front (each branch then
    // its test var) so the emitted tree and fresh-var order are exactly the
    // hand-rolled form. Drives all three dispatch sites (handler/forward/mask).
    pub(super) fn build_op_chain(
        &mut self,
        scrut: &Value,
        ids: &[i64],
        mut make: impl FnMut(&mut Self, usize) -> Result<Comp, TypeError>,
        fallthrough: Comp,
    ) -> Result<Comp, TypeError> {
        let mut acc = fallthrough;
        for i in (0..ids.len()).rev() {
            let then = make(self, i)?;
            let t = self.fresh("t");
            acc = Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Eq, scrut.clone(), Value::Int(ids[i]))),
                t,
                Box::new(Comp::If(Value::Var(t), Box::new(then), Box::new(acc))),
            );
        }
        Ok(acc)
    }

    // A handler is open when evaluating it can perform an effect it does not
    // catch. That is exactly the handle's escape set (`handle_escapes`): body
    // ops with no matching clause, plus everything the return clause and the
    // op clauses perform. Clauses run in the enclosing context (a deep handler
    // reinstalls itself only around `resume`), so even a clause re-performing
    // this handler's own op escapes and keeps the handler open; stripping own
    // ops from clause latents here once misclassified such a handler closed,
    // which the closed drivers turn into a self-handling loop or a residual
    // `do`. `latent` flows the same set interprocedurally, so classification
    // and flow cannot drift. Whole-program mode drives every handler
    // open-style for uniformity.
    pub(super) fn is_open(&self, c: &Comp) -> bool {
        if self.scope.is_whole() {
            return true;
        }
        let Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } = c
        else {
            return false;
        };
        let mut s = BTreeSet::new();
        handle_escapes(body, return_body.as_deref(), ops, &self.latent, &mut s);
        !s.is_empty()
    }

    pub(super) fn is_resume_app(&self, f: &Comp) -> bool {
        matches!(f, Comp::Force(Value::Var(v)) if self.resume_aliases.contains(v))
    }

    // Structural pass over the whole program: rewrite every `handle` into a
    // call to a generated driver, leaving non-effectful code untouched.
    pub(super) fn lower_comp(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        Ok(match c {
            Comp::Handle { .. } if self.is_open(c) => {
                let e = self.fresh("e");
                let x = self.fresh("ex");
                Comp::Bind(
                    Box::new(self.lower_handle_open(c)?),
                    e,
                    Box::new(Comp::Case(
                        Value::Var(e),
                        vec![
                            (
                                ctor_pat(EPURE, slice::from_ref(&x)),
                                Comp::Return(Value::Var(x)),
                            ),
                            (
                                ctor_pat(
                                    EOP,
                                    &["_fi".into(), "_fs".into(), "_fa".into(), "_fk".into()],
                                ),
                                Comp::Error(Value::Str(
                                    "ICE: effect op escaped a closed handler".into(),
                                )),
                            ),
                        ],
                    )),
                )
            }
            Comp::Handle { .. } => self.handle_closed(c)?,
            // A mask reached outside monadic context has no escaping ops to
            // relabel, so it is the identity on its body.
            Comp::Mask(_, b) => self.lower_comp(b)?,
            Comp::Bind(m, x, n) => {
                if let Some(c) = self.try_lower_fn_answer(m, *x, n)? {
                    c
                } else {
                    Comp::Bind(
                        Box::new(self.lower_comp(m)?),
                        *x,
                        Box::new(self.lower_comp(n)?),
                    )
                }
            }
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.lower_comp(t)?),
                Box::new(self.lower_comp(e)?),
            ),
            Comp::Case(v, arms) => Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Ok((p.clone(), self.lower_comp(b)?)))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.lower_comp(b)?)),
            Comp::App(f, args) => Comp::App(Box::new(self.lower_comp(f)?), args.clone()),
            other => other.clone(),
        })
    }

    // Monadic translation: produce a computation whose result is an Eff value.
    pub(super) fn mon(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        Ok(match c {
            Comp::Return(v) => {
                let v = self.mon_value(v)?;
                epure(v)
            }
            Comp::Bind(m, x, n) => {
                // The elaborator routes a resume through `return k to tmp` before
                // applying it, so propagate the alias to keep recognizing it.
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if self.resume_aliases.contains(v) {
                        self.resume_aliases.insert(*x);
                    }
                }
                let mv = self.fresh("m");
                let f = Value::Thunk(Box::new(Comp::Lam(vec![*x], Box::new(self.mon(n)?))));
                Comp::Bind(
                    Box::new(self.mon(m)?),
                    mv,
                    Box::new(Comp::Call(EBIND.into(), vec![Value::Var(mv), f])),
                )
            }
            Comp::Do(op, args) => {
                let id = self.op_id(*op)?;
                let arg = match args.len() {
                    0 => Value::Unit,
                    1 => self.mon_value(&args[0])?,
                    _ => Value::Tuple(args.iter().map(|a| self.mon_value(a)).collect::<Result<
                        _,
                        TypeError,
                    >>(
                    )?),
                };
                // A fresh op's continuation queue is empty (Unit): `qApply(empty,
                // v) = EPure(v)`. `ebind` snocs onto it as the op propagates.
                Comp::Return(Value::Ctor(
                    EOP.into(),
                    OP_TAG,
                    vec![Value::Int(id), Value::Int(0), arg, Value::Unit],
                ))
            }
            Comp::If(v, t, e) => {
                Comp::If(v.clone(), Box::new(self.mon(t)?), Box::new(self.mon(e)?))
            }
            Comp::Case(v, arms) => Comp::Case(
                self.mon_value(v)?,
                arms.iter()
                    .map(|(p, b)| Ok((p.clone(), self.mon(b)?)))
                    .collect::<Result<_, TypeError>>()?,
            ),
            // A resume inside a native (`{n}@region`) clause body: `resume` is
            // bound to the op's captured continuation queue `q`, so applying it
            // reifies to `EResume(queue, value)`, which the `{n}@region` loop drives
            // by tail-calling itself on `qApply(queue, value)`. Eligibility puts
            // this in tail position, so the `EResume` is the clause's result.
            Comp::App(f, args) if self.resume != ResumeMode::Off && self.is_resume_app(f) => {
                let Comp::Force(Value::Var(q)) = f.as_ref() else {
                    unreachable!("is_resume_app matched a non-Force(Var)")
                };
                let arg = match args.len() {
                    0 => Value::Unit,
                    1 => self.mon_value(&args[0])?,
                    _ => Value::Tuple(args.iter().map(|a| self.mon_value(a)).collect::<Result<
                        _,
                        TypeError,
                    >>(
                    )?),
                };
                let reified = match self.resume {
                    ResumeMode::Native => {
                        Value::Ctor(ERESUME.into(), RESUME_TAG, vec![Value::Var(*q), arg])
                    }
                    ResumeMode::Off => unreachable!("guarded by resume != Off"),
                };
                Comp::Return(reified)
            }
            // Applying the current resume already yields an Eff value (the
            // re-driven continuation), so thread it instead of EPure-wrapping.
            Comp::App(f, args) if self.is_resume_app(f) => Comp::App(f.clone(), args.clone()),
            // In whole-program mode every closure body is monadic, so any
            // dynamic application already yields an Eff value.
            Comp::App(f, args) if self.scope.is_whole() => Comp::App(
                Box::new(self.mon_head(f)?),
                args.iter()
                    .map(|a| self.mon_value(a))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Comp::Mask(ops, body) => {
                let driver = self.mask_driver(ops)?;
                let v = self.fresh("m");
                Comp::Bind(
                    Box::new(self.mon(body)?),
                    v,
                    Box::new(Comp::Call(driver, vec![Value::Var(v)])),
                )
            }
            Comp::Handle { .. } if self.is_open(c) => self.lower_handle_open(c)?,
            Comp::Handle { .. } => {
                let v = self.fresh("h");
                Comp::Bind(
                    Box::new(self.handle_closed(c)?),
                    v,
                    Box::new(epure(Value::Var(v))),
                )
            }
            // A call to an effectful function already yields an Eff value. A
            // partial application (whole-program mode) yields a bare closure,
            // so lift it; the closure body is monadic once saturated.
            Comp::Call(g, args) if self.eff.contains(g) => {
                let args: Vec<Value> =
                    args.iter()
                        .map(|a| self.mon_value(a))
                        .collect::<Result<_, TypeError>>()?;
                let arity =
                    self.arities
                        .get(g)
                        .copied()
                        .ok_or_else(|| TypeError::InternalInvariant {
                            msg: format!("effectful call to unknown function `{g}`"),
                        })?;
                let partial = self.scope.is_whole() && args.len() < arity;
                let call = Comp::Call(*g, args);
                if partial {
                    let v = self.fresh("p");
                    Comp::Bind(Box::new(call), v, Box::new(epure(Value::Var(v))))
                } else {
                    call
                }
            }
            // Effect-free computations: run, then lift the result with EPure.
            Comp::Error(_) => c.clone(),
            _ => {
                let v = self.fresh("p");
                Comp::Bind(
                    Box::new(self.lower_comp(c)?),
                    v,
                    Box::new(epure(Value::Var(v))),
                )
            }
        })
    }

    // Whole-program mode rewrites every thunk so its body is monadic. Outside
    // that mode values pass through untouched.
    pub(super) fn mon_value(&mut self, v: &Value) -> Result<Value, TypeError> {
        if !self.scope.is_whole() {
            return Ok(v.clone());
        }
        Ok(match v {
            Value::Thunk(c) => Value::Thunk(Box::new(match c.as_ref() {
                Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.mon(b)?)),
                other => self.mon(other)?,
            })),
            Value::Ctor(n, t, fs) => Value::Ctor(
                *n,
                *t,
                fs.iter()
                    .map(|x| self.mon_value(x))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Value::Tuple(fs) => Value::Tuple(
                fs.iter()
                    .map(|x| self.mon_value(x))
                    .collect::<Result<_, TypeError>>()?,
            ),
            _ => v.clone(),
        })
    }

    pub(super) fn mon_head(&mut self, f: &Comp) -> Result<Comp, TypeError> {
        Ok(match f {
            Comp::Force(v) => Comp::Force(self.mon_value(v)?),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.mon(b)?)),
            Comp::App(g, args) => Comp::App(
                Box::new(self.mon_head(g)?),
                args.iter()
                    .map(|a| self.mon_value(a))
                    .collect::<Result<_, TypeError>>()?,
            ),
            other => other.clone(),
        })
    }

    // An entry to a monadic region returns Eff; unwrap its final EPure to the
    // bare value its (direct-convention) caller expects, and trap on an op that
    // escaped every handler, naming it like the interpreter's unhandled-effect
    // error. `main` is the canonical entry (the runtime calls it); under local
    // monadification every component function a fused caller invokes is one too.
    pub(super) fn unwrap_main(&mut self, body: Comp) -> Comp {
        let r = self.fresh("r");
        let x = self.fresh("x");
        let id = self.fresh("id");
        let ops: Vec<(Sym, i64)> = self.op_ids.iter().map(|(n, i)| (*n, *i)).collect();
        let mut trap = Comp::Error(Value::Str("unhandled effect".into()));
        for (name, opid) in ops.into_iter().rev() {
            let t = self.fresh("t");
            trap = Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Eq, Value::Var(id), Value::Int(opid))),
                t,
                Box::new(Comp::If(
                    Value::Var(t),
                    Box::new(Comp::Error(Value::Str(format!(
                        "unhandled effect `{name}`"
                    )))),
                    Box::new(trap),
                )),
            );
        }
        Comp::Bind(
            Box::new(body),
            r,
            Box::new(Comp::Case(
                Value::Var(r),
                vec![
                    (
                        ctor_pat(EPURE, slice::from_ref(&x)),
                        Comp::Return(Value::Var(x)),
                    ),
                    (
                        ctor_pat(EOP, &[id, "_us".into(), "_ua".into(), "_uk".into()]),
                        trap,
                    ),
                ],
            )),
        )
    }

    // Lower a set of functions on the free-monad path: monadify the effectful
    // ones (`self.eff`), leave the rest direct, and unwrap each entry. Shared by
    // the whole-program fallback and the local-monadification region.
    pub(super) fn lower_set(
        &mut self,
        fns: &[&CoreFn],
        entries: &BTreeSet<Sym>,
    ) -> Result<Vec<CoreFn>, TypeError> {
        fns.iter()
            .map(|f| {
                let body = if self.eff.contains(&f.name) {
                    self.mon(&f.body)?
                } else {
                    self.lower_comp(&f.body)?
                };
                // Trap an effect that escaped every handler whenever the function
                // is a monadic entry, not only in whole-program mode: an unhandled
                // effect would otherwise flow out as a bare `EOp`, silently
                // diverging from the interpreter, which raises `unhandled effect`.
                let body = if entries.contains(&f.name) && self.eff.contains(&f.name) {
                    self.unwrap_main(body)
                } else {
                    body
                };
                Ok(CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    dict_arity: f.dict_arity,
                    body,
                })
            })
            .collect()
    }

    // The functions whose body lets an effectful closure escape untrackably, or
    // whose open handler's resume escapes: the seeds of the monadic region.
    pub(super) fn escaping_set(&self, core: &Core) -> BTreeSet<Sym> {
        let mut s = flow::escaping_fns(core, &self.latent, &self.flow);
        for f in &core.fns {
            if open_resume_escapes(&f.body, &self.latent) {
                s.insert(f.name);
            }
        }
        s
    }

    // Local monadification. When an effectful closure escapes, confine the free
    // monad to the flow/effect-connected component that contains it and keep
    // everything else fused. Returns the fully lowered program when the split
    // is clean, or None to fall back to whole-program monadification (sound, no
    // regression). The cleanliness is structural: the component's effect ops are
    // disjoint from the rest (so no boundary call crosses a live effect), and no
    // thunk crosses the boundary as a call argument or entry result (so the two
    // calling conventions never meet on a first-class value); `monadic_region`
    // returns None otherwise.
    pub(super) fn try_local(
        &mut self,
        core: &Core,
        base_ctors: &BTreeMap<String, CtorInfo>,
    ) -> Result<Option<Lowered>, TypeError> {
        let escaping = self.escaping_set(core);
        if escaping.is_empty() {
            return Ok(None);
        }
        let Some((region, entries)) = monadic_region(core, &self.latent, &escaping) else {
            return Ok(None);
        };
        // `main` must be fusable (in the rest) for the rest to fuse at all; if it
        // is in the region the rest-fusion guard rejects it anyway.
        if region.contains(&Sym::new(ENTRY_POINT)) {
            return Ok(None);
        }

        // Below here `self.eff`/`full`/`early`/`generated` are reconfigured for
        // the two sub-lowerings. Save them so any bail restores the whole-program
        // state `monadic_set` chose, which the fallback then uses unchanged.
        let saved_eff = std::mem::take(&mut self.eff);
        let saved_scope = self.scope;
        let restore = |me: &mut Self, eff: BTreeSet<Sym>, scope: MonadicScope| {
            me.eff = eff;
            me.scope = scope;
            me.early = EarlyExitMode::Continue;
            me.generated.clear();
        };

        // Fuse the rest. Evidence threading appends evidence for genuinely
        // effectful functions only, so reset `eff` from the whole-program
        // inflation `monadic_set` returned.
        let rest = Core {
            fns: core
                .fns
                .iter()
                .filter(|f| !region.contains(&f.name))
                .cloned()
                .collect(),
        };
        self.eff = genuine_eff(&self.latent);
        self.scope = MonadicScope::Selective;
        self.early = EarlyExitMode::Continue;
        let (fused, early) = if let Some(c) = self.try_lower_ev(&rest) {
            (c, EarlyExitMode::Continue)
        } else if let Some(c) = self.try_lower_state(&rest) {
            (c, self.early)
        } else {
            restore(self, saved_eff, saved_scope);
            return Ok(None);
        };

        // Free-monad the region, full-style: a uniform monadic convention within
        // it so the escaping closure's dynamic applies all agree.
        self.eff.clone_from(&region);
        self.scope = MonadicScope::WholeProgram;
        self.early = EarlyExitMode::Continue;
        self.generated.clear();
        let region_fns: Vec<&CoreFn> = core
            .fns
            .iter()
            .filter(|f| region.contains(&f.name))
            .collect();
        let mon_fns = self.lower_set(&region_fns, &entries)?;

        let mut fns = fused.fns;
        fns.extend(mon_fns);
        let generated = std::mem::take(&mut self.generated);
        let mut full_style: BTreeSet<Sym> = region.clone();
        full_style.extend(generated.iter().map(|f| f.name));
        full_style.insert(EBIND.into());
        full_style.insert(QAPPLY.into());
        fns.extend(generated);
        fns.push(ebind_fn());
        fns.push(qapply_fn());

        // Boundary rail over the full-style region (functions, drivers, ebind).
        // The fused rest is a different convention and excluded. A failure here
        // means the split was not as clean as the static checks judged, so fall
        // back to whole-program monadification rather than miscompiling.
        let refs: Vec<&CoreFn> = fns.iter().collect();
        if check_convention_boundaries(&fns, &refs, &full_style, true, &entries).is_err() {
            restore(self, saved_eff, saved_scope);
            return Ok(None);
        }

        let warning = free_monad_warning(core, &region, &self.latent);

        let mut ctors = base_ctors.clone();
        ctors.insert(EPURE.into(), synth_ctor(EFF, PURE_TAG, 1));
        ctors.insert(EOP.into(), synth_ctor(EFF, OP_TAG, 4));
        ctors.insert(TQNIL.into(), synth_ctor(TQ, TQNIL_TAG, 0));
        ctors.insert(TQCONS.into(), synth_ctor(TQ, TQCONS_TAG, 2));
        if early.short_circuits() {
            ctors.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
            ctors.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
        }
        Ok(Some((Core { fns }, ctors, warning)))
    }

    // Emit an op outward: `EOp(id, skip, arg, taq_snoc(Unit, resume))`, a fresh
    // singleton queue holding `resume`, the continuation that re-enters the
    // forwarding driver. The empty queue is `Unit`.
    pub(super) fn forward_eop(
        &mut self,
        id: Value,
        skip: Value,
        arg: Value,
        resume: Value,
    ) -> Comp {
        let q = self.fresh("q");
        Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqSnoc,
                vec![Value::Unit, resume],
            )),
            q,
            Box::new(Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![id, skip, arg, Value::Var(q)],
            ))),
        )
    }
}
