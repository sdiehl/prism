use std::collections::{BTreeMap, BTreeSet};
use std::slice;

use super::cbpv::{reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use super::fv;
use crate::error::TypeError;
use crate::fresh::Fresh;
use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;
use crate::types::{CtorInfo, Type};

mod evidence;
mod flow;
mod state;

// Compile algebraic effects to plain closures and data by a free-monad
// translation. A computation that may perform effects is reified into a value
// of the result type:
//
//   EPure(v)              a finished computation returning v
//   EOp(id, skip, arg, k) a suspended `do op(arg)` whose continuation is k
//
// `ebind` threads a continuation through this representation. Each `handle`
// becomes a recursive driver that pattern-matches the result: EPure runs the
// return clause, EOp dispatches to the matching operation with `resume` bound
// to a closure that re-enters the driver. Because `k` is an ordinary reusable
// closure, resumptions are multishot.
//
// A handler is "open" when its body performs effects it does not itself
// catch: the driver then forwards (re-emits) the unhandled `EOp` outward with
// a continuation that re-enters this driver, so an outer handler discharges it
// and resumption flows back through here. Open drivers return Eff values and
// their clauses are monadified. "Closed" drivers (the common case, including
// the parameter-passing `k(v)(s)` idiom) return bare values and are unchanged.
//
// When effectful code escapes first-class through a thunk, no static analysis
// can tell monadified callees apart at dynamic call sites, so lowering falls
// back to whole-program monadic mode: every function, lambda and thunk body is
// monadified, every handler is driven open-style, and `main` unwraps the final
// EPure, trapping on an op that reaches the top like the interpreter's
// unhandled-effect error.
//
// Mask is an explicit depth, mirroring the interpreter's `skip` counter
// (`eval/mod.rs`): an in-flight `EOp` carries `skip`, the number of matching
// handlers it must still bypass. A mask driver increments `skip` on ops of its
// effect passing through it. A handler driver matches purely on `id` equality;
// when an op is its own but `skip > 0`, it forwards with `skip - 1`, consuming
// one level, exactly as the interpreter decrements on a `Frame::Handle`
// crossing. Fresh ops start at `skip = 0`.

const PURE_TAG: usize = 0;
const OP_TAG: usize = 1;
// Type name carrying the free-monad result (its ctors are EPure/EOp).
const EFF: &str = "Eff";
const EPURE: &str = "EPure";
pub(crate) const EOP: &str = "EOp";
const EBIND: &str = "ebind";

// Step constructors for the state path's early-termination protocol: a fused
// producer threads `Step S` and stops when `stake` yields `SDone`.
const MORE_TAG: usize = 0;
const DONE_TAG: usize = 1;
// Type name carrying the early-termination step (its ctors are SMore/SDone).
const STEP: &str = "Step";
pub(super) const SMORE: &str = "SMore";
pub(super) const SDONE: &str = "SDone";

// A latent op with the mask depth at which it is in flight: `depth` handlers of
// its effect must still be skipped. Replaces the old `op#d` string encoding.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct MaskOp {
    pub id: Sym,
    pub depth: u32,
}

// Per-function set of effect ops still latent in its body (used to decide which
// handlers are open).
type Latent = BTreeMap<Sym, BTreeSet<MaskOp>>;

// Evidence environment: the op id in scope mapped to the variable currently
// holding its active clause. Keyed by id so iteration is in ascending order,
// keeping evidence parameter order agreed between callers and callees.
type Env = BTreeMap<i64, Sym>;

struct Lowerer {
    op_ids: BTreeMap<Sym, i64>,
    eff: BTreeSet<Sym>,
    full: bool,
    arities: BTreeMap<Sym, usize>,
    latent: Latent,
    flow: flow::ThunkFlow,
    resume_aliases: BTreeSet<Sym>,
    fresh: Fresh,
    generated: Vec<CoreFn>,
    // Set by the state path when a `stake`-style early-terminating handler is
    // present: producers then thread `Step S` and check it after each emit.
    early: bool,
}

/// # Panics
/// Panics only if a program declares more than `i64::MAX` distinct effect ops.
///
/// # Errors
/// Returns [`TypeError::Ice`] if lowering reaches an internal inconsistency: an
/// op or effectful callee missing from the tables built during setup, or a
/// monadified tail that is not Eff-shaped (a compiler bug surfaced as an error
/// rather than a panic).
pub fn lower(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<(Core, BTreeMap<String, CtorInfo>), TypeError> {
    // Dead prelude code must not flip the program into monadic mode, so only
    // functions reachable from main are lowered (and kept) at all.
    let shaken;
    let core = if core.fns.iter().any(|f| f.name == ENTRY_POINT) {
        let live = reachable_fns(core);
        shaken = Core {
            fns: core
                .fns
                .iter()
                .filter(|f| live.contains(&f.name))
                .cloned()
                .collect(),
        };
        &shaken
    } else {
        core
    };
    if !core.fns.iter().any(|f| raw_effects(&f.body)) {
        return Ok((core.clone(), ctors.clone()));
    }

    let mut op_set = BTreeSet::new();
    for f in &core.fns {
        collect_ops(&f.body, &mut op_set);
    }
    // Ids are assigned in alphabetical name order (a BTreeSet<Sym> orders by
    // intern id, which is first-seen, so sort by name explicitly to keep the
    // ev@<id> and trap order stable).
    let mut ops_sorted: Vec<Sym> = op_set.into_iter().collect();
    ops_sorted.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    let op_ids: BTreeMap<Sym, i64> = ops_sorted
        .into_iter()
        .enumerate()
        .map(|(i, n)| {
            i64::try_from(i)
                .map(|id| (n, id))
                .map_err(|_| TypeError::Ice {
                    msg: "more than i64::MAX effect ops".into(),
                })
        })
        .collect::<Result<_, _>>()?;

    let lat = latent_map(core);
    let (eff, full) = monadic_set(core, &lat);
    let thunk_flow = flow::analyze(core, &lat);
    let mut lo = Lowerer {
        op_ids,
        eff,
        full,
        arities: core.fns.iter().map(|f| (f.name, f.params.len())).collect(),
        latent: lat,
        flow: thunk_flow,
        resume_aliases: BTreeSet::new(),
        fresh: Fresh::new(),
        generated: Vec::new(),
        early: false,
    };

    // The two fusion paths and the free-monad fallback are three answer-type
    // strategies for the same evidence translation, tried in order of how little
    // they reify: the evidence path is the Identity answer (a clause is a plain
    // thunk, `do op` is `force(ev)(args)`, resume is a direct return); the state
    // path is the State answer (a clause is a transformer `\(args, acc) -> acc'`,
    // producers thread an accumulator, and `stake` adds a `Step` short-circuit);
    // the free monad reifies the continuation when neither answer fits. They are
    // kept as separate passes deliberately: the Identity translation threads
    // values through ordinary CBPV bind, while the State translation threads an
    // explicit accumulator and splits consumer from producer, so the core `Bind`
    // and `do op` handling genuinely differs rather than sharing one traversal.
    // What they do share, the static eligibility prologue, is factored into
    // [`Lowerer::fusion_handles`].
    //
    // The evidence path subsumes the free monad whenever it applies: every
    // reachable handler tail-resumptive and every escaping effectful thunk
    // trackable to its force sites. It fully succeeds or returns None, falling
    // back here with no state to undo.
    if let Some(lowered) = lo.try_lower_ev(core) {
        return Ok((lowered, ctors.clone()));
    }
    if let Some(lowered) = lo.try_lower_state(core) {
        let mut ctors = ctors.clone();
        if lo.early {
            ctors.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
            ctors.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
        }
        return Ok((lowered, ctors));
    }

    let mut fns: Vec<CoreFn> = core
        .fns
        .iter()
        .map(|f| {
            let body = if lo.eff.contains(&f.name) {
                lo.mon(&f.body)?
            } else {
                lo.lower_comp(&f.body)?
            };
            // Trap an effect that escaped every handler whenever `main` is
            // monadified, not only in whole-program mode: in selective mode an
            // unhandled effect leaves `main` in `eff` and its `EOp` would
            // otherwise flow out as a bare value, silently diverging from the
            // interpreter, which raises `unhandled effect`.
            let body = if f.name == ENTRY_POINT && lo.eff.contains(&f.name) {
                lo.unwrap_main(body)
            } else {
                body
            };
            Ok(CoreFn {
                name: f.name,
                params: f.params.clone(),
                body,
            })
        })
        .collect::<Result<_, TypeError>>()?;
    let gen_start = fns.len();
    fns.extend(lo.generated);
    fns.push(ebind_fn());
    if lo.full {
        check_monadified(&fns)?;
    }
    debug_assert_templates_closed(&fns, gen_start);

    let mut ctors = ctors.clone();
    ctors.insert(EPURE.into(), synth_ctor(EFF, PURE_TAG, 1));
    ctors.insert(EOP.into(), synth_ctor(EFF, OP_TAG, 4));

    Ok((Core { fns }, ctors))
}

impl Lowerer {
    // Every op reaching lowering was assigned an id by collect_ops. Aliasing
    // a missed op to id 0 would silently misroute handler dispatch.
    fn op_id(&self, op: Sym) -> Result<i64, TypeError> {
        self.op_ids.get(&op).copied().ok_or_else(|| TypeError::Ice {
            msg: format!("effect op `{op}` escaped collect_ops"),
        })
    }

    fn fresh(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }

    // A right-associative `id == k` cascade: for each op, when `scrut` equals
    // its id run the branch `make` produces, else fall through to the next. The
    // last falls through to `fallthrough`. Built back-to-front (each branch then
    // its test var) so the emitted tree and fresh-var order are exactly the
    // hand-rolled form. Drives all three dispatch sites (handler/forward/mask).
    fn build_op_chain(
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

    // A handler is open when its body performs an effect it does not catch.
    // Whole-program mode drives every handler open-style for uniformity.
    fn is_open(&self, body: &Comp, ops: &[HandleOp]) -> bool {
        if self.full {
            return true;
        }
        let mut s = BTreeSet::new();
        latent(body, &self.latent, &mut s);
        for op in ops {
            s.remove(&MaskOp {
                id: op.name,
                depth: 0,
            });
        }
        !s.is_empty()
    }

    fn is_resume_app(&self, f: &Comp) -> bool {
        matches!(f, Comp::Force(Value::Var(v)) if self.resume_aliases.contains(v))
    }

    // Structural pass over the whole program: rewrite every `handle` into a
    // call to a generated driver, leaving non-effectful code untouched.
    fn lower_comp(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        Ok(match c {
            Comp::Handle { body, ops, .. } if self.is_open(body, ops) => {
                let e = self.fresh("e");
                let x = self.fresh("ex");
                Comp::Bind(
                    Box::new(self.lower_handle(c)?),
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
            Comp::Handle { .. } => self.lower_handle(c)?,
            // A mask reached outside monadic context has no escaping ops to
            // relabel, so it is the identity on its body.
            Comp::Mask(_, b) => self.lower_comp(b)?,
            Comp::Bind(m, x, n) => Comp::Bind(
                Box::new(self.lower_comp(m)?),
                *x,
                Box::new(self.lower_comp(n)?),
            ),
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
    fn mon(&mut self, c: &Comp) -> Result<Comp, TypeError> {
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
                let resume = Value::Thunk(Box::new(Comp::Lam(
                    vec![names::RESUME_VAL.into()],
                    Box::new(epure(Value::Var(names::RESUME_VAL.into()))),
                )));
                Comp::Return(Value::Ctor(
                    EOP.into(),
                    OP_TAG,
                    vec![Value::Int(id), Value::Int(0), arg, resume],
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
            // Applying the current resume already yields an Eff value (the
            // re-driven continuation), so thread it instead of EPure-wrapping.
            Comp::App(f, args) if self.is_resume_app(f) => Comp::App(f.clone(), args.clone()),
            // In whole-program mode every closure body is monadic, so any
            // dynamic application already yields an Eff value.
            Comp::App(f, args) if self.full => Comp::App(
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
            Comp::Handle { body, ops, .. } if self.is_open(body, ops) => self.lower_handle(c)?,
            Comp::Handle { .. } => {
                let v = self.fresh("h");
                Comp::Bind(
                    Box::new(self.lower_handle(c)?),
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
                let arity = self.arities.get(g).copied().ok_or_else(|| TypeError::Ice {
                    msg: format!("effectful call to unknown function `{g}`"),
                })?;
                let partial = self.full && args.len() < arity;
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
    fn mon_value(&mut self, v: &Value) -> Result<Value, TypeError> {
        if !self.full {
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

    fn mon_head(&mut self, f: &Comp) -> Result<Comp, TypeError> {
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

    // Whole-program mode leaves `main` monadic; unwrap the final EPure and
    // trap on an op that escaped every handler, naming it like the
    // interpreter's unhandled-effect error.
    fn unwrap_main(&mut self, body: Comp) -> Comp {
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

    fn lower_handle(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = c
        else {
            return Ok(c.clone());
        };

        // Free variables of the handler arms become extra parameters threaded
        // through the driver and every resumption.
        let mut fvs = BTreeSet::new();
        if let Some(rb) = return_body {
            fvs.extend(fv::comp_without(rb, return_var.iter()));
        }
        for op in ops {
            let mut s = fv::comp_without(&op.body, &op.params);
            s.remove(&op.resume);
            fvs.extend(s);
        }
        // `Sym` orders by intern id. Sort the captured free vars by name so the
        // driver's parameter and resumption-argument order stays byte-stable.
        let mut fvs: Vec<Sym> = fvs.into_iter().collect();
        fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        let open = self.is_open(body, ops);

        let driver = self.fresh("handle");
        let res = self.fresh("res");

        // EPure(x) => run return clause. Open drivers return Eff, so the return
        // body is monadified and a bare result is lifted with EPure.
        let x = self.fresh("x");
        let pure_body = match (return_var, return_body) {
            (Some(rv), Some(rb)) => {
                let rbody = if open {
                    self.mon(rb)?
                } else {
                    self.lower_comp(rb)?
                };
                Comp::Bind(Box::new(Comp::Return(Value::Var(x))), *rv, Box::new(rbody))
            }
            _ if open => epure(Value::Var(x)),
            _ => Comp::Return(Value::Var(x)),
        };
        let pure_arm = (ctor_pat(EPURE, &[x]), pure_body);

        // EOp(id, skip, arg, k) => dispatch on id
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");

        let mut resume_args = vec![Value::Var(names::RESUME_KONT.into())];
        resume_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        let resume_thunk = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::App(
                    Box::new(Comp::Force(Value::Var(k))),
                    vec![Value::Var(names::RESUME_VAL.into())],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(driver, resume_args)),
            )),
        )));

        // Unhandled op (id not ours): closed handlers cannot reach here, open
        // handlers forward by re-emitting the EOp unchanged with a continuation
        // that re-enters this driver, so an enclosing handler discharges it.
        let mut dispatch = if open {
            Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![
                    Value::Var(id),
                    Value::Var(skip),
                    Value::Var(arg),
                    resume_thunk.clone(),
                ],
            ))
        } else {
            Comp::Error(Value::Str(
                "ICE: unhandled effect op in closed handler dispatch".into(),
            ))
        };
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let rt = &resume_thunk;
        dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let op = &ops[i];
                let mut handler = if open {
                    let saved = std::mem::take(&mut me.resume_aliases);
                    me.resume_aliases.insert(op.resume);
                    let h = me.mon(&op.body);
                    me.resume_aliases = saved;
                    h?
                } else {
                    me.lower_comp(&op.body)?
                };
                // bind operation parameters from arg (tuple-unpacked when n-ary)
                handler = bind_params(&op.params, arg, handler);
                // bind resume
                let handle = Comp::Bind(
                    Box::new(Comp::Return(rt.clone())),
                    op.resume,
                    Box::new(handler),
                );
                // A closed handler's own ops always arrive at skip 0 (a masked
                // op of its effect keeps the handler open, by `is_open`), so it
                // handles directly. An open handler may receive one masked past
                // it (skip > 0): forward with one fewer level and re-enter this
                // driver on resume, mirroring the interpreter decrementing `skip`
                // on a matching handler crossing.
                if !open {
                    return Ok(handle);
                }
                let sk1 = me.fresh("sk");
                let forward = Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Sub, Value::Var(skip), Value::Int(1))),
                    sk1,
                    Box::new(Comp::Return(Value::Ctor(
                        EOP.into(),
                        OP_TAG,
                        vec![Value::Var(id), Value::Var(sk1), Value::Var(arg), rt.clone()],
                    ))),
                );
                let z = me.fresh("z");
                Ok(Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Eq, Value::Var(skip), Value::Int(0))),
                    z,
                    Box::new(Comp::If(Value::Var(z), Box::new(handle), Box::new(forward))),
                ))
            },
            dispatch,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let body_case = Comp::Case(Value::Var(res), vec![pure_arm, op_arm]);

        let mut params = vec![res];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: driver,
            params,
            body: body_case,
        });

        // call site: run the monadified body, then drive it
        let r0 = self.fresh("r0");
        let mut call_args = vec![Value::Var(r0)];
        call_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        Ok(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(Comp::Call(driver, call_args)),
        ))
    }

    // mask<Eff> becomes a driver that handles nothing: it adds N to the id of
    // every Eff op flowing through it, so the next driver of that effect
    // misses its equality match once and forwards with id - N.
    //
    // Closed top-level template: its binders are the fixed `names::*` set and it
    // never nests another template's body, so the fixed binders cannot capture
    // (checked by `debug_assert_templates_closed`).
    fn mask_driver(&mut self, ops: &[Sym]) -> Result<Sym, TypeError> {
        let driver = self.fresh("mask");
        let resume = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::App(
                    Box::new(Comp::Force(Value::Var(names::CONT.into()))),
                    vec![Value::Var(names::RESUME_VAL.into())],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(
                    driver,
                    vec![Value::Var(names::RESUME_KONT.into())],
                )),
            )),
        )));
        let reemit = |skipv: Value| {
            Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![
                    Value::Var(names::OP_ID.into()),
                    skipv,
                    Value::Var(names::OP_ARG.into()),
                    resume.clone(),
                ],
            ))
        };
        // An op of the masked effect gains one skip level, so the next matching
        // handler bypasses it once. Any other op passes through unchanged.
        let bump = Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Add,
                Value::Var(names::OP_SKIP.into()),
                Value::Int(1),
            )),
            names::FWD_SKIP.into(),
            Box::new(reemit(Value::Var(names::FWD_SKIP.into()))),
        );
        let fwd = reemit(Value::Var(names::OP_SKIP.into()));
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(*op))
            .collect::<Result<_, _>>()?;
        let dispatch = self.build_op_chain(
            &Value::Var(names::OP_ID.into()),
            &ids,
            |_, _| Ok(bump.clone()),
            fwd,
        )?;
        let pure_arm = (
            ctor_pat(EPURE, &[names::COMPOSE.into()]),
            epure(Value::Var(names::COMPOSE.into())),
        );
        let op_arm = (
            ctor_pat(
                EOP,
                &[
                    names::OP_ID.into(),
                    names::OP_SKIP.into(),
                    names::OP_ARG.into(),
                    names::CONT.into(),
                ],
            ),
            dispatch,
        );
        self.generated.push(CoreFn {
            name: driver,
            params: vec![names::RET.into()],
            body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
        });
        Ok(driver)
    }
}

fn bind_params(params: &[Sym], arg: Sym, body: Comp) -> Comp {
    match params.len() {
        0 => body,
        1 => Comp::Bind(
            Box::new(Comp::Return(Value::Var(arg))),
            params[0],
            Box::new(body),
        ),
        _ => {
            let binders = params.iter().map(|p| Some(*p)).collect();
            Comp::Case(Value::Var(arg), vec![(CorePat::Tuple(binders), body)])
        }
    }
}

fn epure(v: Value) -> Comp {
    Comp::Return(Value::Ctor(EPURE.into(), PURE_TAG, vec![v]))
}

// fn ebind(r, f) =
//   case r {
//     EPure(x)     => force(f)(x),
//     EOp(id,a,k)  => EOp(id, a, \y. ebind(force(k)(y), f)),
//   }
//
// Closed top-level template: its binders (`names::OP_ID`/`OP_ARG`/`CONT`/
// `EBIND_FN`/`RESUME_VAL`/`RESUME_KONT`) are fixed. Templates refer to one another
// by `Call`, never by lexical nesting, so the fixed binders cannot capture across
// templates; do not emit one template's body inside another. The closedness this
// relies on is checked by `debug_assert_templates_closed`, not just argued here.
fn ebind_fn() -> CoreFn {
    let pure_arm = (
        ctor_pat(EPURE, &[names::COMPOSE.into()]),
        Comp::App(
            Box::new(Comp::Force(Value::Var(names::EBIND_FN.into()))),
            vec![Value::Var(names::COMPOSE.into())],
        ),
    );
    let resume = Value::Thunk(Box::new(Comp::Lam(
        vec![names::RESUME_VAL.into()],
        Box::new(Comp::Bind(
            Box::new(Comp::App(
                Box::new(Comp::Force(Value::Var(names::CONT.into()))),
                vec![Value::Var(names::RESUME_VAL.into())],
            )),
            names::RESUME_KONT.into(),
            Box::new(Comp::Call(
                EBIND.into(),
                vec![
                    Value::Var(names::RESUME_KONT.into()),
                    Value::Var(names::EBIND_FN.into()),
                ],
            )),
        )),
    )));
    let op_arm = (
        ctor_pat(
            EOP,
            &[
                names::OP_ID.into(),
                names::OP_SKIP.into(),
                names::OP_ARG.into(),
                names::CONT.into(),
            ],
        ),
        Comp::Return(Value::Ctor(
            EOP.into(),
            OP_TAG,
            vec![
                Value::Var(names::OP_ID.into()),
                Value::Var(names::OP_SKIP.into()),
                Value::Var(names::OP_ARG.into()),
                resume,
            ],
        )),
    );
    CoreFn {
        name: EBIND.into(),
        params: vec![names::RET.into(), names::EBIND_FN.into()],
        body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
    }
}

fn ctor_pat(name: &str, vars: &[Sym]) -> CorePat {
    CorePat::Ctor(Sym::from(name), vars.iter().map(|v| Some(*v)).collect())
}

fn synth_ctor(type_name: &str, tag: usize, n: usize) -> CtorInfo {
    CtorInfo {
        type_name: type_name.into(),
        params: vec![],
        args: vec![Type::Int; n],
        tag,
        fields: vec![],
    }
}

// Per-function set of effect ops still latent in its body, with the mask depth
// dropped: the op identities the call-graph fixpoint believes each function can
// still perform. Exposed for the driver's effect-engine reconciliation check.
#[must_use]
pub fn latent_ops(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
    latent_map(core)
        .into_iter()
        .map(|(f, ops)| (f, ops.into_iter().map(|o| o.id).collect()))
        .collect()
}

fn latent_map(core: &Core) -> Latent {
    // The latent ops of each function are a least fixpoint over the call graph:
    // a function's set is the ops it performs directly plus those latent in its
    // callees. `least_fixpoint` grows each set monotonically to convergence, so
    // termination is structural (no iteration ceiling needed).
    let seed: Latent = core.fns.iter().map(|f| (f.name, BTreeSet::new())).collect();
    let bodies: BTreeMap<Sym, &Comp> = core.fns.iter().map(|f| (f.name, &f.body)).collect();
    crate::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut s = BTreeSet::new();
        latent(bodies[name], cur, &mut s);
        s
    })
}

// Selective mode monadifies only functions that perform or propagate an
// effect. When effectful code escapes first-class through a thunk (a call to
// an effectful function, or a raw do/handle inside a closure body), dynamic
// call sites cannot tell conventions apart, so switch to whole-program mode
// and monadify everything. check_monadified enforces the resulting invariant
// after the rewrite.
fn monadic_set(core: &Core, fl: &Latent) -> (BTreeSet<Sym>, bool) {
    let eff: BTreeSet<Sym> = fl
        .iter()
        .filter(|(_, s)| !s.is_empty())
        .map(|(n, _)| *n)
        .collect();
    let mut thunks = Vec::new();
    for f in &core.fns {
        thunks_in_comp(&f.body, &mut thunks);
    }
    let escapes = thunks.iter().any(|body| {
        let mut heads = BTreeSet::new();
        all_calls(body, &mut heads);
        !heads.is_disjoint(&eff) || raw_effects(body)
    }) || core.fns.iter().any(|f| open_resume_escapes(&f.body, fl));
    if escapes {
        (core.fns.iter().map(|f| f.name).collect(), true)
    } else {
        (eff, false)
    }
}

// An open handler whose resume escapes into a closure (the parameter-passing
// k(v)(s) idiom with a foreign effect passing through) has a function-typed
// answer that surfaces Eff values when forced later, so its applications need
// the uniform whole-program calling convention.
fn open_resume_escapes(c: &Comp, fl: &Latent) -> bool {
    if let Comp::Handle { body, ops, .. } = c {
        let mut s = BTreeSet::new();
        latent(body, fl, &mut s);
        for op in ops {
            s.remove(&MaskOp {
                id: op.name,
                depth: 0,
            });
        }
        if !s.is_empty() && ops.iter().any(|op| resume_in_thunk(&op.body, op.resume)) {
            return true;
        }
    }
    let mut found = false;
    each_subcomp(c, &mut |sc| found |= open_resume_escapes(sc, fl));
    found
}

fn resume_in_thunk(c: &Comp, resume: Sym) -> bool {
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= fv::comp(t).contains(&resume);
        }
    });
    each_subcomp(c, &mut |sc| found |= resume_in_thunk(sc, resume));
    found
}

// Template hygiene, mechanically. Every effect-dispatch template appended above
// (`fns[gen_start..]`: the per-handler drivers, the mask drivers, and `ebind`) is
// a closed top-level function. Its binders are the fixed `names::*` set plus its
// own params and captured free vars; when a driver splices another template's
// body it binds that body's free names as params. The hygiene the comments claim
// is exactly: after removing a template's own params and binders, every name left
// free is the name of another top-level function it calls, never a leftover
// binder. `fv::comp_without` removes the params (it already discounts internal
// lambda/let/case/handler binders), so the residue must be a subset of the
// top-level names. A binder that captured a sub-template's free occurrence, or a
// driver that failed to capture one, leaves a dangling name and trips this in
// debug builds, instead of miscompiling silently at a distant call site. Release
// builds skip it; the cost is debug-only.
fn debug_assert_templates_closed(fns: &[CoreFn], gen_start: usize) {
    if !cfg!(debug_assertions) {
        return;
    }
    let known: BTreeSet<Sym> = fns.iter().map(|f| f.name).collect();
    for t in &fns[gen_start..] {
        let leaked: Vec<Sym> = fv::comp_without(&t.body, &t.params)
            .into_iter()
            .filter(|v| !known.contains(v))
            .collect();
        assert!(
            leaked.is_empty(),
            "effect-lowering template `{}` is not hygienic: {leaked:?} are neither its \
             binders nor top-level functions (a template binder captured a free occurrence \
             or a driver failed to bind one)",
            t.name,
        );
    }
}

// Escalation invariant: after whole-program monadification every function
// body and every thunk body (under its lambda binder, if any) finishes with
// an Eff value at each tail: an EPure/EOp construction, a saturated call to
// a program function (itself Eff-tailed by induction), a dynamic application
// of a closure (every closure body is monadified), or a diverging Error.
// `main` is exempt because unwrap_main strips its final EPure. A function
// the rewrite missed shows up here instead of as a miscompile at a distant
// dynamic call site.
fn check_monadified(fns: &[CoreFn]) -> Result<(), TypeError> {
    let arities: BTreeMap<&str, usize> = fns
        .iter()
        .map(|f| (f.name.as_str(), f.params.len()))
        .collect();
    for f in fns {
        if f.name != ENTRY_POINT {
            check_tails(f.name.as_str(), &f.body, &arities)?;
        }
        let mut ts = Vec::new();
        thunks_in_comp(&f.body, &mut ts);
        for t in ts {
            let b = if let Comp::Lam(_, b) = t { b } else { t };
            check_tails(f.name.as_str(), b, &arities)?;
        }
    }
    Ok(())
}

fn check_tails(fname: &str, c: &Comp, arities: &BTreeMap<&str, usize>) -> Result<(), TypeError> {
    match c {
        Comp::Bind(_, _, n) => check_tails(fname, n, arities)?,
        Comp::If(_, t, e) => {
            check_tails(fname, t, arities)?;
            check_tails(fname, e, arities)?;
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                check_tails(fname, b, arities)?;
            }
        }
        Comp::Return(Value::Ctor(n, ..)) if n == EPURE || n == EOP => {}
        Comp::Call(g, args) if g != ENTRY_POINT && arities.get(g.as_str()) == Some(&args.len()) => {
        }
        Comp::App(..) | Comp::Error(_) => {}
        other => {
            return Err(TypeError::Ice {
                msg: format!(
                    "monadification: `{fname}` tail is not Eff-shaped: {}",
                    other.kind()
                ),
            });
        }
    }
    Ok(())
}

// Invariant check: between selective and whole-program mode, lowering must
// eliminate every `do` and `handle`. A survivor is a compiler bug.
/// # Errors
/// Fails if any `do` or `handle` survives lowering.
pub fn residual_effects(core: &Core) -> Result<(), String> {
    for f in &core.fns {
        if raw_effects(&f.body) {
            return Err(format!("residual effect in `{}` after lowering", f.name));
        }
    }
    Ok(())
}

fn raw_effects(c: &Comp) -> bool {
    if matches!(c, Comp::Do(..) | Comp::Handle { .. } | Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| found |= raw_effects_value(v));
    each_subcomp(c, &mut |sc| found |= raw_effects(sc));
    found
}

fn raw_effects_value(v: &Value) -> bool {
    match v {
        Value::Thunk(c) => raw_effects(c),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(raw_effects_value),
        _ => false,
    }
}

fn all_calls(c: &Comp, out: &mut BTreeSet<Sym>) {
    if let Comp::Call(g, _) = c {
        out.insert(*g);
    }
    each_subcomp(c, &mut |sc| all_calls(sc, out));
}

fn thunks_in_comp<'a>(c: &'a Comp, out: &mut Vec<&'a Comp>) {
    each_value(c, &mut |v| thunks_in_value(v, out));
    each_subcomp(c, &mut |sc| thunks_in_comp(sc, out));
}

fn thunks_in_value<'a>(v: &'a Value, out: &mut Vec<&'a Comp>) {
    match v {
        Value::Thunk(c) => {
            out.push(c);
            thunks_in_comp(c, out);
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                thunks_in_value(f, out);
            }
        }
        _ => {}
    }
}

fn each_value<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Value)) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::ReuseToken(v)
        | Comp::If(v, ..)
        | Comp::Case(v, _) => f(v),
        Comp::Reuse(a, b) | Comp::Prim(_, a, b) => {
            f(a);
            f(b);
        }
        Comp::App(_, args)
        | Comp::Call(_, args)
        | Comp::Do(_, args)
        | Comp::StrBuiltin(_, args) => {
            for a in args {
                f(a);
            }
        }
        _ => {}
    }
}

fn each_subcomp<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Comp)) {
    match c {
        Comp::Bind(m, _, n) => {
            f(m);
            f(n);
        }
        Comp::Lam(_, b) | Comp::Mask(_, b) => f(b),
        Comp::App(g, _) => f(g),
        Comp::If(_, t, e) => {
            f(t);
            f(e);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                f(b);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            f(body);
            if let Some(rb) = return_body {
                f(rb);
            }
            for o in ops {
                f(&o.body);
            }
        }
        _ => {}
    }
}

fn contains_mask(c: &Comp) -> bool {
    if matches!(c, Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        found |= ts.iter().any(|t| contains_mask(t));
    });
    each_subcomp(c, &mut |sc| found |= contains_mask(sc));
    found
}

// Latent sets track mask depth in a `MaskOp { id, depth }`: depth d means d
// handlers of the op's effect must still be skipped. A handler removes its ops
// at depth 0 and peels one level off deeper ones; a mask pushes its ops one
// level down.
fn latent(c: &Comp, fl: &Latent, out: &mut BTreeSet<MaskOp>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(MaskOp { id: *op, depth: 0 });
        }
        Comp::Call(g, _) => {
            if let Some(s) = fl.get(g) {
                out.extend(s.iter().copied());
            }
        }
        Comp::Bind(m, _, n) => {
            latent(m, fl, out);
            latent(n, fl, out);
        }
        Comp::If(_, t, e) => {
            latent(t, fl, out);
            latent(e, fl, out);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                latent(b, fl, out);
            }
        }
        Comp::App(f, _) => latent(f, fl, out),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            let mut inner = BTreeSet::new();
            latent(body, fl, &mut inner);
            for op in ops {
                inner.remove(&MaskOp {
                    id: op.name,
                    depth: 0,
                });
            }
            out.extend(inner.into_iter().map(|l| {
                if ops.iter().any(|op| op.name == l.id) {
                    MaskOp {
                        id: l.id,
                        depth: l.depth - 1,
                    }
                } else {
                    l
                }
            }));
            if let Some(rb) = return_body {
                latent(rb, fl, out);
            }
            for op in ops {
                // A parameter-passing clause returns a transformer thunk that the
                // handler driver then applies, so the ops it re-performs (a
                // `stake`-style `\acc -> { do op(..); resume(..) }`) are latent
                // here, not hidden behind the thunk.
                match &op.body {
                    Comp::Return(Value::Thunk(t)) => {
                        let inner = if let Comp::Lam(_, b) = t.as_ref() {
                            b
                        } else {
                            t
                        };
                        latent(inner, fl, out);
                    }
                    _ => latent(&op.body, fl, out),
                }
            }
        }
        Comp::Mask(ops, body) => {
            let mut inner = BTreeSet::new();
            latent(body, fl, &mut inner);
            out.extend(inner.into_iter().map(|l| {
                if ops.contains(&l.id) {
                    MaskOp {
                        id: l.id,
                        depth: l.depth + 1,
                    }
                } else {
                    l
                }
            }));
        }
        _ => {}
    }
}

fn collect_ops(c: &Comp, out: &mut BTreeSet<Sym>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(*op);
        }
        Comp::Handle { ops, .. } => {
            for op in ops {
                out.insert(op.name);
            }
        }
        Comp::Mask(ops, _) => out.extend(ops.iter().copied()),
        _ => {}
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            collect_ops(t, out);
        }
    });
    each_subcomp(c, &mut |sc| collect_ops(sc, out));
}
