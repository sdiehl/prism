//! Evidence passing: the signature prepass.
//!
//! When every reachable handler is tail-resumptive, no continuation is ever
//! reified. Each op carries its active clause as evidence: a thunk bound at
//! the handle site (the clause body with its tail `resume(v)` replaced by
//! `return v`), `do op(args)` becomes `force(ev@<id>)(args)`, and every
//! effectful callable takes the evidence for the ops latent in it as extra
//! parameters, so each perform site reaches the clause active where its
//! handler was installed.
//!
//! The typed port's real work is signature rewriting, not term traversal, so
//! it happens once here, before any body is touched. Each callable that gains
//! evidence gains **one** ambient residual-row quantifier: an [`EffRow`]
//! carries a single open tail, and every active clause row is a subrow of the
//! same surrounding residual, so one ambient row is both sufficient and the
//! only thing the row language can express. A clause thunk whose own row is
//! narrower inhabits the ambient parameter type because a thunk is covariant
//! in its row, which the independent verifier already proves.
//!
//! The ambient quantifier is witness-only: it never reaches compatibility
//! Core, so it draws from its own [`names::FRESH_EVIDENCE_ROW`] namespace
//! rather than the term counter that fixes generated names and tick order.

use std::collections::{BTreeMap, BTreeSet};

use crate::fresh::Fresh;
use crate::names::{self, ENTRY_POINT, FRESH_EVIDENCE_ROW};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::verify::{instantiate_fn, rename_bound_core, VerifyEnv};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedHandleOp, TypedHandler, TypedValue, TypedValueKind,
};
use super::diagnostics::DriftLog;
use super::flow::{Loc, ThunkFlow};
use super::latent::Latent;

/// The effect ops of a program, numbered alphabetically by name so
/// `ev@<id>` ordering and trap order are stable across compilations.
pub(super) struct OpIds(BTreeMap<Sym, i64>);

impl OpIds {
    /// Assign every op an id. `None` when a program declares more ops than an
    /// `i64` can number.
    pub(super) fn assign(ops: &BTreeSet<Sym>) -> Option<Self> {
        let mut sorted: Vec<Sym> = ops.iter().copied().collect();
        sorted.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        sorted
            .into_iter()
            .enumerate()
            .map(|(i, name)| i64::try_from(i).ok().map(|id| (name, id)))
            .collect::<Option<BTreeMap<_, _>>>()
            .map(Self)
    }

    pub(super) fn id(&self, op: Sym) -> Option<i64> {
        self.0.get(&op).copied()
    }

    /// The inverse of [`id`](Self::id).
    pub(super) fn op(&self, id: i64) -> Option<Sym> {
        self.0.iter().find(|(_, v)| **v == id).map(|(k, _)| *k)
    }

    pub(super) fn iter(&self) -> impl DoubleEndedIterator<Item = (Sym, i64)> + '_ {
        self.0.iter().map(|(name, id)| (*name, *id))
    }

    /// Map a set of ops to their ids in ascending order. Force sites, thunk
    /// parameter lists, and effectful-call argument lists all use this one
    /// ordering, so evidence lines up positionally everywhere.
    pub(super) fn ids_of<'a>(&self, ops: impl IntoIterator<Item = &'a Sym>) -> Option<Vec<i64>> {
        let mut v: Vec<i64> = ops
            .into_iter()
            .map(|op| self.id(*op))
            .collect::<Option<_>>()?;
        v.sort_unstable();
        v.dedup();
        Some(v)
    }
}

/// One evidence parameter: the op it carries the active clause for, its
/// canonical `ev@<id>` binder, and the clause's function type bounded by the
/// callable's ambient row.
pub(super) struct EvidenceParam {
    pub(super) id: i64,
    pub(super) binder: TypedBinder,
}

/// How one callable's signature changes under evidence passing.
pub(super) struct FnPlan {
    /// The ambient residual row every clause this callable receives is bounded
    /// by, and which its own residual tail coalesces into. A callable that only
    /// returns an effectful thunk needs its result witness rewritten, but no
    /// outer evidence row of its own.
    pub(super) ambient: Option<Sym>,
    /// The evidence parameters, in ascending op-id order.
    pub(super) evidence: Vec<EvidenceParam>,
    /// The callable's own parameter types after any thunk witness the flow
    /// widened, so its binders can be re-typed to match what it now declares.
    pub(super) declared: Vec<CoreType>,
    /// The rewritten signature: original quantifiers, then the ambient row;
    /// original parameters, then the evidence.
    pub(super) sig: CoreFnSig,
}

/// The whole-program signature rewrite, computed before any body is rewritten
/// so a call site and its callee cannot disagree.
pub(super) struct EvidencePlan {
    fns: BTreeMap<Sym, FnPlan>,
}

impl EvidencePlan {
    pub(super) fn get(&self, name: Sym) -> Option<&FnPlan> {
        self.fns.get(&name)
    }

    /// Build the plan: every function latent in at least one op gains that
    /// op's evidence. `None` when an op escaped numbering or lacks a declared
    /// signature, which leaves the program to the general lowering.
    pub(super) fn build(
        fns: &[TypedCoreFn],
        latent: &Latent,
        flow: &ThunkFlow,
        ops: &OpIds,
        env: &VerifyEnv,
    ) -> Option<Self> {
        let mut rows = RowNames::new();
        let mut plans = BTreeMap::new();
        for f in fns {
            let ids = ops.ids_of(latent.get(&f.name())?.iter().map(|m| &m.id))?;
            let returned_ids = ops.ids_of(flow.ret.get(&f.name())?.iter().map(|m| &m.id))?;
            let rewritten_result = if returned_ids.is_empty() {
                None
            } else {
                Some(returned_thunk_evidence_type(
                    f.sig().body().result(),
                    &returned_ids,
                    ops,
                    env,
                )?)
            };
            // A callable with no latent op of its own can still take a thunk that
            // performs one, and that parameter's witness has to say so.
            let params = match evidence_params(f, flow, ops, env) {
                ParamPlan::Undescribable => return None,
                ParamPlan::Unchanged if ids.is_empty() && rewritten_result.is_none() => continue,
                ParamPlan::Unchanged => None,
                ParamPlan::Widened(params) => Some(params),
            };
            let needs_outer_ambient = !ids.is_empty() || params.is_some();
            plans.insert(
                f.name(),
                plan_fn(
                    f,
                    &ids,
                    params,
                    rewritten_result,
                    needs_outer_ambient,
                    ops,
                    env,
                    &mut rows,
                )?,
            );
        }
        Some(Self { fns: plans })
    }
}

// The rewritten parameter types of `f`, or `None` when no parameter carries a
// thunk that performs an operation.
//
// A thunk parameter's witness must describe the thunk that actually arrives.
// Once a thunk gains evidence parameters and its own ambient row, the declared
// type of the parameter it is passed to has to gain them too, or the callee's
// witness and its callers disagree. The quantifier is bound inside the parameter
// type rather than on the enclosing callable because it is the callee's force
// site, not its caller, that instantiates it.
fn evidence_params(f: &TypedCoreFn, flow: &ThunkFlow, ops: &OpIds, env: &VerifyEnv) -> ParamPlan {
    let Some(sigs) = flow.param.get(&f.name()) else {
        return ParamPlan::Undescribable;
    };
    let mut handled = BTreeSet::new();
    handled_effects(f.body(), env, &mut handled);
    let mut params = f.sig().params().to_vec();
    let mut rewrote = false;
    for (index, sig) in sigs.iter().enumerate() {
        let Some(declared) = params.get(index) else {
            // A missing witness for a parameter the flow calls effectful is a
            // shape this engine cannot describe; a pure one is simply unchanged.
            if sig.is_empty() {
                continue;
            }
            return ParamPlan::Undescribable;
        };
        if sig.is_empty() {
            // The flow never sees this thunk perform an op, but its declared row
            // may still name one this function handles (a caller passed a
            // strictly smaller-row thunk). Narrow the witness to the thunk that
            // actually arrives, stripping only the effects this function's own
            // handle discharges.
            if let Some(stripped) = strip_handled_thunk_type(declared, &handled) {
                params[index] = stripped;
                rewrote = true;
            }
            continue;
        }
        // A parameter the flow calls effectful but whose witness is not a thunk
        // of a function is one this engine cannot describe; say so rather than
        // guess at its shape.
        let Some(ids) = ops.ids_of(sig.iter().map(|m| &m.id)) else {
            return ParamPlan::Undescribable;
        };
        let Some(rewritten) = thunk_evidence_type(declared, &ids, &handled, ops, env) else {
            return ParamPlan::Undescribable;
        };
        params[index] = rewritten;
        rewrote = true;
    }
    if rewrote {
        ParamPlan::Widened(params)
    } else {
        ParamPlan::Unchanged
    }
}

/// What the flow says about a callable's parameters.
enum ParamPlan {
    /// No parameter carries a thunk that performs an operation.
    Unchanged,
    /// Every parameter type, with the effectful thunks re-witnessed.
    Widened(Vec<CoreType>),
    /// A parameter is effectful in a shape this engine cannot describe, so the
    /// program belongs to the general lowering rather than to evidence.
    Undescribable,
}

// Handlers run while constructing an escaping thunk are no longer dynamically
// active when its caller eventually forces it. The returned thunk's own row
// and `flow.ret` therefore determine the witness without subtracting
// producer-local handlers.
fn returned_thunk_evidence_type(
    declared: &CoreType,
    ids: &[i64],
    ops: &OpIds,
    env: &VerifyEnv,
) -> Option<CoreType> {
    thunk_evidence_type(declared, ids, &BTreeSet::new(), ops, env)
}

// A thunk-of-function witness, extended with the evidence its force site will
// supply: the clause parameters appended in the one ascending id order evidence
// is ever laid out in, under an ambient row named by those same ids so the
// caller's thunk and this parameter agree without sharing a counter.
fn thunk_evidence_type(
    declared: &CoreType,
    ids: &[i64],
    handled: &BTreeSet<Sym>,
    ops: &OpIds,
    env: &VerifyEnv,
) -> Option<CoreType> {
    let CoreType::Thunk(outer) = declared else {
        return None;
    };
    let CoreType::Function(inner) = outer.result() else {
        return None;
    };
    let ambient = Sym::from(names::evidence_row(ids));
    let mut quantifiers = inner.quantifiers().to_vec();
    quantifiers.push(CoreQuantifier::Row(ambient));
    let mut params = inner.params().to_vec();
    for id in ids {
        params.push(clause_type(
            ops.op(*id)?,
            inner.body().effects(),
            env,
            ambient,
        )?);
    }
    // The widened thunk's residual must match a callable's residual exactly:
    // a native, handler-less effect (IO) survives as an explicit label on top of
    // the ambient tail rather than being absorbed into it. Reuse `coalesce` so
    // the parameter type and the argument's own `coalesce`d signature agree.
    let mut body = coalesce(inner.body(), ambient, ids, ops, env);
    // The enclosing function's own handlers discharge more than this thunk
    // performs: an effect it handles but the thunk never itself performs (a
    // capability run_io handles while the thunk only performs a sibling one)
    // must still leave the widened row, exactly as the strip path does for a
    // flow-pure thunk. Otherwise the parameter keeps a label the body no longer
    // carries once handled.
    for label in handled {
        body = CompSig::new(
            body.result().clone(),
            super::subtract::subtract_row(body.effects(), *label),
        );
    }
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(quantifiers, params, body))),
        outer.effects().clone(),
    ))))
}

// The effects a computation handles anywhere in its body, read from each
// handler arm's operation. These are the labels this function's own handles
// discharge, so a thunk parameter forced under them need not carry them.
fn handled_effects(c: &TypedComp, env: &VerifyEnv, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Handle { ops, .. } = c.kind() {
        for arm in ops.arms() {
            if let Some(operation) = env.operation(arm.name()) {
                out.insert(operation.effect().name);
            }
        }
    }
    super::walk::each_value(c, &mut |v| {
        let mut ts = Vec::new();
        super::walk::thunks_in_value(v, &mut ts);
        for t in ts {
            handled_effects(t, env, out);
        }
    });
    super::walk::each_subcomp(c, &mut |sc| handled_effects(sc, env, out));
}

// A thunk-of-function witness with `handled` effects removed from its result
// row. When a caller passes a thunk that performs fewer effects than the
// parameter's declared row - a handler applied to a body that never performs the
// handled op, so the flow widens nothing - the un-widened parameter would keep a
// label this function's own handle already discharges, and the surviving label
// fails verification. Only labels this function HANDLES are stripped, never one
// that genuinely escapes it. Erasure drops rows, so narrowing the witness to the
// thunk that actually arrives cannot change the emitted program. `None` when the
// type is not a thunk of a function or names no handled op.
fn strip_handled_thunk_type(declared: &CoreType, handled: &BTreeSet<Sym>) -> Option<CoreType> {
    let CoreType::Thunk(outer) = declared else {
        return None;
    };
    let CoreType::Function(inner) = outer.result() else {
        return None;
    };
    let body = inner.body();
    let all = body.effects().labels();
    let kept: Vec<Label> = all
        .iter()
        .filter(|l| !handled.contains(&l.name))
        .map(|l| (*l).clone())
        .collect();
    if kept.len() == all.len() {
        return None;
    }
    let new_body = CompSig::new(
        body.result().clone(),
        EffRow::canonical(kept, body.effects().tail().clone()),
    );
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            inner.quantifiers().to_vec(),
            inner.params().to_vec(),
            new_body,
        ))),
        outer.effects().clone(),
    ))))
}

// One callable's plan.
#[allow(clippy::too_many_arguments)]
fn plan_fn(
    f: &TypedCoreFn,
    ids: &[i64],
    rewritten_params: Option<Vec<CoreType>>,
    rewritten_result: Option<CoreType>,
    needs_outer_ambient: bool,
    ops: &OpIds,
    env: &VerifyEnv,
    rows: &mut RowNames,
) -> Option<FnPlan> {
    let ambient = needs_outer_ambient.then(|| rows.next());
    let evidence: Vec<EvidenceParam> = match ambient {
        Some(ambient) => ids
            .iter()
            .map(|id| {
                let op = ops.op(*id)?;
                Some(EvidenceParam {
                    id: *id,
                    binder: TypedBinder::new(
                        Sym::from(names::ev(*id)),
                        clause_type(op, f.sig().body().effects(), env, ambient)?,
                    ),
                })
            })
            .collect::<Option<_>>()?,
        None => Vec::new(),
    };

    // Quantifiers: the original scheme, then the ambient row. The ambient goes
    // last so an existing instantiation's positional arguments do not move.
    let mut quantifiers = f.sig().quantifiers().to_vec();
    if let Some(ambient) = ambient {
        quantifiers.push(CoreQuantifier::Row(ambient));
    }

    // Any thunk parameter whose witness the flow widened is already rewritten;
    // this callable's own evidence appends after them.
    let mut params: Vec<CoreType> = rewritten_params.unwrap_or_else(|| f.sig().params().to_vec());
    // `coalesce` sets the declared body tail to `ambient`, but a widened thunk
    // parameter still tails on the function's source residual row variable, so a
    // force of it would keep that variable while the sig declares `ambient`.
    // Absorb the source residual tail into the ambient across the parameters so
    // the forced body row and the declared sig agree.
    if let Some(ambient) = ambient {
        if let EffRow::Var(src_tail) = f.sig().body().effects().tail() {
            if *src_tail != ambient {
                let old = CoreQuantifier::Row(*src_tail);
                params = params
                    .iter()
                    .map(|p| rename_bound_core(p, &old, ambient))
                    .collect();
            }
        }
    }
    let declared = params.clone();
    params.extend(evidence.iter().map(|e| e.binder.ty().clone()));
    let body = ambient.map_or_else(
        || f.sig().body().clone(),
        |ambient| coalesce(f.sig().body(), ambient, ids, ops, env),
    );
    let body = CompSig::new(
        rewritten_result.unwrap_or_else(|| body.result().clone()),
        body.effects().clone(),
    );

    Some(FnPlan {
        ambient,
        evidence,
        declared,
        sig: CoreFnSig::new(quantifiers, params, body),
    })
}

// The type of the evidence for one op at the instantiation named by the
// enclosing callable's effect row. An evidence parameter lives inside that
// callable's own scheme, so `Emit(a)` becomes a monomorphic clause over the
// outer `a`; re-quantifying the operation here would shadow it, while retaining
// the generic operation scheme would claim a concrete handler clause works at
// every instantiation. Rows that do not name one complete operation
// instantiation decline this fusion rung rather than inventing a partial one.
fn clause_type(op: Sym, effects: &EffRow, env: &VerifyEnv, ambient: Sym) -> Option<CoreType> {
    let sig = env.operation(op)?;
    let labels: Vec<_> = effects
        .labels()
        .into_iter()
        .filter(|label| label.name == sig.effect().name)
        .collect();
    let [label] = labels.as_slice() else {
        return None;
    };
    let instantiation: Vec<_> = label
        .args
        .iter()
        .cloned()
        .map(CoreInstantiation::Type)
        .collect();
    let declared = CoreFnSig::new(
        sig.quantifiers().to_vec(),
        sig.params().to_vec(),
        CompSig::new(sig.result().clone(), EffRow::Var(ambient)),
    );
    let applied = instantiate_fn(&declared, &instantiation).ok()?;
    let clause = CoreFnSig::new(
        Vec::new(),
        clause_params(applied.params()),
        applied.body().clone(),
    );
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(clause)),
        EffRow::Empty,
    ))))
}

/// A clause's parameters: the operation's own, or one unit parameter when the
/// operation is nullary. A clause is applied, and an application needs an
/// argument, so the nullary case takes the unit witness the perform site
/// passes. The clause type and the perform site must agree on this, so both
/// read it here.
pub(super) fn clause_params(declared: &[CoreType]) -> Vec<CoreType> {
    if declared.is_empty() {
        vec![CoreType::Source(Type::Unit)]
    } else {
        declared.to_vec()
    }
}

// A callable's residual after its evidence-passed ops are discharged: the ops
// leave its row, and whatever remains rides the ambient tail. An existing open
// tail coalesces into the ambient one rather than being unioned with it, since
// a row carries a single tail and every clause residual is a subrow of the same
// surrounding residual.
fn coalesce(body: &CompSig, ambient: Sym, ids: &[i64], ops: &OpIds, env: &VerifyEnv) -> CompSig {
    // An op's owning effect is a property of its declaration, so it is read
    // from the environment rather than recovered from a name.
    let discharged: BTreeSet<Sym> = ids
        .iter()
        .filter_map(|id| ops.op(*id))
        .filter_map(|op| env.operation(op).map(|sig| sig.effect().name))
        .collect();
    let labels = body
        .effects()
        .labels()
        .into_iter()
        .filter(|l| !discharged.contains(&l.name))
        .cloned();
    CompSig::new(
        body.result().clone(),
        EffRow::canonical(labels, EffRow::Var(ambient)),
    )
}

// The ambient row quantifiers, in their own deterministic namespace.
pub(super) struct RowNames(u32);

impl RowNames {
    pub(super) const fn new() -> Self {
        Self(0)
    }

    pub(super) fn next(&mut self) -> Sym {
        let name = Sym::from(names::fresh_binder(FRESH_EVIDENCE_ROW, self.0));
        self.0 += 1;
        name
    }
}

/// The alias set a clause's resumption is known by: its own binder, plus any
/// name a trivial `let` rebinds it to.
fn resume_set(resume: Sym) -> BTreeSet<Sym> {
    let mut s = BTreeSet::new();
    s.insert(resume);
    s
}

/// Rewrite a tail-resumptive clause body into a plain function body: drop the
/// `resume` binder (and any rebindings of it), and turn its single tail call
/// `resume(v)` into `return v`. `None` when the clause is not tail-resumptive
/// (resume captured, used off the tail, or some path never resumes), which is
/// exactly the evidence-eligibility test.
///
/// Post-condition guard: a successful strip erases the continuation, so no
/// resume alias may survive in the result. This enforces at the IR level the
/// structural assumption the matcher makes about elaborator output. An
/// upstream change that emitted a clause shape this matcher misreads (accepting
/// it yet leaving a live resume reference) must NOT be accepted: debug builds
/// panic so the drift is loud during development, and release builds reject the
/// match, so the caller falls back to the general lowering rather than
/// miscompiling.
pub(super) fn strip_resume(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    drift: &DriftLog,
) -> Option<TypedComp> {
    let stripped = strip_resume_go(c, aliases, drift)?;
    if !free_comp_vars(&stripped).is_disjoint(aliases) {
        debug_assert!(
            false,
            "strip_resume accepted a clause but left a resume reference: \
             the elaborated shape drifted"
        );
        drift.shape_drift(STRIP_RESUME);
        return None;
    }
    Some(stripped)
}

// The matcher this guard names in a drift report.
const STRIP_RESUME: &str = "strip_resume";

fn strip_resume_go(c: &TypedComp, aliases: &BTreeSet<Sym>, drift: &DriftLog) -> Option<TypedComp> {
    match c.kind() {
        // The tail `resume(v)`: the continuation is the clause's own return.
        TypedCompKind::App { callee, args, .. } if forces_alias(callee, aliases) => {
            let [arg] = args.as_slice() else {
                return None;
            };
            if !free_value_vars(arg).is_disjoint(aliases) {
                return None;
            }
            Some(TypedComp::new(
                CompSig::new(arg.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(arg.clone()),
            ))
        }
        TypedCompKind::Bind(m, x, n) => {
            // `let x = resume` aliases the resumption; track it and keep going.
            if let TypedCompKind::Return(v) = m.kind() {
                if super::as_var(v).is_some_and(|name| aliases.contains(&name)) {
                    let mut extended = aliases.clone();
                    extended.insert(x.name());
                    return strip_resume(n, &extended, drift);
                }
            }
            // Resume may not be consumed off the tail.
            if !free_comp_vars(m).is_disjoint(aliases) {
                return None;
            }
            let rest = strip_resume(n, aliases, drift)?;
            Some(TypedComp::new(
                CompSig::new(
                    rest.sig().result().clone(),
                    super::union_effects(m.sig().effects(), rest.sig().effects()),
                ),
                TypedCompKind::Bind(m.clone(), x.clone(), Box::new(rest)),
            ))
        }
        TypedCompKind::If(v, t, e) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let t2 = strip_resume(t, aliases, drift)?;
            let e2 = strip_resume(e, aliases, drift)?;
            Some(TypedComp::new(
                CompSig::new(
                    t2.sig().result().clone(),
                    super::union_effects(t2.sig().effects(), e2.sig().effects()),
                ),
                TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
            ))
        }
        TypedCompKind::Case(v, arms) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let mut out = Vec::with_capacity(arms.len());
            for (p, b) in arms {
                out.push((p.clone(), strip_resume(b, aliases, drift)?));
            }
            let result = out.first()?.1.sig().result().clone();
            let effects = out.iter().fold(EffRow::Empty, |acc, (_, b)| {
                super::union_effects(&acc, b.sig().effects())
            });
            Some(TypedComp::new(
                CompSig::new(result, effects),
                TypedCompKind::Case(v.clone(), out),
            ))
        }
        _ => None,
    }
}

// `force(k)` where `k` is one of the resumption's aliases.
fn forces_alias(callee: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    matches!(callee.kind(), TypedCompKind::Force(v)
        if super::as_var(v).is_some_and(|name| aliases.contains(&name)))
}

/// The evidence in scope: each op id mapped to the variable holding its active
/// clause. Keyed by id so iteration is ascending, which is the one ordering
/// callers and callees agree on.
pub(super) type Env = BTreeMap<i64, TypedBinder>;

/// The locals whose type threading has changed, and the type each now has.
///
/// Threading an escaping thunk gives it evidence parameters, so its type is not
/// the one its binder was elaborated with. Every later read of that local must
/// carry the new type or the stored witness and the term disagree, which the
/// independent verifier rejects (and rightly: a swapped evidence parameter
/// would otherwise be invisible).
#[derive(Default)]
pub(super) struct Retyped(BTreeMap<Sym, CoreType>);

impl Retyped {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn insert(&mut self, name: Sym, ty: CoreType) -> Option<CoreType> {
        self.0.insert(name, ty)
    }

    fn remove(&mut self, name: Sym) -> Option<CoreType> {
        self.0.remove(&name)
    }

    fn restore(&mut self, name: Sym, previous: Option<CoreType>) {
        match previous {
            Some(ty) => {
                self.0.insert(name, ty);
            }
            None => {
                self.0.remove(&name);
            }
        }
    }

    // A `Var` reading a retyped local, rebuilt at its new type.
    pub(super) fn lookup(&self, v: &TypedValue) -> Option<TypedValue> {
        let name = super::as_var(v)?;
        let ty = self.0.get(&name)?;
        Some(TypedValue::new(
            ty.clone(),
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        ))
    }

    pub(super) fn rebuild(&self, v: &TypedValue) -> TypedValue {
        self.lookup(v).unwrap_or_else(|| v.clone())
    }
}

/// Rewrite one callable's body for the evidence path.
///
/// `do op` forces the current evidence for that op; a call to an effectful
/// function appends its evidence; a handle binds each clause under a fresh
/// name (so an inner handler shadows an op already in scope without a clash).
/// `None` when a shape the engine cannot thread appears, which leaves the
/// whole program to the general lowering.
pub(super) struct Threader<'a> {
    pub(super) plan: &'a EvidencePlan,
    pub(super) ops: &'a OpIds,
    pub(super) env: &'a VerifyEnv,
    pub(super) latent: &'a Latent,
    pub(super) flow: &'a ThunkFlow,
    pub(super) drift: &'a DriftLog,
    /// The term counter, which fixes generated names and tick order.
    pub(super) fresh: &'a mut Fresh,
}

impl Threader<'_> {
    fn thread_in(
        &mut self,
        c: &TypedComp,
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedComp> {
        match c.kind() {
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => self.perform(c, *operation, instantiation, args, ev, retyped),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => self.call(c, *callee, instantiation, args, ev, loc, retyped),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => self.handle(
                c,
                body,
                return_binder.as_ref(),
                return_body.as_deref(),
                ops,
                ev,
                loc,
                retyped,
            ),
            // A mask is meaningless once evidence is passed lexically: the
            // eligibility prologue rejects any program containing one, so this
            // is only reachable if that guard changes.
            TypedCompKind::Mask(..) => None,
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.thread_in(m, ev, loc, retyped)?;
                // Threading may have changed what this binder holds; the binder
                // and every read of it must follow, or the witness and the term
                // disagree.
                let x2 = TypedBinder::new(x.name(), m2.sig().result().clone());
                let shadowed = if x2.ty() == x.ty() {
                    retyped.remove(x.name())
                } else {
                    retyped.insert(x.name(), x2.ty().clone())
                };
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    super::flow::result_sig(m, loc, self.latent, self.flow),
                );
                let n2 = self.thread_in(n, ev, &loc2, retyped)?;
                retyped.restore(x.name(), shadowed);
                Some(TypedComp::new(
                    CompSig::new(
                        n2.sig().result().clone(),
                        super::union_effects(m2.sig().effects(), n2.sig().effects()),
                    ),
                    TypedCompKind::Bind(Box::new(m2), x2, Box::new(n2)),
                ))
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_in(t, ev, loc, retyped)?;
                let e2 = self.thread_in(e, ev, loc, retyped)?;
                Some(TypedComp::new(
                    CompSig::new(
                        t2.sig().result().clone(),
                        super::union_effects(t2.sig().effects(), e2.sig().effects()),
                    ),
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                ))
            }
            TypedCompKind::Case(v, arms) => {
                let mut out = Vec::with_capacity(arms.len());
                for (p, b) in arms {
                    out.push((p.clone(), self.thread_in(b, ev, loc, retyped)?));
                }
                let result = out.first()?.1.sig().result().clone();
                let effects = out.iter().fold(EffRow::Empty, |acc, (_, b)| {
                    super::union_effects(&acc, b.sig().effects())
                });
                Some(TypedComp::new(
                    CompSig::new(result, effects),
                    TypedCompKind::Case(v.clone(), out),
                ))
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => self.force_site(c, callee, instantiation, args, ev, loc, retyped),
            TypedCompKind::Return(v) => {
                let v2 = self.thread_value_in(v, ev, loc, retyped)?;
                Some(TypedComp::new(
                    CompSig::new(v2.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(v2),
                ))
            }
            // Forcing reads its result straight out of the thunk's witness, so a
            // thunk whose type threading widened forces at the wider type. The
            // force site above then finds the evidence-carrying function type
            // rather than the one elaboration wrote.
            TypedCompKind::Force(v) => {
                let v2 = self.thread_value_in(v, ev, loc, retyped)?;
                let CoreType::Thunk(sig) = v2.ty() else {
                    return None;
                };
                Some(TypedComp::new(
                    sig.as_ref().clone(),
                    TypedCompKind::Force(v2),
                ))
            }
            _ => Some(c.clone()),
        }
    }

    // `do op(args)` becomes `force(ev@<id>)(args)`: the active clause, applied
    // at this site's own instantiation. The result rides the clause's row, so
    // the perform's own effect label is gone.
    fn perform(
        &self,
        c: &TypedComp,
        op: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        ev: &Env,
        retyped: &Retyped,
    ) -> Option<TypedComp> {
        let id = self.ops.id(op)?;
        let binder = ev.get(&id)?;
        let CoreType::Thunk(thunk) = binder.ty() else {
            return None;
        };
        let force = TypedComp::new(
            thunk.as_ref().clone(),
            TypedCompKind::Force(binder_value(binder)),
        );
        let CoreType::Function(clause) = thunk.result() else {
            return None;
        };
        // Evidence parameters and local handler clauses are already expressed
        // at the enclosing row's instantiation. Only a genuinely generic
        // fallback clause would still consume the perform's type arguments.
        let instantiation = if clause.quantifiers().is_empty() {
            Vec::new()
        } else {
            instantiation.to_vec()
        };
        let applied = instantiate_fn(clause, &instantiation).ok()?;
        let args = if args.is_empty() {
            vec![TypedValue::new(
                CoreType::Source(Type::Unit),
                TypedValueKind::Unit,
            )]
        } else {
            args.iter().map(|a| retyped.rebuild(a)).collect()
        };
        Some(TypedComp::new(
            CompSig::new(
                applied.body().result().clone(),
                applied.body().effects().clone(),
            ),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation,
                args,
            },
        ))
        .filter(|out| out.sig().result() == c.sig().result())
    }

    // A call to a callable that gained evidence appends it, in ascending op-id
    // order, plus the row instantiation its ambient quantifier demands.
    #[allow(clippy::too_many_arguments)]
    fn call(
        &self,
        c: &TypedComp,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        ev: &Env,
        loc: &Loc,
        retyped: &Retyped,
    ) -> Option<TypedComp> {
        let _ = loc;
        let Some(plan) = self.plan.get(callee) else {
            // No evidence to append, but a retyped local passed as an argument
            // still reads at its new type.
            return Some(TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Call {
                    callee,
                    instantiation: instantiation.to_vec(),
                    args: args.iter().map(|a| retyped.rebuild(a)).collect(),
                },
            ));
        };
        let mut args: Vec<TypedValue> = args.iter().map(|a| retyped.rebuild(a)).collect();
        let mut rows = EffRow::Empty;
        for param in &plan.evidence {
            let binder = ev.get(&param.id)?;
            rows = super::union_effects(&rows, clause_row(binder)?);
            args.push(binder_value(binder));
        }
        let mut instantiation = instantiation.to_vec();
        // The outer ambient row is the last quantifier the prepass appended, so
        // its argument goes last too. A return-only plan has no outer ambient:
        // its nested thunk owns the row that its eventual force site supplies.
        if plan.ambient.is_some() {
            instantiation.push(CoreInstantiation::Row(rows));
        }
        // The call's residual is exactly the callee's body row instantiated at
        // this call: substituting the ambient quantifier with the row we pass
        // closes the callee's private ambient variable instead of leaking it into
        // the caller, and equals what the verifier recomputes for the call node.
        let applied = instantiate_fn(&plan.sig, &instantiation).ok()?;
        if args.len() != applied.params().len() {
            return None;
        }
        let args = args
            .into_iter()
            .zip(applied.params())
            .map(|(value, expected)| retarget_call_argument(value, expected.clone()))
            .collect::<Option<Vec<_>>>()?;
        Some(TypedComp::new(
            applied.body().clone(),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            },
        ))
    }

    // Forcing a thunk that gained evidence parameters must supply them, in the
    // same ascending op-id order the thunk's parameter list uses, plus the row
    // instantiation its ambient quantifier demands. The thunk's signature comes
    // from the interprocedural flow analysis, which is the only thing that
    // knows what a thunk-valued variable performs once forced.
    #[allow(clippy::too_many_arguments)]
    fn force_site(
        &mut self,
        c: &TypedComp,
        callee: &TypedComp,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedComp> {
        let callee2 = self.thread_in(callee, ev, loc, retyped)?;
        let mut args: Vec<TypedValue> = args
            .iter()
            .map(|a| self.thread_value_in(a, ev, loc, retyped))
            .collect::<Option<_>>()?;
        let ordinary_arg_count = args.len();
        let mut evidence_args = Vec::new();
        let mut instantiation = instantiation.to_vec();

        // Only a force of a thunk-valued variable carries a flow signature; a
        // computed callee is threaded structurally and needs nothing appended.
        let forced = match callee.kind() {
            TypedCompKind::Force(v) => super::as_var(v),
            _ => None,
        };
        if let Some(name) = forced {
            if let Some(sig) = loc.get(&name).filter(|s| !s.is_empty()) {
                let mut rows = EffRow::Empty;
                for id in self.ops.ids_of(sig.iter().map(|m| &m.id))? {
                    let binder = ev.get(&id)?;
                    rows = super::union_effects(&rows, clause_row(binder)?);
                    evidence_args.push(binder_value(binder));
                }
                instantiation.push(CoreInstantiation::Row(rows));
            }
        }

        // The callee's own (possibly retyped) thunk decides the result: read it
        // back rather than trusting the pre-threading witness.
        let CoreType::Function(applied) = callee2.sig().result() else {
            return None;
        };
        let applied = instantiate_fn(applied, &instantiation).ok()?;
        for (offset, value) in evidence_args.into_iter().enumerate() {
            let expected = applied.params().get(ordinary_arg_count + offset)?;
            args.push(super::abi::try_word_bridge(value, expected.clone())?);
        }
        Some(TypedComp::new(
            CompSig::new(
                applied.body().result().clone(),
                super::union_effects(callee2.sig().effects(), applied.body().effects()),
            ),
            TypedCompKind::App {
                callee: Box::new(callee2),
                instantiation,
                args,
            },
        ))
        .filter(|out| out.sig().result() == c.sig().result())
    }

    // A handle binds each clause as evidence under a fresh name and threads its
    // body with those in scope. Clauses thread under the OUTER environment: a
    // clause runs where its handler was installed, not under its own binding.
    #[allow(clippy::too_many_arguments)]
    fn handle(
        &mut self,
        c: &TypedComp,
        body: &TypedComp,
        return_binder: Option<&TypedBinder>,
        return_body: Option<&TypedComp>,
        ops: &TypedHandler,
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedComp> {
        let mut binders = Vec::new();
        let mut body_env = ev.clone();
        for arm in ops.arms() {
            let id = self.ops.id(arm.name())?;
            let clause = self.clause(arm, ev, loc, retyped)?;
            let name = Sym::from(names::lowered("ev", self.fresh.bump()));
            let binder = TypedBinder::new(name, clause.ty().clone());
            body_env.insert(id, binder.clone());
            binders.push((binder, clause));
        }
        let threaded = self.thread_in(body, &body_env, loc, retyped)?;
        // The return clause runs outside this handler's dynamic scope, so it
        // threads under the outer environment, not `body_env`.
        let rv = match return_binder {
            Some(b) => b.clone(),
            None => TypedBinder::new(
                Sym::from(names::lowered("hr", self.fresh.bump())),
                threaded.sig().result().clone(),
            ),
        };
        let rb = match return_body {
            Some(b) => self.thread_in(b, ev, loc, retyped)?,
            None => TypedComp::new(
                CompSig::new(rv.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_value(&rv)),
            ),
        };
        let mut acc = TypedComp::new(
            CompSig::new(
                rb.sig().result().clone(),
                super::union_effects(threaded.sig().effects(), rb.sig().effects()),
            ),
            TypedCompKind::Bind(Box::new(threaded), rv, Box::new(rb)),
        );
        for (binder, clause) in binders.into_iter().rev() {
            let bound = TypedComp::new(
                CompSig::new(clause.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(clause),
            );
            acc = TypedComp::new(
                CompSig::new(acc.sig().result().clone(), acc.sig().effects().clone()),
                TypedCompKind::Bind(Box::new(bound), binder, Box::new(acc)),
            );
        }
        (acc.sig().result() == c.sig().result()).then_some(acc)
    }

    // One clause as evidence: the tail `resume(v)` stripped to `return v`, the
    // body threaded under the outer environment, wrapped in a lambda over the
    // op's parameters. A nullary op still takes one unit parameter, since a
    // zero-argument application has no callee to force.
    fn clause(
        &mut self,
        arm: &TypedHandleOp,
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedValue> {
        let stripped = strip_resume(arm.body(), &resume_set(arm.resume().name()), self.drift)?;
        // A handler clause closes over the enclosing callable's parameters, so
        // it must see any witnesses the signature prepass widened. Its own
        // operation parameters shadow outer locals while the clause is threaded.
        let shadowed: Vec<_> = arm
            .params()
            .iter()
            .map(|param| (param.name(), retyped.remove(param.name())))
            .collect();
        let body = self.thread_in(&stripped, ev, loc, retyped);
        for (name, previous) in shadowed {
            retyped.restore(name, previous);
        }
        let body = body?;
        let params: Vec<TypedBinder> = if arm.params().is_empty() {
            vec![TypedBinder::new(
                Sym::from(names::lowered("u", self.fresh.bump())),
                CoreType::Source(Type::Unit),
            )]
        } else {
            arm.params().to_vec()
        };
        Some(lambda_thunk(params, body, Vec::new()))
    }
}

// The residual row a bound clause thunk runs in.
fn clause_row(binder: &TypedBinder) -> Option<&EffRow> {
    let CoreType::Thunk(thunk) = binder.ty() else {
        return None;
    };
    let CoreType::Function(clause) = thunk.result() else {
        return None;
    };
    Some(clause.body().effects())
}

fn binder_value(b: &TypedBinder) -> TypedValue {
    TypedValue::new(
        b.ty().clone(),
        TypedValueKind::Var {
            name: b.name(),
            instantiation: Vec::new(),
        },
    )
}

// A planned callee may expose a narrower effect row for a thunk parameter than
// the source call witness carries. The interprocedural flow plan is the proof:
// it rewrites only parameters whose arriving thunk effects are known, while the
// verifier's representation rule proves that changing the row does not change
// the thunk's runtime shape. Keep this a source-level `Reinterpret`; routing via
// the lowered Word ABI would also admit different parameter/result conventions
// and could hide a genuine calling-convention mismatch.
fn retarget_call_argument(value: TypedValue, expected: CoreType) -> Option<TypedValue> {
    if value.ty() == &expected {
        return Some(value);
    }
    if !matches!(
        (value.ty(), &expected),
        (CoreType::Thunk(_), CoreType::Thunk(_))
    ) {
        return Some(value);
    }
    super::super::verify::representation_preserving(value.ty(), &expected)
        .then(|| TypedValue::new(expected, TypedValueKind::Reinterpret(Box::new(value))))
}

impl Threader<'_> {
    // An escaping effectful thunk gains the same evidence its body's ops need,
    // and each force site appends the matching evidence. A pure thunk still has
    // its body threaded (it may contain a self-contained handle). An effectful
    // thunk this cannot rewrite (a non-lambda thunk, or one buried in data) is
    // untrackable, so the whole attempt declines.
    fn thread_value_in(
        &mut self,
        v: &TypedValue,
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedValue> {
        // A local whose type threading already changed reads at its new type.
        if let Some(rebuilt) = retyped.lookup(v) {
            return Some(rebuilt);
        }
        match &super::peel(v).kind {
            TypedValueKind::Thunk(c) => match c.kind() {
                TypedCompKind::Lam(ps, b) => self.thread_lambda_thunk(ps, b, ev, loc, retyped),
                other_kind => {
                    let _ = other_kind;
                    if !self.latent_ops(c).is_empty() {
                        return None;
                    }
                    let body = self.thread_in(c, ev, loc, retyped)?;
                    Some(TypedValue::new(
                        CoreType::Thunk(Box::new(body.sig().clone())),
                        TypedValueKind::Thunk(Box::new(body)),
                    ))
                }
            },
            TypedValueKind::Ctor { .. } | TypedValueKind::Tuple(_) => {
                // A thunk buried in data is extracted by a `case` the flow does
                // not follow, so its force site cannot be given evidence.
                if self.carries_effectful_thunk(v) {
                    return None;
                }
                Some(v.clone())
            }
            _ => Some(v.clone()),
        }
    }

    // The thunk gains `ev@<id>` parameters for the ops its body is latent in,
    // under its own ambient residual row, so its force sites can supply the
    // matching evidence and row instantiation.
    fn thread_lambda_thunk(
        &mut self,
        params: &[TypedBinder],
        body: &TypedComp,
        ev: &Env,
        loc: &Loc,
        retyped: &mut Retyped,
    ) -> Option<TypedValue> {
        let ids = self
            .ops
            .ids_of(self.latent_ops(body).iter().map(|m| &m.id))?;
        if ids.is_empty() {
            let threaded = self.thread_in(body, ev, loc, retyped)?;
            return Some(lambda_thunk(params.to_vec(), threaded, Vec::new()));
        }
        // Named by the ops it carries, not by a counter: a force site in another
        // function must arrive at this same quantifier without sharing state
        // with this rewrite.
        let ambient = Sym::from(names::evidence_row(&ids));
        let mut env = ev.clone();
        let mut out_params = params.to_vec();
        for id in ids {
            let op = self.op_named(id)?;
            let binder = TypedBinder::new(
                Sym::from(names::ev(id)),
                clause_type(op, body.sig().effects(), self.env, ambient)?,
            );
            env.insert(id, binder.clone());
            out_params.push(binder);
        }
        let threaded = self.thread_in(body, &env, loc, retyped)?;
        Some(lambda_thunk(
            out_params,
            threaded,
            vec![CoreQuantifier::Row(ambient)],
        ))
    }

    fn latent_ops(&self, c: &TypedComp) -> BTreeSet<super::latent::MaskOp> {
        let mut s = BTreeSet::new();
        super::latent::latent(c, self.latent, &mut s);
        s
    }

    // A thunk whose body performs latent ops, in any position.
    fn carries_effectful_thunk(&self, v: &TypedValue) -> bool {
        match &super::peel(v).kind {
            TypedValueKind::Thunk(c) => {
                let body = match c.kind() {
                    TypedCompKind::Lam(_, b) => b.as_ref(),
                    _ => c.as_ref(),
                };
                !self.latent_ops(body).is_empty()
            }
            TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
                fields.iter().any(|f| self.carries_effectful_thunk(f))
            }
            _ => false,
        }
    }

    fn op_named(&self, id: i64) -> Option<Sym> {
        self.ops.op(id)
    }
}

// A thunk of a lambda, with its function type rebuilt from the threaded body.
fn lambda_thunk(
    params: Vec<TypedBinder>,
    body: TypedComp,
    quantifiers: Vec<CoreQuantifier>,
) -> TypedValue {
    let sig = CoreFnSig::new(
        quantifiers,
        params.iter().map(|p| p.ty().clone()).collect(),
        body.sig().clone(),
    );
    let lam = TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(sig)), EffRow::Empty),
        TypedCompKind::Lam(params, Box::new(body)),
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(lam.sig().clone())),
        TypedValueKind::Thunk(Box::new(lam)),
    )
}

/// The eligibility prologue both fusion engines share: a program can fuse only
/// if it has no masks, lets nothing latent escape untrackably, keeps `main`'s
/// row closed, and installs at least one handler. Returns the program's handles
/// for the caller's own per-handler shape check, or `None` when a guard fails.
pub(super) fn fusion_handles(
    fns: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
) -> Option<Vec<TypedComp>> {
    if fns.iter().any(|f| contains_mask(f.body())) {
        return None;
    }
    if super::flow::escapes(fns, latent, flow) {
        return None;
    }
    if latent
        .get(&Sym::new(ENTRY_POINT))
        .is_some_and(|s| !s.is_empty())
    {
        return None;
    }
    let mut handles = Vec::new();
    for f in fns {
        find_handles(f.body(), &mut handles);
    }
    (!handles.is_empty()).then_some(handles)
}

fn contains_mask(c: &TypedComp) -> bool {
    if matches!(c.kind(), TypedCompKind::Mask(..)) {
        return true;
    }
    let mut found = false;
    super::walk::each_subterm(c, &mut |sc| found |= contains_mask(sc));
    found
}

fn find_handles(c: &TypedComp, out: &mut Vec<TypedComp>) {
    if matches!(c.kind(), TypedCompKind::Handle { .. }) {
        out.push(c.clone());
    }
    super::walk::each_subterm(c, &mut |sc| find_handles(sc, out));
}

/// Lower the whole program by evidence passing, or report ineligibility by
/// returning `None` (no state to undo: the caller falls back to the next rung).
/// Eligibility is decided up front by the static guards, then confirmed
/// structurally as the rewrite threads each escaping thunk to its force sites;
/// an untrackable thunk aborts the whole attempt.
pub(super) fn try_lower_ev(
    fns: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
    ops: &OpIds,
    env: &VerifyEnv,
    drift: &DriftLog,
    fresh: &mut Fresh,
) -> Option<Vec<TypedCoreFn>> {
    if !ev_eligible(fns, latent, flow, drift) {
        return None;
    }
    let plan = EvidencePlan::build(fns, latent, flow, ops, env)?;
    let mut threader = Threader {
        plan: &plan,
        ops,
        env,
        latent,
        flow,
        drift,
        fresh,
    };
    let mut out = Vec::with_capacity(fns.len());
    for f in fns {
        // A callable with no latent op keeps its signature; one that gains
        // evidence takes the prepass's rewritten signature and parameters, so
        // a call site and its callee cannot disagree.
        let (params, sig, ev) = plan.get(f.name()).map_or_else(
            || (f.params().to_vec(), f.sig().clone(), Env::new()),
            |fp| {
                // A parameter whose declared witness the prepass widened must be
                // rebound at that type, or the binder and the signature disagree.
                let mut params: Vec<TypedBinder> = f
                    .params()
                    .iter()
                    .zip(&fp.declared)
                    .map(|(p, ty)| TypedBinder::new(p.name(), ty.clone()))
                    .collect();
                params.extend(fp.evidence.iter().map(|e| e.binder.clone()));
                let ev: Env = fp
                    .evidence
                    .iter()
                    .map(|e| (e.id, e.binder.clone()))
                    .collect();
                (params, fp.sig.clone(), ev)
            },
        );
        let loc: Loc = f
            .params()
            .iter()
            .map(TypedBinder::name)
            .zip(flow.param[&f.name()].iter().cloned())
            .collect();
        // A parameter the prepass re-typed is already in scope at its new type,
        // so every read of it in this body must be rebuilt at that type. The
        // threading traversal learns about locals as it binds them; a parameter
        // was bound before it started, so it has to be seeded.
        let mut retyped = Retyped::new();
        for (p, q) in f.params().iter().zip(&params) {
            if p.ty() != q.ty() {
                retyped.insert(p.name(), q.ty().clone());
            }
        }
        let body = threader.thread_in(f.body(), &ev, &loc, &mut retyped)?;
        out.push(TypedCoreFn::new(
            f.name(),
            params,
            body,
            sig,
            f.dict_arity(),
        ));
    }
    // No self-check here. The engine now threads evidence through every shape it
    // accepts, including a thunk-valued parameter's type, so a tree it hands back
    // that does not verify is a bug in this pass and must surface as one. The
    // shapes it cannot describe are refused earlier and by name: `ev_eligible`
    // rejects masks and untrackable escapes, `ParamPlan::Undescribable` rejects
    // an effectful parameter that is not a thunk of a function, and the
    // traversal declines a thunk whose evidence it cannot place.
    Some(out)
}

// Static eligibility: the shared fusion prologue plus every reachable handler
// being tail-resumptive. Escaping effectful thunks are fine here: the rewrite
// confirms it can track each one.
fn ev_eligible(fns: &[TypedCoreFn], latent: &Latent, flow: &ThunkFlow, drift: &DriftLog) -> bool {
    let Some(handles) = fusion_handles(fns, latent, flow) else {
        return false;
    };
    handles.iter().all(|h| {
        let TypedCompKind::Handle { ops, .. } = h.kind() else {
            return false;
        };
        ops.arms()
            .iter()
            .all(|op| strip_resume(op.body(), &resume_set(op.resume().name()), drift).is_some())
    })
}

#[cfg(test)]
mod tests {
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::super::verify::OperationSig;
    use super::super::super::{TypedComp, TypedCompKind};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    // Ids are alphabetical by name, not by intern order, so `ev@<id>` and trap
    // order stay stable however the program interned its symbols.
    #[test]
    fn op_ids_are_alphabetical_not_intern_order() {
        // Intern in reverse order, so intern ids disagree with names.
        let zulu = sym("zulu");
        let alpha = sym("alpha");
        let ops: BTreeSet<Sym> = [zulu, alpha].into_iter().collect();
        let ids = OpIds::assign(&ops).expect("ids assign");
        assert_eq!(ids.id(alpha), Some(0));
        assert_eq!(ids.id(zulu), Some(1));
    }

    // Evidence lines up positionally everywhere, so a set of ops always maps
    // to ascending ids with duplicates collapsed.
    #[test]
    fn evidence_order_is_ascending_and_deduplicated() {
        let ops: BTreeSet<Sym> = [sym("b"), sym("a"), sym("c")].into_iter().collect();
        let ids = OpIds::assign(&ops).expect("ids assign");
        let wanted = [sym("c"), sym("a"), sym("c")];
        assert_eq!(ids.ids_of(wanted.iter()), Some(vec![0, 2]));
    }

    #[test]
    fn a_call_argument_can_retarget_only_its_thunk_effect_row() {
        let source_tail = sym("source_row");
        let planned_tail = sym("planned_row");
        let callable = |effects| {
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![int()],
                    CompSig::new(int(), effects),
                ))),
                EffRow::Empty,
            )))
        };
        let actual = callable(EffRow::canonical(
            [Label::bare(sym("Emit"))],
            EffRow::Var(source_tail),
        ));
        let expected = callable(EffRow::Var(planned_tail));
        let value = TypedValue::new(
            actual.clone(),
            TypedValueKind::Var {
                name: sym("f"),
                instantiation: Vec::new(),
            },
        );
        let erased = value.clone().erase();
        let retargeted = retarget_call_argument(value, expected.clone())
            .expect("effect rows do not change a thunk's representation");
        assert_eq!(retargeted.ty(), &expected);
        assert!(matches!(retargeted.kind(), TypedValueKind::Reinterpret(_)));
        assert_eq!(retargeted.erase(), erased);

        let different_result = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![int()],
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Var(planned_tail)),
            ))),
            EffRow::Empty,
        )));
        let incompatible = TypedValue::new(
            actual.clone(),
            TypedValueKind::Var {
                name: sym("g"),
                instantiation: Vec::new(),
            },
        );
        assert!(
            retarget_call_argument(incompatible, different_result).is_none(),
            "a row bridge cannot conceal a result-convention mismatch"
        );

        let different_param = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Bool)],
                CompSig::new(int(), EffRow::Var(planned_tail)),
            ))),
            EffRow::Empty,
        )));
        let different_quantifiers = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                vec![CoreQuantifier::Row(sym("extra"))],
                vec![int()],
                CompSig::new(int(), EffRow::Var(planned_tail)),
            ))),
            EffRow::Empty,
        )));
        let different_outer_effect = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![int()],
                CompSig::new(int(), EffRow::Var(planned_tail)),
            ))),
            EffRow::singleton(sym("Allocate")),
        )));
        for (name, expected) in [
            ("parameter", different_param),
            ("quantifier", different_quantifiers),
            ("outer effect", different_outer_effect),
        ] {
            let incompatible = TypedValue::new(
                actual.clone(),
                TypedValueKind::Var {
                    name: sym(name),
                    instantiation: Vec::new(),
                },
            );
            assert!(
                retarget_call_argument(incompatible, expected).is_none(),
                "a row bridge cannot conceal a {name} mismatch"
            );
        }
    }

    // The design decision this port turns on: one ambient residual row per
    // callable. The evidence parameter's clause runs in that row, the
    // callable's own residual coalesces into it, and the discharged effect
    // leaves the row entirely.
    #[test]
    fn a_plan_gives_one_ambient_row_and_discharges_the_handled_effect() {
        let ask = sym("ask");
        let effect = sym("Ask");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            ask,
            OperationSig::new(Vec::new(), Vec::new(), int(), Label::bare(effect)),
        );
        let mut op_set = BTreeSet::new();
        op_set.insert(ask);
        let ops = OpIds::assign(&op_set).expect("ids");

        // `fn reader() : Int ! {Ask}` is latent in `ask`.
        let f = TypedCoreFn::new(
            sym("reader"),
            Vec::new(),
            TypedComp::new(
                CompSig::new(int(), EffRow::singleton(effect)),
                TypedCompKind::Do {
                    operation: ask,
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            ),
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(int(), EffRow::singleton(effect)),
            ),
            0,
        );
        let mut ask_set = BTreeSet::new();
        ask_set.insert(super::super::latent::MaskOp { id: ask, depth: 0 });
        let mut latent = Latent::new();
        latent.insert(sym("reader"), ask_set);

        let flow = super::super::flow::analyze(std::slice::from_ref(&f), &latent);
        let plan = EvidencePlan::build(std::slice::from_ref(&f), &latent, &flow, &ops, &env)
            .expect("plan builds");
        let fp = plan.get(sym("reader")).expect("reader gains evidence");
        let ambient = fp.ambient.expect("reader owns an ambient row");

        // Exactly one ambient row quantifier, appended after the original
        // scheme so existing instantiation positions do not move.
        assert_eq!(
            fp.sig.quantifiers(),
            &[CoreQuantifier::Row(ambient)],
            "one ambient row, appended last"
        );
        // The handled effect is discharged; what remains rides the ambient
        // tail rather than being unioned with it.
        assert_eq!(fp.sig.body().effects(), &EffRow::Var(ambient));
        // One evidence parameter, canonically named, carrying the clause.
        assert_eq!(fp.evidence.len(), 1);
        assert_eq!(fp.evidence[0].id, 0);
        assert_eq!(fp.evidence[0].binder.name().as_str(), "ev@0");
        let CoreType::Thunk(thunk) = fp.evidence[0].binder.ty() else {
            panic!("evidence is a thunk: {:?}", fp.evidence[0].binder.ty());
        };
        let CoreType::Function(clause) = thunk.result() else {
            panic!("evidence thunks a clause function: {:?}", thunk.result());
        };
        assert_eq!(clause.body().result(), &int());
        assert_eq!(
            clause.body().effects(),
            &EffRow::Var(ambient),
            "the clause runs in the ambient row"
        );
        assert_eq!(fp.sig.params(), &[fp.evidence[0].binder.ty().clone()]);
    }

    #[test]
    fn a_parametric_evidence_clause_uses_the_callable_effect_instantiation() {
        let emit = sym("emit");
        let effect = sym("Emit");
        let element = sym("a");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            emit,
            OperationSig::new(
                vec![CoreQuantifier::Type(element)],
                vec![CoreType::Source(Type::Var(element))],
                CoreType::Source(Type::Unit),
                Label {
                    name: effect,
                    args: vec![Type::Var(element)],
                },
            ),
        );
        let effects = EffRow::canonical(
            [Label {
                name: effect,
                args: vec![Type::Int],
            }],
            EffRow::Empty,
        );
        let f = TypedCoreFn::new(
            sym("numbers"),
            Vec::new(),
            TypedComp::new(
                CompSig::new(CoreType::Source(Type::Unit), effects.clone()),
                TypedCompKind::Do {
                    operation: emit,
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    args: vec![TypedValue::new(int(), TypedValueKind::Int(1))],
                },
            ),
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(CoreType::Source(Type::Unit), effects),
            ),
            0,
        );
        let ops = OpIds::assign(&BTreeSet::from([emit])).expect("ids");
        let latent = super::super::latent::latent_map(std::slice::from_ref(&f));
        let flow = super::super::flow::analyze(std::slice::from_ref(&f), &latent);
        let plan = EvidencePlan::build(std::slice::from_ref(&f), &latent, &flow, &ops, &env)
            .expect("plan builds");
        let evidence = &plan.get(f.name()).expect("numbers gains evidence").evidence[0];
        let CoreType::Thunk(thunk) = evidence.binder.ty() else {
            panic!("evidence is a thunk: {:?}", evidence.binder.ty());
        };
        let CoreType::Function(clause) = thunk.result() else {
            panic!("evidence thunks a clause: {:?}", thunk.result());
        };
        assert!(clause.quantifiers().is_empty());
        assert_eq!(clause.params(), &[int()]);
        assert_eq!(clause.body().result(), &CoreType::Source(Type::Unit));
    }

    #[test]
    fn evidence_declines_an_operation_scheme_not_fully_named_by_the_effect_row() {
        let emit = sym("emit");
        let effect = sym("Emit");
        let element = sym("a");
        let local = sym("b");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            emit,
            OperationSig::new(
                vec![CoreQuantifier::Type(element), CoreQuantifier::Type(local)],
                vec![
                    CoreType::Source(Type::Var(element)),
                    CoreType::Source(Type::Var(local)),
                ],
                CoreType::Source(Type::Unit),
                Label {
                    name: effect,
                    args: vec![Type::Var(element)],
                },
            ),
        );
        let effects = EffRow::canonical(
            [Label {
                name: effect,
                args: vec![Type::Int],
            }],
            EffRow::Empty,
        );
        assert!(
            clause_type(emit, &effects, &env, sym("ambient")).is_none(),
            "partial operation instantiation must fall through to a later rung"
        );
    }

    fn thunk_of(body: TypedComp) -> TypedValue {
        TypedValue::new(
            CoreType::Thunk(Box::new(body.sig().clone())),
            TypedValueKind::Thunk(Box::new(body)),
        )
    }

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    // The resumption's type in a tail-resumptive clause: `thunk ((Int) -> Int)`.
    fn resume_ty() -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![int()],
                CompSig::new(int(), EffRow::Empty),
            ))),
            EffRow::Empty,
        )))
    }

    // `resume(v)` at the clause's tail.
    fn resume_call(arg: TypedValue) -> TypedComp {
        let k = var("k", resume_ty());
        let CoreType::Thunk(sig) = resume_ty() else {
            unreachable!()
        };
        let force = TypedComp::new(*sig, TypedCompKind::Force(k));
        TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![arg],
            },
        )
    }

    // A tail-resumptive clause is exactly what evidence passing needs: the
    // continuation vanishes and the clause becomes a plain function body.
    #[test]
    fn a_tail_resume_strips_to_a_plain_return() {
        let drift = DriftLog::new(true);
        let body = resume_call(TypedValue::new(int(), TypedValueKind::Int(7)));
        let stripped = strip_resume(&body, &resume_set(sym("k")), &drift).expect("tail-resumptive");
        let TypedCompKind::Return(v) = stripped.kind() else {
            panic!("resume(v) becomes return v: {stripped:?}");
        };
        assert!(matches!(v.kind(), TypedValueKind::Int(7)));
    }

    // A resumption that escapes into a value is not tail-resumptive: the
    // continuation genuinely survives, so evidence passing must decline rather
    // than silently drop it.
    #[test]
    fn a_captured_resume_refuses_to_strip() {
        let drift = DriftLog::new(true);
        // `return thunk { resume(1) }`: the continuation escapes into a thunk.
        let inner = resume_call(TypedValue::new(int(), TypedValueKind::Int(1)));
        let escaped = thunk_of(inner);
        let body = TypedComp::new(
            CompSig::new(escaped.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(escaped),
        );
        assert!(
            strip_resume(&body, &resume_set(sym("k")), &drift).is_none(),
            "a captured resume is not tail-resumptive"
        );
    }

    // A resume consumed off the tail (its value bound and used) is likewise
    // not tail-resumptive.
    #[test]
    fn a_non_tail_resume_refuses_to_strip() {
        let drift = DriftLog::new(true);
        let call = resume_call(TypedValue::new(int(), TypedValueKind::Int(1)));
        let body = TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(call),
                TypedBinder::new(sym("r"), int()),
                Box::new(TypedComp::new(
                    CompSig::new(int(), EffRow::Empty),
                    TypedCompKind::Return(var("r", int())),
                )),
            ),
        );
        assert!(
            strip_resume(&body, &resume_set(sym("k")), &drift).is_none(),
            "a resume off the tail is not tail-resumptive"
        );
    }

    // An alias of the resumption is tracked, so a clause that rebinds it still
    // strips (and, critically, still leaves no live reference behind).
    #[test]
    fn an_aliased_resume_is_tracked() {
        let drift = DriftLog::new(true);
        let tail = {
            let j = var("j", resume_ty());
            let CoreType::Thunk(sig) = resume_ty() else {
                unreachable!()
            };
            let force = TypedComp::new(*sig, TypedCompKind::Force(j));
            TypedComp::new(
                CompSig::new(int(), EffRow::Empty),
                TypedCompKind::App {
                    callee: Box::new(force),
                    instantiation: Vec::new(),
                    args: vec![TypedValue::new(int(), TypedValueKind::Int(3))],
                },
            )
        };
        // `let j = k in j(3)`
        let body = TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(resume_ty(), EffRow::Empty),
                    TypedCompKind::Return(var("k", resume_ty())),
                )),
                TypedBinder::new(sym("j"), resume_ty()),
                Box::new(tail),
            ),
        );
        let stripped = strip_resume(&body, &resume_set(sym("k")), &drift)
            .expect("an alias is still tail-resumptive");
        assert!(
            free_comp_vars(&stripped).is_disjoint(&resume_set(sym("k"))),
            "the guard's invariant: no resume reference survives a strip"
        );
    }

    // The witness-only ambient namespace must not collide with a term name,
    // and each callable gets its own row.
    #[test]
    fn ambient_rows_are_witness_only_and_distinct() {
        let mut rows = RowNames::new();
        let a = rows.next();
        let b = rows.next();
        assert_ne!(a, b);
        for r in [a, b] {
            assert!(
                r.as_str().starts_with(FRESH_EVIDENCE_ROW),
                "ambient rows live in their own namespace: {r}"
            );
        }
    }

    // A handler in the producer is gone by the time an escaping thunk is
    // forced. Keep effects outside `flow.ret` in the returned witness instead
    // of treating producer-local handlers as dynamically enclosing the force.
    #[test]
    fn returned_thunk_witness_keeps_effects_not_discharged_by_its_evidence() {
        let emit = sym("emit");
        let emit_effect = sym("Emit");
        let producer_local = sym("ProducerLocal");
        let unit = CoreType::Source(Type::Unit);
        let mut env = VerifyEnv::new();
        env.insert_operation(
            emit,
            OperationSig::new(
                Vec::new(),
                vec![int()],
                unit.clone(),
                Label::bare(emit_effect),
            ),
        );
        let declared = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![unit.clone()],
                CompSig::new(
                    unit,
                    EffRow::canonical(
                        [Label::bare(emit_effect), Label::bare(producer_local)],
                        EffRow::Empty,
                    ),
                ),
            ))),
            EffRow::Empty,
        )));
        let ops = OpIds::assign(&BTreeSet::from([emit])).expect("ids");
        let ids = [ops.id(emit).expect("emit id")];
        let widened = returned_thunk_evidence_type(&declared, &ids, &ops, &env).expect("witness");
        let CoreType::Thunk(outer) = widened else {
            panic!("returned witness stays a thunk");
        };
        let CoreType::Function(inner) = outer.result() else {
            panic!("returned witness stays callable");
        };
        let labels: BTreeSet<Sym> = inner
            .body()
            .effects()
            .labels()
            .into_iter()
            .map(|label| label.name)
            .collect();
        assert_eq!(labels, BTreeSet::from([producer_local]));
        assert_eq!(
            inner.body().effects().tail(),
            &EffRow::Var(Sym::from(names::evidence_row(&ids)))
        );

        let locally_handled = BTreeSet::from([producer_local]);
        let narrowed = thunk_evidence_type(&declared, &ids, &locally_handled, &ops, &env)
            .expect("parameter witness");
        let CoreType::Thunk(outer) = narrowed else {
            panic!("parameter witness stays a thunk");
        };
        let CoreType::Function(inner) = outer.result() else {
            panic!("parameter witness stays callable");
        };
        assert!(
            inner.body().effects().labels().is_empty(),
            "the nonempty handled set has a real, intentionally different meaning"
        );
    }

    // `flow.ret` is the declaration-level witness for a returned thunk. The
    // term rewrite widens the lambda thunk with evidence parameters, so the
    // producer signature and every direct call must publish that same widened
    // result before a later force appends the evidence and row instantiation.
    #[test]
    fn returned_effectful_thunk_retypes_its_declaration_and_direct_calls() {
        let emit = sym("emit");
        let effect = sym("Emit");
        let producer = sym("producer");
        let unit = CoreType::Source(Type::Unit);
        let mut env = VerifyEnv::new();
        env.insert_operation(
            emit,
            OperationSig::new(Vec::new(), vec![int()], unit.clone(), Label::bare(effect)),
        );
        let perform = TypedComp::new(
            CompSig::new(unit.clone(), EffRow::singleton(effect)),
            TypedCompKind::Do {
                operation: emit,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(int(), TypedValueKind::Int(1))],
            },
        );
        let source_thunk =
            lambda_thunk(vec![TypedBinder::new(sym("u"), unit)], perform, Vec::new());
        let source_result = source_thunk.ty().clone();
        let body = TypedComp::new(
            CompSig::new(source_result.clone(), EffRow::Empty),
            TypedCompKind::Return(source_thunk),
        );
        let function = TypedCoreFn::new(
            producer,
            Vec::new(),
            body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(source_result.clone(), EffRow::Empty),
            ),
            0,
        );
        let functions = [function];
        let latent = super::super::latent::latent_map(&functions);
        assert!(
            latent[&producer].is_empty(),
            "the effect is suspended in the returned thunk, not latent in the call"
        );
        let flow = super::super::flow::analyze(&functions, &latent);
        assert_eq!(
            flow.ret[&producer]
                .iter()
                .map(|masked| masked.id)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([emit])
        );
        let ops = OpIds::assign(&BTreeSet::from([emit])).expect("ids");
        let plan = EvidencePlan::build(&functions, &latent, &flow, &ops, &env)
            .expect("return witness plan");
        let planned = plan.get(producer).expect("producer result is planned");
        assert!(planned.ambient.is_none());
        assert!(planned.evidence.is_empty());
        assert_ne!(planned.sig.body().result(), &source_result);

        let call = TypedComp::new(
            functions[0].sig().body().clone(),
            TypedCompKind::Call {
                callee: producer,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let mut fresh = Fresh::new();
        let threader = Threader {
            plan: &plan,
            ops: &ops,
            env: &env,
            latent: &latent,
            flow: &flow,
            drift: &DriftLog::new(true),
            fresh: &mut fresh,
        };
        let rewritten_call = threader
            .call(
                &call,
                producer,
                &[],
                &[],
                &Env::new(),
                &Loc::new(),
                &Retyped::new(),
            )
            .expect("direct call follows the planned result witness");
        assert_eq!(rewritten_call.sig(), planned.sig.body());
    }
}
