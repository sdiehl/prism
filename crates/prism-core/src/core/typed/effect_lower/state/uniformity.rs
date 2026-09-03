//! Producer coincidence, fold uniformity, and escape analysis.

use super::super::{as_var, evidence::fusion_handles, latent, peel, walk};
use super::{
    collect_ops, each_subcomp, flow, free_comp_vars, is_fold, is_id_return, is_id_transformer,
    is_state_transformer, pins, plan_producer, BTreeMap, BTreeSet, CoreType, EarlyExitMode, EffRow,
    FoldAKind, FoldPlan, Latent, Loc, Sig, StateAnalysis, StateAnswerMode, Sym, ThunkFlow,
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue,
    TypedValueKind,
};

/// The pre-threading type of the thunk a handle body forces.
pub(super) fn forced_source_type(c: &TypedComp) -> Option<CoreType> {
    match c.kind() {
        TypedCompKind::App { callee, .. } => match callee.kind() {
            TypedCompKind::Force(v) => Some(peel(v).ty().clone()),
            _ => None,
        },
        TypedCompKind::Bind(m, _, n) => forced_source_type(m).or_else(|| forced_source_type(n)),
        _ => None,
    }
}

/// The open tail at the end of a row, if any.
pub(super) fn row_tail(row: &EffRow) -> Option<Sym> {
    match row {
        EffRow::Extend(_, rest) => row_tail(rest),
        EffRow::Var(name) => Some(*name),
        _ => None,
    }
}

/// One lexical type per free name in `wanted`, harvested from its `Var`
/// occurrences everywhere in `c`, tracking bound names so a `wanted` name
/// rebound under an inner binder is NOT recorded from its shadowed occurrence.
/// Every value form is descended (wrapper, aggregate field, thunk body) and
/// every binder that a name can be rebound at extends the bound set for the
/// scope it governs. `None` when a genuinely free occurrence carries two
/// different types, which one bridge cannot serve.
pub(super) fn lexical_types(
    c: &TypedComp,
    wanted: &BTreeSet<Sym>,
) -> Option<BTreeMap<Sym, TypedValue>> {
    struct Collect<'a> {
        wanted: &'a BTreeSet<Sym>,
        out: BTreeMap<Sym, TypedValue>,
        ok: bool,
    }
    impl Collect<'_> {
        fn value(&mut self, v: &TypedValue, bound: &BTreeSet<Sym>) {
            // The bridge reuses the ACTUAL occurrence, instantiations and all,
            // so a name-keyed map is only sound when every free occurrence is
            // byte-identical; a same-typed occurrence at a different
            // instantiation declines the whole capture.
            if let TypedValueKind::Var { name, .. } = &v.kind {
                if self.wanted.contains(name) && !bound.contains(name) {
                    match self.out.get(name) {
                        Some(existing) if existing != v => self.ok = false,
                        _ => {
                            self.out.insert(*name, v.clone());
                        }
                    }
                    return;
                }
            }
            // Exhaustive by construction: a new value form must be added here or
            // this fails to compile.
            match &v.kind {
                TypedValueKind::Reinterpret(inner)
                | TypedValueKind::NewtypeRepr { value: inner, .. }
                | TypedValueKind::LoweredRepr { value: inner, .. } => self.value(inner, bound),
                TypedValueKind::Thunk(body) => self.comp(body, bound),
                TypedValueKind::Ctor { fields, .. }
                | TypedValueKind::Tuple(fields)
                | TypedValueKind::UnboxedTuple(fields) => {
                    for f in fields {
                        self.value(f, bound);
                    }
                }
                TypedValueKind::UnboxedRecord(fields) => {
                    for (_, f) in fields {
                        self.value(f, bound);
                    }
                }
                TypedValueKind::Var { .. }
                | TypedValueKind::Int(_)
                | TypedValueKind::I64(_)
                | TypedValueKind::U64(_)
                | TypedValueKind::Float(_)
                | TypedValueKind::Bool(_)
                | TypedValueKind::Unit
                | TypedValueKind::Str(_) => {}
            }
        }
        fn comp(&mut self, c: &TypedComp, bound: &BTreeSet<Sym>) {
            match c.kind() {
                TypedCompKind::Bind(m, x, n) => {
                    self.comp(m, bound);
                    let mut b2 = bound.clone();
                    b2.insert(x.name());
                    self.comp(n, &b2);
                }
                TypedCompKind::Lam(ps, body) => {
                    let mut b2 = bound.clone();
                    b2.extend(ps.iter().map(TypedBinder::name));
                    self.comp(body, &b2);
                }
                TypedCompKind::Case(v, arms) => {
                    self.value(v, bound);
                    for (pat, arm) in arms {
                        let mut b2 = bound.clone();
                        pattern_binders(pat, &mut b2);
                        self.comp(arm, &b2);
                    }
                }
                TypedCompKind::Handle {
                    body,
                    ops,
                    return_binder,
                    return_body,
                } => {
                    self.comp(body, bound);
                    for arm in ops.arms() {
                        let mut b2 = bound.clone();
                        b2.extend(arm.params().iter().map(TypedBinder::name));
                        b2.insert(arm.resume().name());
                        self.comp(arm.body(), &b2);
                    }
                    if let Some(rb) = return_body {
                        let mut b2 = bound.clone();
                        if let Some(binder) = return_binder {
                            b2.insert(binder.name());
                        }
                        self.comp(rb, &b2);
                    }
                }
                TypedCompKind::WithReuse { token, freed, body } => {
                    self.value(freed, bound);
                    let mut b2 = bound.clone();
                    b2.insert(token.name());
                    self.comp(body, &b2);
                }
                _ => {
                    walk::each_value(c, &mut |v| self.value(v, bound));
                    walk::each_subcomp(c, &mut |sc| self.comp(sc, bound));
                }
            }
        }
    }
    let mut collect = Collect {
        wanted,
        out: BTreeMap::new(),
        ok: true,
    };
    collect.comp(c, &BTreeSet::new());
    collect.ok.then_some(collect.out)
}

/// Every binder a pattern introduces.
fn pattern_binders(pat: &TypedPattern, out: &mut BTreeSet<Sym>) {
    match pat {
        TypedPattern::Var(b) => {
            out.insert(b.name());
        }
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            for f in fields.iter().flatten() {
                out.insert(f.name());
            }
        }
        TypedPattern::Wild => {}
    }
}

/// Whether a computation is latent in any fused operation, so a thunk built
/// from it is a producer the moment it is forced.
pub(super) fn body_folds(c: &TypedComp, ops: &BTreeSet<Sym>, latent: &Latent) -> bool {
    let mut s = Sig::new();
    latent::latent(c, latent, &mut s);
    s.iter().any(|m| ops.contains(&m.id))
}

/// Whether running a computation performs any fused operation, so the
/// accumulator must be threaded through it.
///
/// That is a `do op`, a call to an operation-latent function, or a force of a
/// thunk whose flow signature carries a fused operation, in any executed
/// position.
///
/// [`latent::latent`] cannot see a force of a thunk-valued variable, so
/// this augments it with the flow `loc`.
#[must_use]
pub fn produces(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => ops.contains(operation),
        TypedCompKind::Call { callee, .. } => latent
            .get(callee)
            .is_some_and(|s| s.iter().any(|m| ops.contains(&m.id))),
        TypedCompKind::App { callee, .. } => {
            matches!(callee.kind(), TypedCompKind::Force(v)
                if flow::value_sig(v, loc, latent).iter().any(|m| ops.contains(&m.id)))
        }
        TypedCompKind::Bind(m, x, n) => {
            produces(m, loc, ops, latent, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, latent, flow));
                produces(n, &loc2, ops, latent, flow)
            }
        }
        TypedCompKind::If(_, t, e) => {
            produces(t, loc, ops, latent, flow) || produces(e, loc, ops, latent, flow)
        }
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .any(|(_, body)| produces(body, loc, ops, latent, flow)),
        TypedCompKind::Mask(_, body) => produces(body, loc, ops, latent, flow),
        _ => false,
    }
}

/// Whether a computation's result value coincides with the threaded accumulator,
/// so the state-mode loop (which yields the accumulator) yields the right answer.
///
/// True when the tail is a read (a read resumes with the accumulator, so it
/// returns the state) or a tail-call to a producer (compiled to return the
/// accumulator, checked transitively). A `return` of any value, a first-class
/// application, or a write tail is not coincident: the producer value differs
/// from the state.
///
/// This is the check the whole engine's correctness in
/// [`StateAnswerMode::Producer`] rests on, and it is why the state rung declines
/// below its own gate: it belongs with the threading rather than the gate,
/// because it reads what each clause resumes with.
fn value_coincident(
    c: &TypedComp,
    plan: &FoldPlan,
    fns: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
    visited: &mut BTreeSet<Sym>,
) -> bool {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => plan.kinds.get(operation) == Some(&FoldAKind::Acc),
        TypedCompKind::Bind(_, _, n) => value_coincident(n, plan, fns, latent, flow, visited),
        TypedCompKind::If(_, t, e) => {
            value_coincident(t, plan, fns, latent, flow, visited)
                && value_coincident(e, plan, fns, latent, flow, visited)
        }
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .all(|(_, body)| value_coincident(body, plan, fns, latent, flow, visited)),
        TypedCompKind::Mask(_, body) => value_coincident(body, plan, fns, latent, flow, visited),
        TypedCompKind::Call { callee, .. } if produces(c, &Loc::new(), &plan.ops, latent, flow) => {
            // A recursive cycle is coinductively fine: its non-recursive tails are
            // checked on first visit.
            if !visited.insert(*callee) {
                return true;
            }
            fns.iter()
                .find(|f| f.name() == *callee)
                .is_some_and(|f| value_coincident(f.body(), plan, fns, latent, flow, visited))
        }
        _ => false,
    }
}

/// Whether the threaded loop's answer is the one the program means, which is the
/// precondition the threading itself runs under.
///
/// In [`StateAnswerMode::Producer`] the loop yields the accumulator while the
/// answer is the producer's value, so the two must coincide: every fold handle's
/// body must be value-coincident. Otherwise this engine would return the state
/// where the program means the value, and the program falls back to a slower rung
/// that is correct.
///
/// This sits below the gate deliberately: it is the first thing
/// `try_lower_state` asks after fold-uniformity, and it asks nothing the gate
/// answered.
#[must_use]
pub fn threads(plan: &FoldPlan, fns: &[TypedCoreFn], analysis: &StateAnalysis<'_>) -> bool {
    let StateAnalysis {
        ids, latent, flow, ..
    } = analysis;
    if plan.ops.iter().any(|op| ids.id(*op).is_none()) {
        return false;
    }
    if plan.answer != StateAnswerMode::Producer {
        return true;
    }
    let Some(handles) = fusion_handles(fns, latent, flow) else {
        return false;
    };
    handles.iter().all(|h| {
        let TypedCompKind::Handle {
            body, ops: clauses, ..
        } = h.kind()
        else {
            return true;
        };
        let erased = clauses.clone().erase();
        let all_folds = !erased.arms().is_empty()
            && erased
                .iter_with_use()
                .all(|(c, ru)| is_fold(c, ru).is_some());
        !all_folds || value_coincident(body, plan, fns, latent, flow, &mut BTreeSet::new())
    })
}

/// The fused operations a function is latent in, which are the ones whose
/// accumulator it threads. Empty for a function that is not a producer.
pub(super) fn producer_ops(f: &TypedCoreFn, ops: &BTreeSet<Sym>, latent: &Latent) -> BTreeSet<Sym> {
    latent
        .get(&f.name())
        .map(|s| {
            s.iter()
                .map(|m| m.id)
                .filter(|id| ops.contains(id))
                .collect()
        })
        .unwrap_or_default()
}

/// Decide whether the whole program streams a single operation set through
/// handlers this engine can fuse, or `None` to fall back.
///
/// `None` for a mask, an escaping effectful thunk the flow cannot track, an open
/// latent escape, no handles, an unhandled operation, or any handler that is not
/// a fold consumer with a state-transformer return clause, a re-emitting
/// forwarder, a control consumer, or a take. One handler may carry several fold
/// clauses over distinct operations, each threading the one shared accumulator.
pub fn fold_uniform(fns: &[TypedCoreFn], analysis: &StateAnalysis<'_>) -> Option<FoldPlan> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
    } = analysis;
    let mut ops = BTreeSet::new();
    for f in fns {
        collect_ops(f.body(), &mut ops);
    }
    if ops.is_empty() {
        return None;
    }
    let handles = fusion_handles(fns, latent, flow)?;

    let mut kinds = BTreeMap::new();
    let mut answer = StateAnswerMode::Accumulator;
    let mut consumed: BTreeSet<Sym> = BTreeSet::new();
    let mut folds = 0u32;
    let mut takes = 0u32;

    for h in &handles {
        let TypedCompKind::Handle {
            ops: clauses,
            return_binder,
            return_body,
            ..
        } = h.kind()
        else {
            return None;
        };
        // One erased clone per handle, so every clause-shape question below is
        // answered from one neutral representation.
        let erased = clauses.clone().erase();
        let uses: Vec<_> = erased
            .iter_with_use()
            .map(|(c, ru)| (c.clone(), ru))
            .collect();

        if !uses.is_empty() && uses.iter().all(|(c, ru)| is_fold(c, *ru).is_some()) {
            // A fold's return clause is a state transformer. The identity
            // transformer is the writer special case; a get-style `\s -> r` is the
            // general one, applied to the final accumulator.
            let rb = return_body.as_deref().map(|b| b.clone().erase());
            if !rb.as_ref().is_some_and(is_state_transformer) {
                return None;
            }
            if !rb.as_ref().is_some_and(is_id_transformer) {
                answer = StateAnswerMode::Producer;
            }
            for (c, ru) in &uses {
                kinds.insert(c.name, is_fold(c, *ru)?);
                consumed.insert(c.name);
                folds += 1;
            }
            continue;
        }

        let ([arm], [(erased_arm, ru)]) = (clauses.arms(), uses.as_slice()) else {
            return None;
        };
        if is_take(arm, latent) {
            takes += 1;
        } else if ru.tail && folds_op(arm.body(), arm.name(), latent) {
            // A re-emitting forwarder threads the accumulator straight into the
            // outer evidence, so its return clause must pass the source's final
            // value through unchanged.
            let rv = return_binder.as_ref().map(TypedBinder::name);
            let rb = return_body.as_deref().map(|b| b.clone().erase());
            if !is_id_return(rv, rb.as_ref()) {
                return None;
            }
        } else if ru.tail {
            // A control consumer: tail-resumptive but not re-emitting, so its
            // clause is a side effect over a unit state the producer threads
            // unchanged. Any return clause is fine.
        } else {
            return None;
        }
        consumed.insert(erased_arm.name);
    }

    // Every streamed operation must be handled here, and something must consume.
    // A pure forwarding or control chain belongs to the evidence engine, which
    // runs first, so reaching here means a fold or a take.
    if consumed != ops || folds + takes == 0 {
        return None;
    }

    // An effectful thunk handed to a callee this engine will not thread would gain
    // parameters its un-threaded force site cannot supply. The evidence engine
    // threads such callees through the flow analysis; this one does not.
    let forcers = generic_forcers(fns);
    if fns.iter().any(|f| {
        let loc: Loc = flow::param_loc(f, flow);
        state_escapes(f.body(), &loc, &ops, &forcers, latent, flow)
    }) {
        return None;
    }

    let plan = FoldPlan {
        pins: pins(&kinds, env)?,
        ops,
        kinds,
        answer,
        early: if takes > 0 {
            EarlyExitMode::ShortCircuit
        } else {
            EarlyExitMode::Continue
        },
    };

    // Every producer must have an expressible threaded signature, which is where
    // typing the one accumulator it threads is decided: chains that share no
    // producer are free to disagree on the accumulator, and do.
    for f in fns {
        let ops = producer_ops(f, &plan.ops, latent);
        if !ops.is_empty() {
            plan_producer(f, &ops, &plan, ids, fns, latent, env)?;
        }
    }

    Some(plan)
}

/// A `stake`-style early-terminating handler: a parameter-passing clause that
/// re-emits and resumes on one branch but drops the continuation on the other, so
/// the threaded state gains a `Step` wrapper the producer can stop on.
pub(super) fn is_take(arm: &TypedHandleOp, latent: &Latent) -> bool {
    let TypedCompKind::Return(v) = arm.body().kind() else {
        return false;
    };
    let TypedValueKind::Thunk(t) = &peel(v).kind else {
        return false;
    };
    let TypedCompKind::Lam(ps, inner) = t.kind() else {
        return false;
    };
    if ps.len() != 1 {
        return false;
    }
    let Some((b1, b2)) = tail_if(inner) else {
        return false;
    };
    let aliases = BTreeSet::from([arm.resume().name()]);
    folds_op(inner, arm.name(), latent)
        && branch_resumes(b1, &aliases) != branch_resumes(b2, &aliases)
}

/// The branches of a take clause's tail `if`, skipping its leading counter-test
/// binds. `None` when the clause is not that shape.
fn tail_if(c: &TypedComp) -> Option<(&TypedComp, &TypedComp)> {
    match c.kind() {
        TypedCompKind::Bind(_, _, n) => tail_if(n),
        TypedCompKind::If(_, t, e) => Some((t, e)),
        _ => None,
    }
}

/// Whether a branch uses a resume alias, so it resumes rather than dropping it.
pub(super) fn branch_resumes(c: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    !free_comp_vars(c).is_disjoint(aliases)
}

/// Whether a computation is latent in one operation, so it is a producer body.
pub(super) fn folds_op(c: &TypedComp, op: Sym, latent: &Latent) -> bool {
    let mut s = Sig::new();
    latent::latent(c, latent, &mut s);
    s.iter().any(|m| m.id == op)
}

/// Functions that force a thunk-valued parameter outside any handle: generic loop
/// combinators that drive their thunk at a fixed arity. A fold consumer forces its
/// thunk inside a handle body, where the threading reaches it, so it is not one of
/// these. Handing one an effectful thunk is an un-threadable escape.
fn generic_forcers(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| {
            let ps: BTreeSet<Sym> = f.params().iter().map(TypedBinder::name).collect();
            forces_param_bare(f.body(), &ps, false)
        })
        .map(TypedCoreFn::name)
        .collect()
}

/// Whether `c` forces one of `params` (or an A-normal-form alias of one) while not
/// inside a handle body.
fn forces_param_bare(c: &TypedComp, params: &BTreeSet<Sym>, in_handle: bool) -> bool {
    match c.kind() {
        TypedCompKind::App { callee, .. } => {
            (!in_handle
                && matches!(callee.kind(), TypedCompKind::Force(v)
                    if as_var(v).is_some_and(|n| params.contains(&n))))
                || forces_param_bare(callee, params, in_handle)
        }
        TypedCompKind::Bind(m, x, n) => {
            if forces_param_bare(m, params, in_handle) {
                return true;
            }
            // Track `return p to x` so a forced alias resolves back to the param.
            if let TypedCompKind::Return(v) = m.kind() {
                if as_var(v).is_some_and(|n| params.contains(&n)) {
                    let mut ps = params.clone();
                    ps.insert(x.name());
                    return forces_param_bare(n, &ps, in_handle);
                }
            }
            forces_param_bare(n, params, in_handle)
        }
        // A handle drives any thunk forced in its body or clauses through the
        // consumer threading, so those forces are not bare.
        TypedCompKind::Handle {
            body,
            ops,
            return_body,
            ..
        } => {
            forces_param_bare(body, params, true)
                || ops
                    .arms()
                    .iter()
                    .any(|o| forces_param_bare(o.body(), params, true))
                || return_body
                    .as_deref()
                    .is_some_and(|rb| forces_param_bare(rb, params, true))
        }
        _ => {
            let mut found = false;
            each_subcomp(c, &mut |sc| {
                found |= forces_param_bare(sc, params, in_handle);
            });
            found
        }
    }
}

/// Whether the body hands an effectful thunk to a callee this engine will not
/// thread the force site of.
fn state_escapes(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    forcers: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    match c.kind() {
        TypedCompKind::Call { callee, args, .. } => {
            forcers.contains(callee)
                && args.iter().any(|a| {
                    flow::value_sig(a, loc, latent)
                        .iter()
                        .any(|m| ops.contains(&m.id))
                })
        }
        TypedCompKind::Bind(m, x, n) => {
            state_escapes(m, loc, ops, forcers, latent, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, latent, flow));
                state_escapes(n, &loc2, ops, forcers, latent, flow)
            }
        }
        _ => {
            let mut found = false;
            each_subcomp(c, &mut |sc| {
                found |= state_escapes(sc, loc, ops, forcers, latent, flow);
            });
            found
        }
    }
}
