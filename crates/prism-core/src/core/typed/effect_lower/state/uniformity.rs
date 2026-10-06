//! Producer coincidence, fold uniformity, and escape analysis.

use prism_syntax::names::ENTRY_POINT;

use super::super::{latent, peel, walk};
use super::judgment::{judge_arms, judge_handle, ClauseClass, HandleClass};
use super::{
    collect_ops, each_subcomp, flow, free_comp_vars, name_ambient, pins, plan_producer, BTreeMap,
    BTreeSet, CoreType, EarlyExitMode, EffRow, FoldAKind, FoldPlan, Latent, Loc, Sig,
    StateAnalysis, StateAnswerMode, Sym, ThunkFlow, Type, TypedBinder, TypedComp, TypedCompKind,
    TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
};

/// The eligibility prologue: a program can fuse only if it has no masks, lets
/// nothing latent escape untrackably, keeps `main`'s row closed, and installs
/// at least one handler.
///
/// Returns the program's handles for the caller's own per-handler shape check.
///
/// # Errors
///
/// The guard that failed, in words a plan artifact can carry.
pub(super) fn fusion_handles<'a>(
    fns: &'a [TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
    widen: bool,
) -> Result<Vec<&'a TypedComp>, String> {
    if fns.iter().any(|f| walk::contains_mask(f.body())) {
        return Err("the program masks an effect".into());
    }
    // The flow tracks where a thunk is forced so the fused state can be handed
    // to it there. A thunk stored in data outruns that tracking, and the widened
    // convention answers by type instead: a thunk whose row carries a fused
    // operation takes that operation's state wherever it sits, so a force site
    // reads what to pass off the value's own type.
    if let Some((f, why)) = flow::escape_reason(fns, latent, flow, widen) {
        return Err(format!(
            "an effectful thunk escapes the flow: `{}` {why}",
            f.as_str()
        ));
    }
    if let Some(escaped) = latent.get(&Sym::new(ENTRY_POINT)).filter(|s| !s.is_empty()) {
        let names: Vec<String> = escaped.iter().map(|m| format!("`{}`", m.id)).collect();
        return Err(format!(
            "the entry point performs an operation no handler discharges: {}",
            names.join(", ")
        ));
    }
    let mut handles = Vec::new();
    for f in fns {
        find_handles(f.body(), &mut handles);
    }
    if handles.is_empty() {
        return Err("no handler".into());
    }
    Ok(handles)
}

fn find_handles<'a>(c: &'a TypedComp, out: &mut Vec<&'a TypedComp>) {
    // `Visit` hooks cannot retain node borrows, so this query uses an explicit
    // worklist while it returns the original handle nodes to its callers.
    let mut pending = vec![c];
    while let Some(comp) = pending.pop() {
        if matches!(comp.kind(), TypedCompKind::Handle { .. }) {
            out.push(comp);
        }
        let start = pending.len();
        walk::each_subterm(comp, &mut |child| pending.push(child));
        pending[start..].reverse();
    }
}

/// The function each handle of [`fusion_handles`] sits in, in that order.
fn handle_owners(fns: &[TypedCoreFn]) -> Vec<&TypedCoreFn> {
    let mut owners = Vec::new();
    for f in fns {
        let mut found = Vec::new();
        find_handles(f.body(), &mut found);
        owners.extend(std::iter::repeat_n(f, found.len()));
    }
    owners
}

/// The aborts the threaded convention has no room for, which are reified
/// instead: an abort arm's clause answers with one done payload, and a scope
/// steps over one payload type, so a scope reaching two aborts cannot thread
/// both. An aborting handle inside a producer that threads an accumulator past
/// it has the same problem from the other side: the accumulator would have to
/// survive the abort, and a step has no room for it beside the payload, so
/// the operations that accumulator is threaded for are reified too.
///
/// Only aborts answered by a handler of direct arms are counted. A fold's
/// stopping arm takes the accumulator and answers the fold itself, so it has
/// the room it needs.
fn crowded_aborts(
    owners: &[&TypedCoreFn],
    arms: &[Vec<(Sym, ClauseClass)>],
    reach: &[BTreeSet<Sym>],
    stateful: &BTreeSet<Sym>,
    latent: &Latent,
) -> BTreeSet<Sym> {
    let direct_aborts: BTreeSet<Sym> = arms
        .iter()
        .filter(|arms| {
            arms.iter()
                .all(|(_, class)| matches!(class, ClauseClass::Direct(_) | ClauseClass::Abort))
        })
        .flatten()
        .filter(|(_, class)| *class == ClauseClass::Abort)
        .map(|(op, _)| *op)
        .collect();
    let latent_in = |f: &TypedCoreFn| -> BTreeSet<Sym> {
        latent
            .get(&f.name())
            .map(|s| s.iter().map(|m| m.id).collect())
            .unwrap_or_default()
    };
    let mut crowded = BTreeSet::new();
    for ((owner, arms), reach) in owners.iter().zip(arms).zip(reach) {
        let reached = reach & &direct_aborts;
        if reached.len() > 1 {
            crowded.extend(reached);
        }
        let escaping = latent_in(owner);
        let own = &escaping & &direct_aborts;
        if own.len() > 1 {
            crowded.extend(own);
        }
        let own_aborts: BTreeSet<Sym> = arms
            .iter()
            .filter(|(op, class)| *class == ClauseClass::Abort && direct_aborts.contains(op))
            .map(|(op, _)| *op)
            .collect();
        // The accumulator threaded past the handle cannot survive the abort
        // in a step, so the operations it is threaded for are reified with
        // the abort: the fold that answers them then drives the same cells.
        let threaded_past = &escaping & stateful;
        if !own_aborts.is_empty() && !threaded_past.is_empty() {
            crowded.extend(own_aborts);
            crowded.extend(threaded_past);
        }
    }
    crowded
}

/// The operations a handler of direct clauses answers where a fold elsewhere
/// pins the accumulator to a type of its own. A direct clause takes no
/// accumulator, so such a handler consumes the scope under it with a unit
/// state, and it has no seed of the pinned type to offer instead: the same
/// operation has two shapes in two handles, and the threaded plan records one.
/// The handler drives cells instead, where each handle answers its own
/// performs.
fn pinned_consumers(
    arms: &[Vec<(Sym, ClauseClass)>],
    stateful: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> BTreeSet<Sym> {
    let unit = CoreType::Source(Type::Unit);
    let pinned: BTreeSet<Sym> = arms
        .iter()
        .flatten()
        .filter(|(op, class)| {
            *class == ClauseClass::Fold(FoldAKind::Acc)
                && env.operation(*op).is_some_and(|o| *o.result() != unit)
        })
        .map(|(op, _)| *op)
        .collect();
    arms.iter()
        .filter(|arms| {
            arms.iter()
                .all(|(_, class)| matches!(class, ClauseClass::Direct(_)))
                && arms.iter().any(|(op, _)| pinned.contains(op))
        })
        .flatten()
        .map(|(op, _)| *op)
        .filter(|op| stateful.contains(op))
        .collect()
}

/// The operations whose payload carries an arrow: a callback the clause
/// receives as a value and forces where it likes, possibly under a handler
/// it installs again. A threaded clause would read that callback at one
/// widened convention while its perform site, and any store that keeps it,
/// spell their own; as cells the callback is a closure like any other.
fn arrow_payloads(ops: &BTreeSet<Sym>, env: &VerifyEnv) -> BTreeSet<Sym> {
    fn arrow(ty: &Type) -> bool {
        match ty {
            Type::Fun(..) => true,
            Type::Con(_, args) => args.iter().any(arrow),
            Type::Tuple(ts) => ts.iter().any(arrow),
            _ => false,
        }
    }
    ops.iter()
        .copied()
        .filter(|op| {
            env.operation(*op).is_some_and(|sig| {
                sig.params().iter().any(|p| match p {
                    CoreType::Source(ty) => arrow(ty),
                    CoreType::Thunk(_) | CoreType::Function(_) => true,
                    _ => false,
                })
            })
        })
        .collect()
}

/// Which handles run under a reified operation, and the closure of the
/// operations that reifies.
///
/// A handle whose body or clauses reach a reified operation runs inside cells,
/// so it is answered by a driver over cells rather than threaded state, and the
/// operations it handles are reified in turn, as are the operations its clauses
/// perform: a driver's clause runs as cells code, and an operation it performs
/// must be answered as cells too. The closure stops where no handle reaches
/// the set.
///
/// A direct clause takes no accumulator, so one that performs an operation the
/// fold threads as state has nothing to hand that operation: it needs the rest
/// of its performer as a value after all, and its operation seeds the set.
fn promoted_handles(
    fns: &[TypedCoreFn],
    handles: &[&TypedComp],
    owners: &[&TypedCoreFn],
    arms: &[Vec<(Sym, ClauseClass)>],
    ops: &BTreeSet<Sym>,
    analysis: &StateAnalysis<'_>,
) -> (Vec<bool>, BTreeSet<Sym>) {
    let StateAnalysis {
        latent, flow, env, ..
    } = analysis;
    let reify = analysis.reify();
    let stateful: BTreeSet<Sym> = arms
        .iter()
        .flatten()
        .filter(|(_, class)| matches!(class, ClauseClass::Fold(_) | ClauseClass::Take))
        .map(|(op, _)| *op)
        .collect();
    // What each handle's clauses perform themselves, among the fold's
    // operations, by clause; a thunk the clause forces counts as the clause.
    let performs: Vec<BTreeMap<Sym, BTreeSet<Sym>>> = handles
        .iter()
        .zip(owners)
        .map(|(h, owner)| {
            let TypedCompKind::Handle { ops: clauses, .. } = h.kind() else {
                return BTreeMap::new();
            };
            let loc: Loc = flow::param_loc(owner, flow);
            clauses
                .arms()
                .iter()
                .map(|arm| {
                    // The resumption's type carries the rest of the handled
                    // body's row; resuming is not the clause performing it.
                    let mut loc = loc.clone();
                    loc.insert(arm.resume().name(), BTreeSet::new());
                    let mut performed = BTreeSet::new();
                    latent::latent(arm.body(), latent, &mut performed);
                    flow::performed(arm.body(), &loc, latent, flow, &mut performed);
                    let performed = performed
                        .into_iter()
                        .map(|m| m.id)
                        .filter(|op| ops.contains(op))
                        .collect();
                    (arm.name(), performed)
                })
                .collect()
        })
        .collect();
    let reach: Vec<BTreeSet<Sym>> = handles
        .iter()
        .zip(owners)
        .map(|(h, owner)| {
            let TypedCompKind::Handle {
                body,
                return_body,
                ops,
                ..
            } = h.kind()
            else {
                return BTreeSet::new();
            };
            let loc: Loc = flow::param_loc(owner, flow);
            let mut performed = BTreeSet::new();
            let mut visit = |c: &TypedComp| {
                latent::latent(c, latent, &mut performed);
                flow::performed(c, &loc, latent, flow, &mut performed);
            };
            visit(body);
            ops.arms().iter().for_each(|arm| visit(arm.body()));
            if let Some(rb) = return_body {
                visit(rb);
            }
            performed.into_iter().map(|m| m.id).collect()
        })
        .collect();
    let mut reified: BTreeSet<Sym> = arms
        .iter()
        .flatten()
        .filter(|(_, class)| *class == ClauseClass::Reified)
        .map(|(op, _)| *op)
        .collect();
    for (arms, performs) in arms.iter().zip(&performs) {
        for (op, class) in arms {
            let performs_state = performs
                .get(op)
                .is_some_and(|performed| !performed.is_disjoint(&stateful));
            if reify && matches!(class, ClauseClass::Direct(_)) && performs_state {
                reified.insert(*op);
            }
        }
    }
    if reify {
        reified.extend(crowded_aborts(owners, arms, &reach, &stateful, latent));
        reified.extend(pinned_consumers(arms, &stateful, env));
        reified.extend(arrow_payloads(ops, env));
        reified.extend(mixed_slots(fns, ops, latent, flow));
    }
    let mut promoted = vec![false; handles.len()];
    if reified.is_empty() {
        return (promoted, reified);
    }
    loop {
        let mut grew = false;
        for (i, reach) in reach.iter().enumerate() {
            if promoted[i] || reach.is_disjoint(&reified) {
                continue;
            }
            promoted[i] = true;
            reified.extend(arms[i].iter().map(|(op, _)| *op));
            reified.extend(performs[i].values().flatten().copied());
            grew = true;
        }
        if !grew {
            return (promoted, reified);
        }
    }
}

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
                    finally_body,
                } => {
                    self.comp(body, bound);
                    if let Some(finally_body) = finally_body {
                        self.comp(finally_body, bound);
                    }
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
                if flow::value_sig_in(v, loc, latent, flow).iter().any(|m| ops.contains(&m.id)))
        }
        TypedCompKind::Bind(m, x, n) => {
            produces(m, loc, ops, latent, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig_in(m, loc, latent, flow));
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

/// What a producing head's tail resumes with.
///
/// That decides what its bound result reads: a read observes the
/// pre-operation accumulator, a write unit. `None` for a head that is neither
/// a fused `Do` nor a bind chain ending in one, such as a forced thunk or a
/// call.
#[must_use]
pub fn tail_kind(
    m: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    kinds: &BTreeMap<Sym, FoldAKind>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> Option<FoldAKind> {
    match m.kind() {
        TypedCompKind::Do { operation, .. } if ops.contains(operation) => {
            kinds.get(operation).copied()
        }
        TypedCompKind::Bind(mm, x, n) if !produces(mm, loc, ops, latent, flow) => {
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), flow::result_sig_in(mm, loc, latent, flow));
            tail_kind(n, &loc2, ops, kinds, latent, flow)
        }
        _ => None,
    }
}

/// Whether some scope binds the value of a producing head on the state
/// channel that [`tail_kind`] cannot classify and reads that value later. An
/// accumulator-answer scope rebuilds a unit value on its own, so a unit binder
/// there does not count.
fn reads_produced_value(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    let ops: BTreeSet<Sym> = plan
        .ops
        .iter()
        .copied()
        .filter(|op| !plan.value_shaped(*op) && !plan.reified.contains(op))
        .collect();
    fns.iter().any(|f| {
        binds_produced_value(
            f.body(),
            &flow::param_loc(f, flow),
            &ops,
            plan,
            latent,
            flow,
        )
    })
}

fn binds_produced_value(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    let mut found = false;
    let mut values = |c: &TypedComp, loc: &Loc| {
        walk::each_value(c, &mut |v| {
            if let TypedValueKind::Thunk(body) = &peel(v).kind {
                found |= binds_produced_value(body, loc, ops, plan, latent, flow);
            }
        });
    };
    let TypedCompKind::Bind(m, x, n) = c.kind() else {
        values(c, loc);
        each_subcomp(c, &mut |sc| {
            found |= binds_produced_value(sc, loc, ops, plan, latent, flow);
        });
        return found;
    };
    let rebuilt =
        plan.answer == StateAnswerMode::Accumulator && *x.ty() == CoreType::Source(Type::Unit);
    let read = !rebuilt
        && free_comp_vars(n).contains(&x.name())
        && produces(m, loc, ops, latent, flow)
        && tail_kind(m, loc, ops, &plan.kinds, latent, flow).is_none();
    read || binds_produced_value(m, loc, ops, plan, latent, flow) || {
        let mut loc2 = loc.clone();
        loc2.insert(x.name(), flow::result_sig_in(m, loc, latent, flow));
        binds_produced_value(n, &loc2, ops, plan, latent, flow)
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
    let StateAnalysis { ids, .. } = analysis;
    if plan.ops.iter().any(|op| ids.id(*op).is_none()) {
        analysis.note("an operation without an id");
        return false;
    }
    if plan.answer != StateAnswerMode::Producer {
        return true;
    }
    match coincides(plan, fns, analysis) {
        Ok(true) => true,
        Ok(false) => {
            analysis.note("a fold body whose answer is not the accumulator");
            false
        }
        Err(why) => {
            analysis.note(why);
            false
        }
    }
}

/// Whether every fold handle's body answers with the accumulator it threads.
///
/// `Err` when the handles cannot be collected at all, which is a different
/// answer from a body that does not coincide: the caller decides which of the
/// two it can recover from.
fn coincides(
    plan: &FoldPlan,
    fns: &[TypedCoreFn],
    analysis: &StateAnalysis<'_>,
) -> Result<bool, String> {
    let StateAnalysis { latent, flow, .. } = analysis;
    let handles = fusion_handles(fns, latent, flow, analysis.widen())?;
    Ok(handles.iter().all(|h| {
        let TypedCompKind::Handle { body, .. } = h.kind() else {
            return true;
        };
        // The shared judgment decides what a fold is, a stopping arm included:
        // a handle that answers its own abort still yields the accumulator on
        // the arms that continue, so its body is held to the same answer.
        let folding = judge_handle(h, latent, analysis.widen(), analysis.reify())
            .is_ok_and(|judged| matches!(judged.class, HandleClass::Fold { .. }));
        !folding || value_coincident(body, plan, fns, latent, flow, &mut BTreeSet::new())
    }))
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
#[must_use]
#[allow(clippy::too_many_lines)] // One arm per clause class; the exhaustive match is the point.
pub fn fold_uniform(fns: &[TypedCoreFn], analysis: &StateAnalysis<'_>) -> Option<FoldPlan> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
        ..
    } = analysis;
    let mut ops = BTreeSet::new();
    for f in fns {
        collect_ops(f.body(), &mut ops);
    }
    if ops.is_empty() {
        return analysis.decline("no operation");
    }
    let handles = match fusion_handles(fns, latent, flow, analysis.widen()) {
        Ok(handles) => handles,
        Err(why) => return analysis.decline(why),
    };

    let mut kinds = BTreeMap::new();
    // What each operation's direct clauses resume with, where they agree.
    let mut directs: BTreeMap<Sym, Option<FoldAKind>> = BTreeMap::new();
    let mut classes: BTreeMap<Sym, ClauseClass> = BTreeMap::new();
    let mut answer = StateAnswerMode::Accumulator;
    // The aborts a fold handler answers itself: their clause takes the
    // accumulator like any other arm of that handler, so they keep the state
    // channel's clause where an abort answered elsewhere takes the value
    // channel's.
    let mut folded_stops: BTreeSet<Sym> = BTreeSet::new();
    let mut consumed: BTreeSet<Sym> = BTreeSet::new();
    let mut takes = 0u32;
    // Operations that share a handler share a channel. So does an operation a
    // clause performs: the clause runs with that operation's evidence in hand,
    // so the operations it handles join that channel.
    let mut groups: Vec<BTreeSet<Sym>> = Vec::new();
    let arms: Vec<Vec<(Sym, ClauseClass)>> = match handles
        .iter()
        .map(|h| judge_arms(h, latent, analysis.widen(), analysis.reify()))
        .collect()
    {
        Ok(arms) => arms,
        Err(why) => return analysis.decline(why),
    };
    // The operations some handler reifies, and the handles promoted into the
    // reified rewrite because they run under one.
    let (promoted, mut reified) =
        promoted_handles(fns, &handles, &handle_owners(fns), &arms, &ops, analysis);

    for ((h, arms), promoted) in handles.iter().zip(&arms).zip(&promoted) {
        if *promoted {
            // A promoted handle is a driver over cells: its operations are
            // consumed here, but it classifies nothing for the threaded fold,
            // so how its arms agree is not asked.
            consumed.extend(arms.iter().map(|(op, _)| *op));
        } else {
            // A handle the fold threads answers to the shared judgment.
            let judged = match judge_handle(h, latent, analysis.widen(), analysis.reify()) {
                Ok(judged) => judged,
                Err(why) => return analysis.decline(why),
            };
            if matches!(
                judged.class,
                HandleClass::Fold {
                    transforms: true,
                    ..
                }
            ) {
                answer = StateAnswerMode::Producer;
            }
            if let HandleClass::Fold {
                abort: Some(op), ..
            } = judged.class
            {
                folded_stops.insert(op);
            }
            for (op, class) in &judged.arms {
                consumed.insert(*op);
                match class {
                    ClauseClass::Fold(kind) => {
                        kinds.insert(*op, *kind);
                    }
                    ClauseClass::Take => takes += 1,
                    // A forwarder is a source: the handler it forwards to
                    // classifies the operation.
                    ClauseClass::Forward => continue,
                    ClauseClass::Direct(kind) => {
                        directs
                            .entry(*op)
                            .and_modify(|agreed| {
                                if *agreed != *kind {
                                    *agreed = None;
                                }
                            })
                            .or_insert(*kind);
                    }
                    ClauseClass::Abort => {}
                    // A reified clause is answered from the queue, so it agrees
                    // with nothing: the operation's channel is decided by the
                    // reification alone, not by how another handler of it resumes.
                    ClauseClass::Reified => {
                        reified.insert(*op);
                        continue;
                    }
                }
                // An operation folded anywhere threads state everywhere, and a
                // direct clause reads that state too. An abort has one shape, so
                // an operation aborted here and handled otherwise elsewhere has no
                // one evidence.
                match classes.get(op) {
                    None => {
                        classes.insert(*op, *class);
                    }
                    // An operation one handler aborts is stepped everywhere, since
                    // the producer that performs it has one evidence type. So the
                    // abort wins the classification and the handler that resumes
                    // answers a stepped clause.
                    Some(prev)
                        if (*prev == ClauseClass::Abort) != (*class == ClauseClass::Abort)
                            && !analysis.widen() =>
                    {
                        return analysis.decline(format!(
                            "`{}` aborts in one handler and resumes in another",
                            op.as_str()
                        ));
                    }
                    Some(prev) if *prev != ClauseClass::Abort && *class == ClauseClass::Abort => {
                        classes.insert(*op, *class);
                    }
                    Some(prev) if !stateful(*prev) && stateful(*class) => {
                        classes.insert(*op, *class);
                    }
                    Some(_) => {}
                }
            }
        }
        let TypedCompKind::Handle {
            ops: handler_arms,
            return_body,
            ..
        } = h.kind()
        else {
            return None;
        };
        let mut performed = BTreeSet::new();
        for arm in handler_arms.arms() {
            latent::latent(arm.body(), latent, &mut performed);
        }
        if let Some(rb) = return_body {
            latent::latent(rb, latent, &mut performed);
        }
        let mut group: BTreeSet<Sym> = arms.iter().map(|(op, _)| *op).collect();
        group.extend(
            performed
                .into_iter()
                .map(|m| m.id)
                .filter(|op| ops.contains(op)),
        );
        groups.push(group);
    }

    // Every streamed operation must be handled here.
    if consumed != ops {
        let unhandled: Vec<&str> = ops.difference(&consumed).map(|op| op.as_str()).collect();
        return analysis.decline(format!("unhandled: {}", unhandled.join(", ")));
    }

    // A parameter that carries evidence at one call carries it at every call,
    // since the callee has one signature. A call that hands that parameter a
    // thunk carrying nothing has no evidence to pass, so a callee used both
    // ways has no threaded form.
    let threaded: BTreeSet<Sym> = ops.difference(&reified).copied().collect();
    if let Some(f) = fns.iter().find(|f| {
        let loc: Loc = flow::param_loc(f, flow);
        let mut mixed = BTreeSet::new();
        mixed_call(f.body(), &loc, &threaded, latent, flow, &mut mixed);
        !mixed.is_empty()
    }) {
        return analysis.decline(format!(
            "`{}` hands one parameter thunks with and without evidence",
            f.name().as_str()
        ));
    }

    // Operations that share a producer share a channel too. A component with a
    // fold or a take threads an accumulator; one of direct and abort clauses
    // only threads by value; an abort beside an accumulator takes the
    // accumulator's channel and keeps the value channel's clause.
    for f in fns {
        let carried = producer_ops(f, &ops, latent);
        if !carried.is_empty() {
            groups.push(carried);
        }
    }
    let aborts: BTreeSet<Sym> = classes
        .iter()
        .filter(|(_, class)| **class == ClauseClass::Abort)
        .map(|(op, _)| *op)
        .collect();
    // An abandoned cleanup runs as the abort's step propagates outward, which
    // is before the catching clause body runs where the spec orders it after.
    // The two orders agree only when no catching clause does anything.
    if fns.iter().any(|f| walk::contains_cleanup(f.body()))
        && handles.iter().any(|h| {
            let TypedCompKind::Handle { ops: arms, .. } = h.kind() else {
                return false;
            };
            arms.arms().iter().any(|arm| {
                aborts.contains(&arm.name()) && !matches!(arm.body().sig().effects(), EffRow::Empty)
            })
        })
    {
        return analysis.decline("a cleanup beside an abort clause that performs effects");
    }
    // An operation whose clause leaves through a further-out abort aborts
    // wherever it is performed, because the handler answers it by not
    // returning. The relation is transitive, so it is closed to a fixpoint.
    let mut taint: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
    if analysis.widen() {
        let mut raises: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
        for h in &handles {
            let TypedCompKind::Handle { ops: arms, .. } = h.kind() else {
                return None;
            };
            for arm in arms
                .arms()
                .iter()
                .filter(|arm| !aborts.contains(&arm.name()))
            {
                let mut performed = BTreeSet::new();
                latent::latent(arm.body(), latent, &mut performed);
                raises.entry(arm.name()).or_default().extend(
                    performed
                        .into_iter()
                        .map(|m| m.id)
                        .filter(|op| ops.contains(op)),
                );
            }
        }
        loop {
            let mut changed = false;
            for (op, performed) in &raises {
                let mut found = BTreeSet::new();
                for p in performed {
                    if aborts.contains(p) {
                        found.insert(*p);
                    }
                    if let Some(through) = taint.get(p) {
                        found.extend(through.iter().copied());
                    }
                }
                found.remove(op);
                if !found.is_empty() && taint.get(op) != Some(&found) {
                    taint.insert(*op, found);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    let mut by_value = BTreeSet::new();
    // The aborts admitted beside an accumulator, kept so the answer convention
    // decided below can refuse the one shape they have no room in.
    let mut folded_aborts: BTreeSet<Sym> = BTreeSet::new();
    let mut stepped: BTreeMap<Sym, Sym> = BTreeMap::new();
    for component in components(groups) {
        if !component
            .iter()
            .any(|op| classes.get(op).is_some_and(|c| stateful(*c)))
        {
            by_value.extend(component);
            continue;
        }
        // An abort beside an accumulator still takes no accumulator: it never
        // resumes, so its clause answers a step over the payload it carries,
        // which is the value channel's clause. The two travel together, the
        // threaded accumulator becoming a step whose done payload is the
        // abort's.
        let raised: Vec<Sym> = component
            .iter()
            .copied()
            .filter(|op| aborts.contains(op))
            .collect();
        match raised.as_slice() {
            [] => {}
            // A take decides what the one step over the accumulator means, and
            // an abort would need a second.
            [op] if takes > 0 => {
                return analysis.decline(format!(
                    "abort `{}` in a program that stops early",
                    op.as_str()
                ))
            }
            // A fold handler answering its own abort keeps that arm on the
            // state channel; one answered further out never sees the
            // accumulator, so its clause is the value channel's.
            [op] => {
                if !folded_stops.contains(op) {
                    by_value.insert(*op);
                }
                folded_aborts.insert(*op);
                stepped.extend(component.iter().map(|o| (*o, *op)));
            }
            [first, ..] => {
                return analysis.decline(format!(
                    "several aborts from `{}` share a channel with a fold",
                    first.as_str()
                ))
            }
        }
    }

    // A direct clause takes no accumulator: it resumes in tail position with a
    // value of its own and leaves the state exactly as it found it. So an
    // operation whose every clause is direct rides the value channel even where
    // a fold shares its component, as an abort does, and only one still bound
    // to the state channel by a clause of its own decides anything about the
    // convention there.
    let mut folded_directs: BTreeSet<Sym> = BTreeSet::new();
    if analysis.widen() {
        for (op, kind) in directs {
            if matches!(classes.get(&op), Some(ClauseClass::Direct(_))) {
                if by_value.insert(op) {
                    folded_directs.insert(op);
                }
                continue;
            }
            if let Some(kind) = kind.filter(|_| !by_value.contains(&op)) {
                kinds.entry(op).or_insert(kind);
            }
        }
    }

    let Some(pins) = pins(&kinds, env) else {
        return analysis.decline("fold clauses pin one accumulator to different types");
    };
    let mut plan = FoldPlan {
        pins,
        ops,
        kinds,
        answer,
        early: if takes > 0 {
            EarlyExitMode::ShortCircuit
        } else {
            EarlyExitMode::Continue
        },
        aborts,
        taint,
        by_value,
        folded_aborts,
        stepped,
        folded_directs,
        entry: analysis.entry.clone(),
        widen: analysis.widen(),
        reify: analysis.reify(),
        reified,
    };

    // A producer-answer program whose fold body does not answer with the
    // accumulator carries the value beside it instead of rebuilding it. The
    // accumulator-only conventions stay where they hold, because the pair costs
    // a product at every scope boundary that crosses a function.
    if plan.widen
        && plan.answer == StateAnswerMode::Producer
        && !plan.early.short_circuits()
        && coincides(&plan, fns, analysis) == Ok(false)
    {
        plan.answer = StateAnswerMode::Pair;
    }

    // A clause resuming with a value of its own decides the same thing on its
    // own: the accumulator cannot stand for that value at the perform site, so
    // every scope carries the two together. A take decides what the one step
    // over the accumulator means, and a resumed value would need a second.
    if plan.kinds.values().any(|kind| *kind == FoldAKind::Value) {
        if plan.early.short_circuits() {
            return analysis.decline("a clause resuming with a value beside a take");
        }
        plan.answer = StateAnswerMode::Pair;
    }

    // So does a scope that binds the value of a producing head which is
    // neither a read nor a write of a fused operation and goes on to read it:
    // a forced thunk carrying a read, a call answering with a value of its own.
    // A read is rebuilt as the prior accumulator and a write as unit, but
    // nothing recreates such a value from the accumulator, so the scope
    // carries the two together.
    if plan.widen
        && plan.answer != StateAnswerMode::Pair
        && !plan.early.short_circuits()
        && reads_produced_value(fns, &plan, latent, flow)
    {
        plan.answer = StateAnswerMode::Pair;
    }

    // Every producer must have an expressible threaded signature, which is where
    // typing the one accumulator it threads is decided: chains that share no
    // producer are free to disagree on the accumulator, and do.
    for f in fns {
        // A reified operation threads nothing, so its producers have no
        // threaded signature to check for it.
        let ops = &producer_ops(f, &plan.ops, latent) - &plan.reified;
        if !ops.is_empty() {
            let Some(named) = name_ambient(f, &ops, &plan, ids) else {
                return analysis.decline(format!("`{}`: no ambient row", f.name().as_str()));
            };
            if let Err(why) = plan_producer(&named, &ops, &plan, ids, fns, latent, env) {
                return analysis.decline(format!("`{}`: {why}", f.name().as_str()));
            }
        }
    }

    Some(plan)
}

/// Whether a clause of this class threads the accumulator.
const fn stateful(class: ClauseClass) -> bool {
    matches!(class, ClauseClass::Fold(_) | ClauseClass::Take)
}

/// The connected components of `groups` under sharing a member.
fn components(groups: Vec<BTreeSet<Sym>>) -> Vec<BTreeSet<Sym>> {
    let mut out: Vec<BTreeSet<Sym>> = Vec::new();
    for group in groups {
        let mut merged = group;
        let (touching, rest): (Vec<_>, Vec<_>) =
            out.into_iter().partition(|c| !c.is_disjoint(&merged));
        for c in touching {
            merged.extend(c);
        }
        out = rest;
        out.push(merged);
    }
    out
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

/// The operations a parameter carries at some call and not at another. A
/// threaded callee has one signature, with one evidence binder per operation
/// its parameter carries, so a call handing that parameter a thunk carrying
/// none has no evidence to pass; as cells the parameter takes none and the
/// two calls agree.
fn mixed_slots(
    fns: &[TypedCoreFn],
    ops: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> BTreeSet<Sym> {
    let mut mixed = BTreeSet::new();
    for f in fns {
        let loc: Loc = flow::param_loc(f, flow);
        mixed_call(f.body(), &loc, ops, latent, flow, &mut mixed);
    }
    mixed
}

/// Collects the operations of every parameter that carries evidence somewhere
/// and is handed a thunk carrying none here.
fn mixed_call(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
    mixed: &mut BTreeSet<Sym>,
) {
    let carried = |sig: &Sig| -> BTreeSet<Sym> {
        sig.iter()
            .map(|m| m.id)
            .filter(|op| ops.contains(op))
            .collect()
    };
    let values = |c: &TypedComp, loc: &Loc, mixed: &mut BTreeSet<Sym>| {
        walk::each_value(c, &mut |v| {
            if let TypedValueKind::Thunk(body) = &peel(v).kind {
                mixed_call(body, loc, ops, latent, flow, mixed);
            }
        });
    };
    match c.kind() {
        TypedCompKind::Call { callee, args, .. } => {
            values(c, loc, mixed);
            if let Some(slots) = flow.param.get(callee) {
                for (slot, a) in slots.iter().zip(args) {
                    let slot = carried(slot);
                    if !slot.is_empty()
                        && carried(&flow::value_sig_in(a, loc, latent, flow)).is_empty()
                    {
                        mixed.extend(slot);
                    }
                }
            }
        }
        TypedCompKind::Bind(m, x, n) => {
            mixed_call(m, loc, ops, latent, flow, mixed);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), flow::result_sig_in(m, loc, latent, flow));
            mixed_call(n, &loc2, ops, latent, flow, mixed);
        }
        _ => {
            values(c, loc, mixed);
            each_subcomp(c, &mut |sc| {
                mixed_call(sc, loc, ops, latent, flow, mixed);
            });
        }
    }
}
