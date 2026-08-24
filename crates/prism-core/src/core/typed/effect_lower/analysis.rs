//! Typed monadic calling-convention planning.
//!
//! This module decides which declarations share the free-monad convention
//! before any computation is rewritten. The plan is declaration-owned: later
//! handler, native-region, and `LocalPartial` builders consume it rather than
//! re-inferring openness or scope from partially lowered trees.

use std::cmp::Ordering;
use std::collections::{btree_map, BTreeMap, BTreeSet};
use std::ptr;

use prism_common::fixpoint::least_fixpoint;
use prism_common::sym::Sym;
use prism_syntax::names::ENTRY_POINT;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::{
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue,
    TypedValueKind,
};
use super::flow;
use super::latent::{self, Latent, MaskOp};
use super::plan::{self, collect_calls, EffectPlan};
use super::walk::{
    collect_ops, each_subcomp, each_subterm, each_value, thunks_in_comp, top_thunks_in_value,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MonadicScope {
    Selective,
    WholeProgram,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MonadicRegionPlan {
    pub members: BTreeSet<Sym>,
    pub entries: BTreeSet<Sym>,
    pub genuine_effects: BTreeSet<Sym>,
    /// The parameter slots that receive a computation the free-monad
    /// convention owns, per function. A member forces such a slot through the
    /// monadic head path; a declaration outside the region must not force one
    /// at all, which is why forcing one is what makes a function a member.
    pub monadic_params: BTreeMap<Sym, BTreeSet<usize>>,
    pub scope: MonadicScope,
}

/// What a handler is asked about needs both maps: the latent one, which names
/// the ops a body performs by itself, and the flow, which names the ops it
/// performs by forcing a computation handed to it.
///
/// Carrying them as one value keeps the openness question from being asked with
/// only half the answer.
#[derive(Clone, Copy, Debug)]
pub struct Effects<'a> {
    pub latent: &'a Latent,
    pub flow: &'a flow::ThunkFlow,
}

impl<'a> Effects<'a> {
    /// The two maps a solved effect plan carries.
    #[must_use]
    pub const fn of(plan: &'a EffectPlan) -> Self {
        Self {
            latent: plan.latent(),
            flow: plan.flow(),
        }
    }
}

impl MonadicRegionPlan {
    #[must_use]
    pub fn handler_is_open(
        &self,
        comp: &TypedComp,
        effects: Effects<'_>,
        scope: &flow::Loc,
    ) -> bool {
        if self.scope == MonadicScope::WholeProgram {
            return true;
        }
        let TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } = comp.kind()
        else {
            return false;
        };
        let mut escaping = BTreeSet::new();
        latent::handle_escapes(
            body,
            return_body.as_deref(),
            ops,
            effects.latent,
            &mut escaping,
        );
        // The latent map is not flow aware, so an action that performs only by
        // forcing a computation handed to it names no op there. Such an op
        // leaves this handler exactly like one performed in place, and a
        // handler that reads itself as closed on the strength of the latent map
        // alone compiles a dispatch table with no case for it. This handler's
        // own ops are discharged here, exactly as they are for an op the action
        // performs in place.
        let mut forced = BTreeSet::new();
        forced_thunk_ops(
            body,
            scope,
            effects,
            Islands::Enter,
            HandedOff::Count,
            &mut forced,
        );
        for op in ops.arms() {
            forced.remove(&MaskOp {
                id: op.name(),
                depth: 0,
            });
        }
        escaping.extend(forced);
        !escaping.is_empty()
    }

    #[must_use]
    pub fn native_closed(
        &self,
        comp: &TypedComp,
        effects: Effects<'_>,
        scope: &flow::Loc,
        native_enabled: bool,
    ) -> bool {
        if !native_enabled || self.handler_is_open(comp, effects, scope) {
            return false;
        }
        let TypedCompKind::Handle { ops, .. } = comp.kind() else {
            return false;
        };
        !ops.arms().is_empty()
    }

    #[must_use]
    pub fn native_eligible(
        &self,
        comp: &TypedComp,
        effects: Effects<'_>,
        scope: &flow::Loc,
        native_enabled: bool,
    ) -> bool {
        if !self.native_closed(comp, effects, scope, native_enabled) {
            return false;
        }
        let TypedCompKind::Handle { ops, .. } = comp.kind() else {
            return false;
        };
        resume_tail_only(ops.arms())
    }
}

/// The monadic region plan.
///
/// `force_whole` requests whole-program scope for a program the analysis would
/// have confined; the widening is decided here, not patched onto the result,
/// because `members` and `entries` follow from it.
pub fn plan(
    functions: &[TypedCoreFn],
    effects: &EffectPlan,
    force_whole: bool,
) -> MonadicRegionPlan {
    let genuine_effects = effects.genuine().clone();
    // A region can be confined only when nothing escapes it: no untrackable
    // thunk, and no capture whose forcing the thunk signatures fail to
    // describe. A capture the signatures *do* describe no longer widens: the
    // computation it holds is built by the monadic builder and forced through
    // the monadic head path, so the region reaches through the thunk instead of
    // swallowing the function that built it.
    let whole = force_whole || effects.opaque_thunks() || !effects.opaque_captures().is_empty();
    let monadic_params = monadic_params(effects);
    let members = if whole {
        functions.iter().map(TypedCoreFn::name).collect()
    } else {
        confined_members(functions, effects, &genuine_effects, &monadic_params)
    };
    let entry = Sym::new(ENTRY_POINT);
    let entries = if members.contains(&entry) {
        BTreeSet::from([entry])
    } else {
        BTreeSet::new()
    };
    MonadicRegionPlan {
        members,
        entries,
        genuine_effects,
        monadic_params,
        scope: if whole {
            MonadicScope::WholeProgram
        } else {
            MonadicScope::Selective
        },
    }
}

/// The thunk-valued parameter slots that receive a computation the free-monad
/// convention owns, read off the interprocedural flow the plan already solved.
fn monadic_params(effects: &EffectPlan) -> BTreeMap<Sym, BTreeSet<usize>> {
    effects
        .flow()
        .param
        .iter()
        .map(|(name, slots)| {
            let slots = slots
                .iter()
                .enumerate()
                .filter_map(|(index, signature)| (!signature.is_empty()).then_some(index))
                .collect();
            (*name, slots)
        })
        .filter(|(_, slots): &(Sym, BTreeSet<usize>)| !slots.is_empty())
        .collect()
}

/// The members of a confined region: every function that still performs an
/// operation, plus every one that receives or forces a computation the
/// free-monad convention owns, closed under the callers that would otherwise
/// call one from direct code.
///
/// The receivers and forcers are not covered by the genuine set because the
/// latent map is not flow aware: a forwarder that only applies its
/// thunk-valued parameter names no operation of its own. A slot's convention
/// is one flow fact, so owning a monadic slot is enough on its own: the caller
/// builds that argument at the monadic convention off the same fact, and a
/// declaration outside the region has no way to hold an `Eff` cell, whether it
/// forces the slot, forwards it, or forces it from inside a `handle` its own
/// body installs. Reading membership off the slot rather than off the force
/// site is what keeps the two sides of the boundary reading the same fact.
///
/// The caller closure is what makes a member's `Eff`-returning signature
/// consumable, and it terminates at a `handle`: a handled action is built by
/// the monadic builder inside any declaration, so a capturer that handles what
/// it captured bounds the region rather than joining it.
fn confined_members(
    functions: &[TypedCoreFn],
    effects: &EffectPlan,
    genuine: &BTreeSet<Sym>,
    monadic_params: &BTreeMap<Sym, BTreeSet<usize>>,
) -> BTreeSet<Sym> {
    let mut base = genuine.clone();
    base.extend(monadic_params.keys().copied());
    for function in functions {
        let scope = flow::param_loc(function, effects.flow());
        if forces_monadic(function.body(), &scope, effects) {
            base.insert(function.name());
        }
    }

    let edges: BTreeMap<Sym, BTreeSet<Sym>> = functions
        .iter()
        .map(|function| {
            let mut callees = BTreeSet::new();
            direct_calls(function.body(), effects.latent(), &mut callees);
            (function.name(), callees)
        })
        .collect();
    let seed: BTreeMap<Sym, BTreeSet<Sym>> =
        edges.keys().map(|name| (*name, BTreeSet::new())).collect();
    let reachable = least_fixpoint(seed, |name, current| {
        let mut out = edges[name].clone();
        for callee in &edges[name] {
            if let Some(indirect) = current.get(callee) {
                out.extend(indirect.iter().copied());
            }
        }
        out
    });

    let mut members = base.clone();
    for (name, callees) in &reachable {
        if !callees.is_disjoint(&base) {
            members.insert(*name);
        }
    }
    members
}

/// Whether a `handle` a computation installs is entered by the traversal below.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Islands {
    /// A handled action is an island of the monadic convention inside any
    /// declaration, so what it forces says nothing about the convention of the
    /// declaration around it.
    Skip,
    /// The island itself is what is being asked about, so its action counts.
    Enter,
}

/// Whether a computation handed to a callee counts as performed here.
#[derive(Clone, Copy, PartialEq, Eq)]
enum HandedOff {
    /// Not counted. The question is what this declaration forces where a direct
    /// force would stand, and a callee that forces the argument owns that force
    /// itself: the slot it receives is what makes *it* a region member.
    Ignore,
    /// Counted. The question is what can still reach a handler, and the callee
    /// forces the argument inside this handler's extent, so the op arrives at
    /// its driver exactly as an in-place force would deliver it. Neither map
    /// names such an op: the latent one records what the callee performs by
    /// itself, which for a forwarder is nothing, and the force that performs it
    /// sits in the callee's body rather than here.
    Count,
}

/// The operations `comp` can still perform by forcing a computation the
/// free-monad convention owns, with the thunk signatures threaded through the
/// binders that introduce them. A thunk value carries its own convention, so a
/// thunk this computation only builds contributes nothing here.
fn forced_thunk_ops(
    comp: &TypedComp,
    scope: &flow::Loc,
    effects: Effects<'_>,
    islands: Islands,
    handed: HandedOff,
    out: &mut BTreeSet<MaskOp>,
) {
    match comp.kind() {
        TypedCompKind::Force(value) => out.extend(flow::value_sig(value, scope, effects.latent)),
        TypedCompKind::Handle { .. } if islands == Islands::Skip => {}
        TypedCompKind::Call { args, .. }
        | TypedCompKind::App { args, .. }
        | TypedCompKind::Do { args, .. }
            if handed == HandedOff::Count =>
        {
            for argument in args {
                out.extend(flow::value_sig(argument, scope, effects.latent));
            }
            each_subcomp(comp, &mut |child| {
                forced_thunk_ops(child, scope, effects, islands, handed, out);
            });
        }
        TypedCompKind::Bind(head, binder, tail) => {
            forced_thunk_ops(head, scope, effects, islands, handed, out);
            let mut inner = scope.clone();
            inner.insert(
                binder.name(),
                flow::result_sig(head, scope, effects.latent, effects.flow),
            );
            forced_thunk_ops(tail, &inner, effects, islands, handed, out);
        }
        TypedCompKind::Lam(params, body) => {
            let mut inner = scope.clone();
            for param in params {
                inner.remove(&param.name());
            }
            forced_thunk_ops(body, &inner, effects, islands, handed, out);
        }
        TypedCompKind::Case(_, arms) => {
            for (pattern, body) in arms {
                let mut inner = scope.clone();
                for binder in pattern_binders(pattern) {
                    inner.remove(&binder.name());
                }
                forced_thunk_ops(body, &inner, effects, islands, handed, out);
            }
        }
        _ => each_subcomp(comp, &mut |child| {
            forced_thunk_ops(child, scope, effects, islands, handed, out);
        }),
    }
}

/// Whether `comp` forces a computation the free-monad convention owns where a
/// direct declaration would emit a direct force.
fn forces_monadic(comp: &TypedComp, scope: &flow::Loc, effects: &EffectPlan) -> bool {
    let mut forced = BTreeSet::new();
    forced_thunk_ops(
        comp,
        scope,
        Effects::of(effects),
        Islands::Skip,
        HandedOff::Ignore,
        &mut forced,
    );
    !forced.is_empty()
}

/// The functions `comp` calls from a position a direct declaration lowers
/// directly: everything but a `handle`, whose body and clauses the monadic
/// builder owns wherever they sit, and a thunk the convention predicate reports
/// as monadic, whose body the monadic builder likewise owns.
fn direct_calls(comp: &TypedComp, latent: &Latent, out: &mut BTreeSet<Sym>) {
    if matches!(comp.kind(), TypedCompKind::Handle { .. }) {
        return;
    }
    if let TypedCompKind::Call { callee, .. } = comp.kind() {
        out.insert(*callee);
    }
    each_subcomp(comp, &mut |child| direct_calls(child, latent, out));
    each_value(comp, &mut |value| {
        let mut thunks = Vec::new();
        top_thunks_in_value(value, &mut thunks);
        for thunk in thunks {
            if !plan::body_is_monadic(thunk, latent) {
                direct_calls(thunk, latent, out);
            }
        }
    });
}

fn pattern_binders(pattern: &TypedPattern) -> Vec<TypedBinder> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.clone()],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().cloned().collect()
        }
    }
}

/// The clean whole-style component for `LocalPartial`, and the declarations the
/// fused rest calls across its bare-returning boundary.
pub fn local_region(
    functions: &[TypedCoreFn],
    effects: &EffectPlan,
) -> Option<(BTreeSet<Sym>, BTreeSet<Sym>)> {
    let closure_flow = closure_flow(functions);
    let escaping = effects.escaping().clone();
    if escaping.is_empty() {
        return None;
    }

    let latent = effects.latent();
    let by_name: BTreeMap<Sym, &TypedCoreFn> = functions.iter().map(|f| (f.name(), f)).collect();
    let footprint: BTreeMap<Sym, BTreeSet<Sym>> = functions
        .iter()
        .map(|function| {
            let mut operations = BTreeSet::new();
            collect_ops(function.body(), &mut operations);
            if let Some(latent) = latent.get(&function.name()) {
                operations.extend(latent.iter().map(|masked| masked.id));
            }
            (function.name(), operations)
        })
        .collect();

    let mut inert: BTreeSet<Sym> = functions.iter().map(TypedCoreFn::name).collect();
    loop {
        let mut changed = false;
        for function in functions {
            if !inert.contains(&function.name()) {
                continue;
            }
            let mut callees = BTreeSet::new();
            collect_calls(function.body(), &mut callees);
            if has_app(function.body())
                || !footprint[&function.name()].is_empty()
                || callees
                    .iter()
                    .any(|callee| by_name.contains_key(callee) && !inert.contains(callee))
            {
                inert.remove(&function.name());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut region = escaping;
    loop {
        let mut changed = false;
        for name in region.clone() {
            if let Some(function) = by_name.get(&name) {
                let mut callees = BTreeSet::new();
                collect_calls(function.body(), &mut callees);
                for callee in callees {
                    if by_name.contains_key(&callee) && !inert.contains(&callee) {
                        changed |= region.insert(callee);
                    }
                }
            }
        }
        let tainted: BTreeSet<Sym> = region
            .iter()
            .flat_map(|name| footprint[name].iter().copied())
            .collect();
        for function in functions {
            if !footprint[&function.name()].is_disjoint(&tainted) {
                changed |= region.insert(function.name());
            }
        }
        if !changed {
            break;
        }
    }

    let entry_point = Sym::new(ENTRY_POINT);
    let region_operations: BTreeSet<Sym> = region
        .iter()
        .flat_map(|name| footprint[name].iter().copied())
        .collect();
    if functions
        .iter()
        .filter(|function| !region.contains(&function.name()))
        .any(|function| !footprint[&function.name()].is_disjoint(&region_operations))
    {
        return None;
    }

    for function in functions
        .iter()
        .filter(|function| !region.contains(&function.name()))
    {
        let mut thunks = Vec::new();
        thunks_in_comp(function.body(), &mut thunks);
        for thunk in thunks {
            let mut callees = BTreeSet::new();
            collect_calls(thunk, &mut callees);
            if !callees.is_disjoint(&region) {
                return None;
            }
        }
    }

    let mut entries = BTreeSet::new();
    for function in functions {
        if region.contains(&function.name()) {
            continue;
        }
        let mut callees = BTreeSet::new();
        collect_calls(function.body(), &mut callees);
        entries.extend(callees.into_iter().filter(|callee| region.contains(callee)));
    }
    if region.contains(&entry_point) {
        entries.insert(entry_point);
    }
    for function in functions
        .iter()
        .filter(|function| region.contains(&function.name()))
    {
        let mut callees = BTreeSet::new();
        collect_calls(function.body(), &mut callees);
        if callees
            .iter()
            .any(|callee| *callee != entry_point && entries.contains(callee))
        {
            return None;
        }
    }

    if closure_crosses_boundary(functions, &region, &closure_flow) {
        return None;
    }
    for entry in entries.iter().filter(|entry| **entry != entry_point) {
        if let Some(function) = by_name.get(entry) {
            let parameters: BTreeSet<Sym> =
                function.params().iter().map(TypedBinder::name).collect();
            if closure_flow
                .ret
                .get(entry)
                .is_some_and(ClosureShape::carries)
                || applies_parameter(function.body(), &parameters)
            {
                return None;
            }
        }
    }
    (!region.contains(&entry_point)).then_some((region, entries))
}

fn has_app(comp: &TypedComp) -> bool {
    if matches!(comp.kind(), TypedCompKind::App { .. }) {
        return true;
    }
    let mut found = false;
    each_subterm(comp, &mut |child| found |= has_app(child));
    found
}

// Closure shape is a finite set of allocation sites. Keeping the site, rather
// than only a yes/no fact, lets dynamic application use the result summary of
// the closure that can actually reach it. The supplied count is the finite
// state needed for curry adapters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ClosureAtom {
    Thunk(usize, usize),
    Named(Sym, usize),
    Resume(usize, Sym),
    Opaque,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ClosureShape(BTreeSet<ClosureAtom>);

impl ClosureShape {
    fn atom(atom: ClosureAtom) -> Self {
        Self(BTreeSet::from([atom]))
    }

    fn opaque() -> Self {
        Self::atom(ClosureAtom::Opaque)
    }

    fn carries(&self) -> bool {
        !self.0.is_empty()
    }

    fn merge(&mut self, other: &Self) -> bool {
        let before = self.0.len();
        self.0.extend(other.0.iter().copied());
        self.0.len() != before
    }
}

type ClosureLoc = BTreeMap<Sym, ClosureShape>;

// Site numbering for one stationary borrowed tree. A node's address is its
// identity only while that tree is borrowed, and the site *numbers* handed out
// come from structural traversal order, so no address can reach the fixpoint or
// any compiler output.
//
// The map is deliberately opaque: interning, lookup, and a count are the whole
// surface, and there is no way to iterate it. Iterating an address-keyed map is
// the one route by which address order could leak into a compiler whose
// contract is determinism, so the type makes that route unreachable rather than
// leaving it to a comment.
#[derive(Default)]
struct SiteIds(BTreeMap<*const TypedComp, usize>);

impl SiteIds {
    // The site number of `comp`, assigning the next one and reporting `true` if
    // this is its first sighting.
    fn intern(&mut self, comp: &TypedComp) -> (usize, bool) {
        let next = self.0.len();
        match self.0.entry(ptr::from_ref(comp)) {
            btree_map::Entry::Occupied(seen) => (*seen.get(), false),
            btree_map::Entry::Vacant(slot) => {
                slot.insert(next);
                (next, true)
            }
        }
    }

    fn get(&self, comp: &TypedComp) -> Option<usize> {
        self.0.get(&ptr::from_ref(comp)).copied()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

struct ClosureSites<'a> {
    thunk_ids: SiteIds,
    thunks: Vec<&'a TypedComp>,
    handle_ids: SiteIds,
    operation_arities: BTreeMap<Sym, usize>,
}

impl<'a> ClosureSites<'a> {
    fn new(functions: &'a [TypedCoreFn]) -> Self {
        let mut sites = Self {
            thunk_ids: SiteIds::default(),
            thunks: Vec::new(),
            handle_ids: SiteIds::default(),
            operation_arities: BTreeMap::new(),
        };
        for function in functions {
            sites.collect_comp(function.body());
        }
        sites
    }

    fn collect_comp(&mut self, comp: &'a TypedComp) {
        if let TypedCompKind::Do {
            operation, args, ..
        } = comp.kind()
        {
            self.operation_arities
                .entry(*operation)
                .and_modify(|arity| *arity = (*arity).max(args.len()))
                .or_insert(args.len());
        }
        if matches!(comp.kind(), TypedCompKind::Handle { .. }) {
            self.handle_ids.intern(comp);
            let TypedCompKind::Handle { ops, .. } = comp.kind() else {
                unreachable!();
            };
            for operation in ops.arms() {
                let arity = operation.params().len();
                self.operation_arities
                    .entry(operation.name())
                    .and_modify(|known| *known = (*known).max(arity))
                    .or_insert(arity);
            }
        }
        each_value(comp, &mut |value| self.collect_value(value));
        each_subcomp(comp, &mut |child| self.collect_comp(child));
    }

    fn collect_value(&mut self, value: &'a TypedValue) {
        match value.kind() {
            TypedValueKind::Thunk(body) => {
                // `thunks` is indexed by site number, so it grows in lockstep
                // with the numbering and the two stay the same length.
                if self.thunk_ids.intern(body).1 {
                    self.thunks.push(body);
                    self.collect_comp(body);
                }
            }
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::LoweredRepr { value: inner, .. }
            | TypedValueKind::NewtypeRepr { value: inner, .. } => self.collect_value(inner),
            TypedValueKind::Ctor { fields, .. }
            | TypedValueKind::Tuple(fields)
            | TypedValueKind::UnboxedTuple(fields) => {
                for field in fields {
                    self.collect_value(field);
                }
            }
            TypedValueKind::UnboxedRecord(fields) => {
                for (_, field) in fields {
                    self.collect_value(field);
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

    // `None` for a site the collecting traversal never reached. Collection and
    // the flow traversal walk the same tree, so a miss is not expected; the
    // callers still answer it with the opaque shape rather than a panic, because
    // this analysis chooses a lowering tier and the conservative shape only
    // costs speed, while an abort on a legal program costs the compile.
    fn thunk_id(&self, body: &TypedComp) -> Option<usize> {
        self.thunk_ids.get(body)
    }

    fn handle_id(&self, comp: &TypedComp) -> Option<usize> {
        self.handle_ids.get(comp)
    }
}

struct ClosureFlow<'a> {
    sites: ClosureSites<'a>,
    ret: BTreeMap<Sym, ClosureShape>,
    param: BTreeMap<Sym, Vec<ClosureShape>>,
    thunk_ret: Vec<ClosureShape>,
    thunk_param: Vec<Vec<ClosureShape>>,
    handle_ret: Vec<ClosureShape>,
    operation_ret: BTreeMap<Sym, ClosureShape>,
    operation_param: BTreeMap<Sym, Vec<ClosureShape>>,
}

struct ClosureUpdates {
    param: BTreeMap<Sym, Vec<ClosureShape>>,
    thunk_ret: Vec<ClosureShape>,
    thunk_param: Vec<Vec<ClosureShape>>,
    handle_ret: Vec<ClosureShape>,
    operation_ret: BTreeMap<Sym, ClosureShape>,
    operation_param: BTreeMap<Sym, Vec<ClosureShape>>,
}

impl ClosureUpdates {
    fn new(flow: &ClosureFlow<'_>) -> Self {
        Self {
            param: flow
                .param
                .iter()
                .map(|(name, slots)| (*name, vec![ClosureShape::default(); slots.len()]))
                .collect(),
            thunk_ret: vec![ClosureShape::default(); flow.thunk_ret.len()],
            thunk_param: flow
                .thunk_param
                .iter()
                .map(|slots| vec![ClosureShape::default(); slots.len()])
                .collect(),
            handle_ret: vec![ClosureShape::default(); flow.handle_ret.len()],
            operation_ret: flow
                .operation_ret
                .keys()
                .map(|operation| (*operation, ClosureShape::default()))
                .collect(),
            operation_param: flow
                .operation_param
                .iter()
                .map(|(operation, slots)| (*operation, vec![ClosureShape::default(); slots.len()]))
                .collect(),
        }
    }
}

fn closure_flow(functions: &[TypedCoreFn]) -> ClosureFlow<'_> {
    let sites = ClosureSites::new(functions);
    let thunk_param = sites
        .thunks
        .iter()
        .map(|body| match body.kind() {
            TypedCompKind::Lam(parameters, _) => {
                vec![ClosureShape::default(); parameters.len()]
            }
            _ => Vec::new(),
        })
        .collect();
    let mut flow = ClosureFlow {
        thunk_ret: vec![ClosureShape::default(); sites.thunks.len()],
        thunk_param,
        handle_ret: vec![ClosureShape::default(); sites.handle_ids.len()],
        operation_ret: sites
            .operation_arities
            .keys()
            .map(|operation| (*operation, ClosureShape::default()))
            .collect(),
        operation_param: sites
            .operation_arities
            .iter()
            .map(|(operation, arity)| (*operation, vec![ClosureShape::default(); *arity]))
            .collect(),
        sites,
        ret: functions
            .iter()
            .map(|function| (function.name(), ClosureShape::default()))
            .collect(),
        param: functions
            .iter()
            .map(|function| {
                (
                    function.name(),
                    vec![ClosureShape::default(); function.params().len()],
                )
            })
            .collect(),
    };
    loop {
        let mut updates = ClosureUpdates::new(&flow);
        let mut returns = BTreeMap::new();
        for function in functions {
            let loc = function
                .params()
                .iter()
                .map(TypedBinder::name)
                .zip(flow.param[&function.name()].iter().cloned())
                .collect();
            returns.insert(
                function.name(),
                closure_props(function.body(), &loc, &flow, &mut updates, &mut |_, _| {}),
            );
        }
        let mut changed = false;
        for (slot, value) in flow.ret.values_mut().zip(returns.values()) {
            changed |= slot.merge(value);
        }
        for (slots, values) in flow.param.values_mut().zip(updates.param.values()) {
            for (slot, value) in slots.iter_mut().zip(values) {
                changed |= slot.merge(value);
            }
        }
        for (slots, values) in flow.thunk_param.iter_mut().zip(&updates.thunk_param) {
            for (slot, value) in slots.iter_mut().zip(values) {
                changed |= slot.merge(value);
            }
        }
        for (slot, value) in flow.thunk_ret.iter_mut().zip(&updates.thunk_ret) {
            changed |= slot.merge(value);
        }
        for (slot, value) in flow.handle_ret.iter_mut().zip(&updates.handle_ret) {
            changed |= slot.merge(value);
        }
        for (slot, value) in flow
            .operation_ret
            .values_mut()
            .zip(updates.operation_ret.values())
        {
            changed |= slot.merge(value);
        }
        for (slots, values) in flow
            .operation_param
            .values_mut()
            .zip(updates.operation_param.values())
        {
            for (slot, value) in slots.iter_mut().zip(values) {
                changed |= slot.merge(value);
            }
        }
        if !changed {
            return flow;
        }
    }
}

fn closure_thunk(
    id: usize,
    loc: &ClosureLoc,
    flow: &ClosureFlow<'_>,
    updates: &mut ClosureUpdates,
    on_call: &mut impl FnMut(Sym, &[ClosureShape]),
) {
    let body = flow.sites.thunks[id];
    let result = match body.kind() {
        TypedCompKind::Lam(parameters, body) => {
            let mut extended = loc.clone();
            for (parameter, shape) in parameters.iter().zip(&flow.thunk_param[id]) {
                extended.insert(parameter.name(), shape.clone());
            }
            closure_props(body, &extended, flow, updates, on_call)
        }
        _ => closure_props(body, loc, flow, updates, on_call),
    };
    updates.thunk_ret[id].merge(&result);
}

fn closure_value(
    value: &TypedValue,
    loc: &ClosureLoc,
    flow: &ClosureFlow<'_>,
    updates: &mut ClosureUpdates,
    on_call: &mut impl FnMut(Sym, &[ClosureShape]),
) -> ClosureShape {
    match value.kind() {
        TypedValueKind::Thunk(body) => {
            let Some(id) = flow.sites.thunk_id(body) else {
                return ClosureShape::opaque();
            };
            closure_thunk(id, loc, flow, updates, on_call);
            ClosureShape::atom(ClosureAtom::Thunk(id, 0))
        }
        TypedValueKind::Var { name, .. } => loc.get(name).cloned().unwrap_or_else(|| {
            if flow.ret.contains_key(name) {
                ClosureShape::atom(ClosureAtom::Named(*name, 0))
            } else {
                ClosureShape::default()
            }
        }),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            closure_value(inner, loc, flow, updates, on_call)
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            let mut result = ClosureShape::default();
            for field in fields {
                result.merge(&closure_value(field, loc, flow, updates, on_call));
            }
            result
        }
        TypedValueKind::UnboxedRecord(fields) => {
            let mut result = ClosureShape::default();
            for (_, field) in fields {
                result.merge(&closure_value(field, loc, flow, updates, on_call));
            }
            result
        }
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => ClosureShape::default(),
    }
}

fn merge_arguments(slots: &mut [ClosureShape], offset: usize, arguments: &[ClosureShape]) {
    for (slot, argument) in slots.iter_mut().skip(offset).zip(arguments) {
        slot.merge(argument);
    }
}

fn closure_apply(
    heads: &ClosureShape,
    arguments: &[ClosureShape],
    flow: &ClosureFlow<'_>,
    updates: &mut ClosureUpdates,
    on_call: &mut impl FnMut(Sym, &[ClosureShape]),
) -> ClosureShape {
    let mut result = ClosureShape::default();
    let mut work: Vec<(ClosureAtom, usize)> = heads.0.iter().map(|atom| (*atom, 0)).collect();
    let mut seen = BTreeSet::new();
    while let Some((atom, offset)) = work.pop() {
        if !seen.insert((atom, offset)) {
            continue;
        }
        match atom {
            ClosureAtom::Thunk(id, supplied) => {
                let TypedCompKind::Lam(parameters, _) = flow.sites.thunks[id].kind() else {
                    result.merge(&ClosureShape::opaque());
                    continue;
                };
                let needed = parameters.len().saturating_sub(supplied);
                let available = arguments.len().saturating_sub(offset);
                let taken = needed.min(available);
                merge_arguments(
                    &mut updates.thunk_param[id],
                    supplied,
                    &arguments[offset..offset + taken],
                );
                if taken < needed {
                    result.merge(&ClosureShape::atom(ClosureAtom::Thunk(
                        id,
                        supplied + taken,
                    )));
                } else if offset + taken == arguments.len() {
                    result.merge(&flow.thunk_ret[id]);
                } else {
                    for next in &flow.thunk_ret[id].0 {
                        work.push((*next, offset + taken));
                    }
                }
            }
            ClosureAtom::Named(name, supplied) => {
                let arity = flow.param.get(&name).map_or(0, Vec::len);
                let needed = arity.saturating_sub(supplied);
                let available = arguments.len().saturating_sub(offset);
                let taken = needed.min(available);
                if let Some(slots) = updates.param.get_mut(&name) {
                    merge_arguments(slots, supplied, &arguments[offset..offset + taken]);
                }
                on_call(name, &arguments[offset..offset + taken]);
                if taken < needed {
                    result.merge(&ClosureShape::atom(ClosureAtom::Named(
                        name,
                        supplied + taken,
                    )));
                } else if offset + taken == arguments.len() {
                    if let Some(returned) = flow.ret.get(&name) {
                        result.merge(returned);
                    }
                } else if let Some(returned) = flow.ret.get(&name) {
                    for next in &returned.0 {
                        work.push((*next, offset + taken));
                    }
                }
            }
            ClosureAtom::Resume(handle, operation) => {
                if offset == arguments.len() {
                    result.merge(&ClosureShape::atom(atom));
                } else if offset + 1 == arguments.len() {
                    updates
                        .operation_ret
                        .get_mut(&operation)
                        .expect("a handled operation has a result slot")
                        .merge(&arguments[offset]);
                    result.merge(&flow.handle_ret[handle]);
                } else {
                    updates
                        .operation_ret
                        .get_mut(&operation)
                        .expect("a handled operation has a result slot")
                        .merge(&arguments[offset]);
                    for next in &flow.handle_ret[handle].0 {
                        work.push((*next, offset + 1));
                    }
                }
            }
            ClosureAtom::Opaque => {
                result.merge(&ClosureShape::opaque());
            }
        }
    }
    result
}

fn closure_pattern(loc: &ClosureLoc, pattern: &TypedPattern, shape: &ClosureShape) -> ClosureLoc {
    let mut out = loc.clone();
    match pattern {
        TypedPattern::Wild => {}
        TypedPattern::Var(binder) => {
            out.insert(binder.name(), shape.clone());
        }
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            for binder in fields.iter().flatten() {
                out.insert(binder.name(), shape.clone());
            }
        }
    }
    out
}

fn closure_props(
    comp: &TypedComp,
    loc: &ClosureLoc,
    flow: &ClosureFlow<'_>,
    updates: &mut ClosureUpdates,
    on_call: &mut impl FnMut(Sym, &[ClosureShape]),
) -> ClosureShape {
    match comp.kind() {
        TypedCompKind::Return(value) => closure_value(value, loc, flow, updates, on_call),
        TypedCompKind::Call { callee, args, .. } => {
            let shapes: Vec<ClosureShape> = args
                .iter()
                .map(|argument| closure_value(argument, loc, flow, updates, on_call))
                .collect();
            on_call(*callee, &shapes);
            if let Some(slots) = updates.param.get_mut(callee) {
                merge_arguments(slots, 0, &shapes);
            }
            let arity = flow.param.get(callee).map_or(0, Vec::len);
            match shapes.len().cmp(&arity) {
                Ordering::Less => ClosureShape::atom(ClosureAtom::Named(*callee, shapes.len())),
                Ordering::Equal => flow.ret.get(callee).cloned().unwrap_or_default(),
                Ordering::Greater => ClosureShape::opaque(),
            }
        }
        TypedCompKind::Bind(head, binder, tail) => {
            let shape = closure_props(head, loc, flow, updates, on_call);
            let mut extended = loc.clone();
            extended.insert(binder.name(), shape);
            closure_props(tail, &extended, flow, updates, on_call)
        }
        TypedCompKind::If(condition, yes, no) => {
            closure_value(condition, loc, flow, updates, on_call);
            let mut result = closure_props(yes, loc, flow, updates, on_call);
            result.merge(&closure_props(no, loc, flow, updates, on_call));
            result
        }
        TypedCompKind::Case(scrutinee, arms) => {
            let shape = closure_value(scrutinee, loc, flow, updates, on_call);
            let mut result = ClosureShape::default();
            for (pattern, body) in arms {
                result.merge(&closure_props(
                    body,
                    &closure_pattern(loc, pattern, &shape),
                    flow,
                    updates,
                    on_call,
                ));
            }
            result
        }
        TypedCompKind::Lam(parameters, body) => {
            let mut extended = loc.clone();
            for parameter in parameters {
                extended.insert(parameter.name(), ClosureShape::opaque());
            }
            closure_props(body, &extended, flow, updates, on_call);
            ClosureShape::default()
        }
        TypedCompKind::App { callee, args, .. } => {
            let heads = if let TypedCompKind::Force(value) = callee.kind() {
                closure_value(value, loc, flow, updates, on_call)
            } else {
                closure_props(callee, loc, flow, updates, on_call);
                ClosureShape::opaque()
            };
            let shapes: Vec<ClosureShape> = args
                .iter()
                .map(|argument| closure_value(argument, loc, flow, updates, on_call))
                .collect();
            closure_apply(&heads, &shapes, flow, updates, on_call)
        }
        TypedCompKind::Force(value) => {
            let heads = closure_value(value, loc, flow, updates, on_call);
            let mut result = ClosureShape::default();
            for atom in heads.0 {
                match atom {
                    ClosureAtom::Thunk(id, 0)
                        if !matches!(flow.sites.thunks[id].kind(), TypedCompKind::Lam(..)) =>
                    {
                        result.merge(&flow.thunk_ret[id]);
                    }
                    ClosureAtom::Opaque => {
                        result.merge(&ClosureShape::opaque());
                    }
                    ClosureAtom::Thunk(..) | ClosureAtom::Named(..) | ClosureAtom::Resume(..) => {}
                }
            }
            result
        }
        TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
            closure_props(body, loc, flow, updates, on_call)
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            let id = flow.sites.handle_id(comp);
            let body_shape = closure_props(body, loc, flow, updates, on_call);
            let mut result = return_body.as_ref().map_or_else(
                || body_shape.clone(),
                |return_body| {
                    let mut extended = loc.clone();
                    if let Some(return_binder) = return_binder {
                        extended.insert(return_binder.name(), body_shape.clone());
                    }
                    closure_props(return_body, &extended, flow, updates, on_call)
                },
            );
            for operation in ops.arms() {
                let mut extended = loc.clone();
                for (parameter, shape) in operation
                    .params()
                    .iter()
                    .zip(&flow.operation_param[&operation.name()])
                {
                    extended.insert(parameter.name(), shape.clone());
                }
                // Without a site number there is no answer slot to resume into,
                // so the continuation is an unknown closure.
                extended.insert(
                    operation.resume().name(),
                    id.map_or_else(ClosureShape::opaque, |id| {
                        ClosureShape::atom(ClosureAtom::Resume(id, operation.name()))
                    }),
                );
                result.merge(&closure_props(
                    operation.body(),
                    &extended,
                    flow,
                    updates,
                    on_call,
                ));
            }
            if let Some(id) = id {
                updates.handle_ret[id].merge(&result);
            }
            result
        }
        TypedCompKind::Do {
            operation, args, ..
        } => {
            let shapes: Vec<ClosureShape> = args
                .iter()
                .map(|argument| closure_value(argument, loc, flow, updates, on_call))
                .collect();
            merge_arguments(
                updates
                    .operation_param
                    .get_mut(operation)
                    .expect("an operation call has parameter slots"),
                0,
                &shapes,
            );
            flow.operation_ret[operation].clone()
        }
        _ => {
            each_value(comp, &mut |value| {
                closure_value(value, loc, flow, updates, on_call);
            });
            ClosureShape::default()
        }
    }
}

fn closure_crosses_boundary(
    functions: &[TypedCoreFn],
    region: &BTreeSet<Sym>,
    flow: &ClosureFlow<'_>,
) -> bool {
    let mut updates = ClosureUpdates::new(flow);
    for function in functions {
        let loc = function
            .params()
            .iter()
            .map(TypedBinder::name)
            .zip(flow.param[&function.name()].iter().cloned())
            .collect();
        let inside = region.contains(&function.name());
        let mut crosses = false;
        closure_props(
            function.body(),
            &loc,
            flow,
            &mut updates,
            &mut |callee, arguments| {
                if inside != region.contains(&callee) && arguments.iter().any(ClosureShape::carries)
                {
                    crosses = true;
                }
            },
        );
        if crosses {
            return true;
        }
    }
    false
}

fn applies_parameter(comp: &TypedComp, parameters: &BTreeSet<Sym>) -> bool {
    match comp.kind() {
        TypedCompKind::App { callee, .. } => {
            matches!(
                callee.kind(),
                TypedCompKind::Force(TypedValue {
                    kind: TypedValueKind::Var { name, .. },
                    ..
                }) if parameters.contains(name)
            ) || applies_parameter(callee, parameters)
        }
        TypedCompKind::Bind(head, binder, tail) => {
            if applies_parameter(head, parameters) {
                return true;
            }
            if let TypedCompKind::Return(TypedValue {
                kind: TypedValueKind::Var { name, .. },
                ..
            }) = head.kind()
            {
                if parameters.contains(name) {
                    let mut extended = parameters.clone();
                    extended.insert(binder.name());
                    return applies_parameter(tail, &extended);
                }
            }
            applies_parameter(tail, parameters)
        }
        TypedCompKind::If(_, yes, no) => {
            applies_parameter(yes, parameters) || applies_parameter(no, parameters)
        }
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .any(|(_, body)| applies_parameter(body, parameters)),
        TypedCompKind::Lam(_, body) | TypedCompKind::Mask(_, body) => {
            applies_parameter(body, parameters)
        }
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            applies_parameter(body, parameters)
                || return_body
                    .as_ref()
                    .is_some_and(|body| applies_parameter(body, parameters))
                || ops
                    .arms()
                    .iter()
                    .any(|operation| applies_parameter(operation.body(), parameters))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::core::typed::{
        CompSig, CoreFnSig, CoreType, TypedComp, TypedCompKind, TypedCoreFn, TypedValue,
        TypedValueKind,
    };
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::super::fixtures;
    use super::*;

    fn function(body: &TypedComp) -> TypedCoreFn {
        let signature = CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone());
        TypedCoreFn::new(
            Sym::from(ENTRY_POINT),
            Vec::new(),
            body.clone(),
            signature,
            0,
        )
    }

    fn planned(functions: &[TypedCoreFn]) -> MonadicRegionPlan {
        plan(functions, &EffectPlan::analyze(functions), false)
    }

    #[test]
    fn direct_effects_are_selective() {
        let operation = Sym::from("Ask.ask");
        let body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let functions = vec![function(&body)];
        let actual = planned(&functions);
        assert_eq!(actual.members, BTreeSet::from([Sym::from(ENTRY_POINT)]));
        assert_eq!(actual.scope, MonadicScope::Selective);
        assert_eq!(actual.entries, BTreeSet::from([Sym::from(ENTRY_POINT)]));
    }

    #[test]
    fn an_effect_inside_an_escaping_thunk_forces_whole_program_scope() {
        let operation = Sym::from("Ask.ask");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let thunk_ty = CoreType::Thunk(Box::new(performed.sig().clone()));
        let body = TypedComp::new(
            CompSig::new(thunk_ty.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                thunk_ty,
                TypedValueKind::Thunk(Box::new(performed)),
            )),
        );
        let functions = vec![function(&body)];
        let actual = planned(&functions);
        assert_eq!(actual.members, BTreeSet::from([Sym::from(ENTRY_POINT)]));
        // The thunk escapes: nothing downstream can say where it is forced, so
        // the signatures cannot describe what forcing it performs. That is the
        // fact that still widens the region. A capture the signatures *can*
        // describe no longer does, which is what
        // `a_trackable_capturer_keeps_the_region_confined` pins.
        assert_eq!(actual.scope, MonadicScope::WholeProgram);
    }

    #[test]
    fn a_trackable_capturer_keeps_the_region_confined() {
        let functions = fixtures::capturing_program();
        let effects = EffectPlan::analyze(&functions);
        let actual = plan(&functions, &effects, false);

        assert_eq!(
            effects.tracked_captures(),
            &BTreeSet::from([Sym::from(ENTRY_POINT)]),
            "the entry point is the capturer"
        );
        assert!(
            !effects.opaque_thunks(),
            "the thunk travels as a named-call argument, so the flow analysis \
             tracks it: the capture alone is what used to widen the region"
        );
        assert_eq!(actual.scope, MonadicScope::Selective);
        assert_eq!(
            actual.members,
            BTreeSet::from([Sym::from(fixtures::BUMP), Sym::from(fixtures::RUN)]),
            "the performer and the forwarder that forces its thunk"
        );
        assert!(
            !actual.members.contains(&Sym::from(ENTRY_POINT)),
            "the capturer stays direct: its handler bounds the region"
        );
        assert_eq!(
            actual.monadic_params.get(&Sym::from(fixtures::RUN)),
            Some(&BTreeSet::from([0usize])),
            "slot 0 of the forwarder receives a thunk that performs an operation"
        );
        assert!(
            actual.entries.is_empty(),
            "no member is called from direct code"
        );
    }

    #[test]
    fn a_forcer_under_its_own_handler_joins_the_region_and_reads_open() {
        let functions = fixtures::island_program();
        let effects = EffectPlan::analyze(&functions);
        let actual = plan(&functions, &effects, false);
        let forwarder = Sym::from(fixtures::RUN);

        assert_eq!(actual.scope, MonadicScope::Selective);
        assert_eq!(
            actual.monadic_params.get(&forwarder),
            Some(&BTreeSet::from([0usize])),
            "the slot is driven at the monadic convention wherever the force sits"
        );
        assert!(
            actual.members.contains(&forwarder),
            "owning a monadic slot is enough: the caller builds that argument \
             off the same flow fact, so the forwarder cannot answer at the \
             direct convention even though its force is buried in a handler"
        );

        let island = functions
            .iter()
            .find(|function| function.name() == forwarder)
            .expect("the forwarder is in the program");
        let scope = flow::param_loc(island, effects.flow());
        assert!(
            actual.handler_is_open(island.body(), Effects::of(&effects), &scope),
            "the operation the forced computation performs leaves this handler, \
             which discharges an unrelated one: reading it as closed would \
             compile a dispatch table with no case for it"
        );
    }

    #[test]
    fn a_handler_whose_action_is_handed_to_a_callee_reads_open() {
        let functions = fixtures::handed_off_program();
        let effects = EffectPlan::analyze(&functions);
        let actual = plan(&functions, &effects, false);
        let helper = functions
            .iter()
            .find(|function| function.name() == Sym::from(fixtures::HELPER))
            .expect("the intermediate is in the program");
        let scope = flow::param_loc(helper, effects.flow());

        assert_eq!(actual.scope, MonadicScope::Selective);
        assert!(
            actual.handler_is_open(helper.body(), Effects::of(&effects), &scope),
            "the operation arrives at this handler's driver from the forwarder's \
             force, so a dispatch table built from this handler's own arms would \
             have no case for it"
        );
    }

    #[test]
    fn a_caller_of_a_forcer_joins_the_confined_region() {
        let functions = fixtures::forwarded_program();
        let effects = EffectPlan::analyze(&functions);
        let actual = plan(&functions, &effects, false);

        assert_eq!(actual.scope, MonadicScope::Selective);
        assert!(
            actual.members.contains(&Sym::from(fixtures::HELPER)),
            "the intermediate performs nothing itself, and joins only because it \
             calls the forwarder from direct code, where the forwarder now \
             answers with an effect cell"
        );
        assert_eq!(
            actual.members,
            BTreeSet::from([
                Sym::from(fixtures::BUMP),
                Sym::from(fixtures::RUN),
                Sym::from(fixtures::HELPER),
            ]),
        );
        assert!(
            !actual.members.contains(&Sym::from(ENTRY_POINT)),
            "the closure stops at the handler, which is monadic wherever it sits"
        );
    }
}

fn resume_tail_only(operations: &[TypedHandleOp]) -> bool {
    operations.iter().all(|operation| {
        clause_resume_tail(
            operation.body(),
            &BTreeSet::from([operation.resume().name()]),
            true,
        )
    })
}

fn clause_resume_tail(comp: &TypedComp, aliases: &BTreeSet<Sym>, tail: bool) -> bool {
    match comp.kind() {
        TypedCompKind::App { callee, args, .. }
            if matches!(
                callee.kind(),
                TypedCompKind::Force(TypedValue {
                    kind: TypedValueKind::Var { name, instantiation },
                    ..
                }) if instantiation.is_empty() && aliases.contains(name)
            ) =>
        {
            tail && args
                .iter()
                .all(|argument| free_value_vars(argument).is_disjoint(aliases))
        }
        TypedCompKind::Bind(head, binder, body) => {
            let routing = matches!(
                head.kind(),
                TypedCompKind::Return(TypedValue {
                    kind: TypedValueKind::Var { name, instantiation },
                    ..
                }) if instantiation.is_empty() && aliases.contains(name)
            );
            let mut extended = aliases.clone();
            if routing {
                extended.insert(binder.name());
            }
            (routing || clause_resume_tail(head, aliases, false))
                && clause_resume_tail(body, &extended, tail)
        }
        TypedCompKind::If(condition, yes, no) => {
            free_value_vars(condition).is_disjoint(aliases)
                && clause_resume_tail(yes, aliases, tail)
                && clause_resume_tail(no, aliases, tail)
        }
        TypedCompKind::Case(scrutinee, arms) => {
            free_value_vars(scrutinee).is_disjoint(aliases)
                && arms
                    .iter()
                    .all(|(_, body)| clause_resume_tail(body, aliases, tail))
        }
        _ => free_comp_vars(comp).is_disjoint(aliases),
    }
}

#[cfg(test)]
mod judgment_tests {
    use crate::core::typed::{
        CompSig, CoreFnSig, CoreType, TypedComp, TypedCompKind, TypedCoreFn, TypedValueKind,
    };
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::super::fixtures;
    use super::*;

    fn function(body: &TypedComp) -> TypedCoreFn {
        let signature = CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone());
        TypedCoreFn::new(
            Sym::from(ENTRY_POINT),
            Vec::new(),
            body.clone(),
            signature,
            0,
        )
    }

    fn planned(functions: &[TypedCoreFn]) -> (EffectPlan, MonadicRegionPlan) {
        let effects = EffectPlan::analyze(functions);
        let plan = plan(functions, &effects, false);
        (effects, plan)
    }

    fn performed(operation: Sym) -> TypedComp {
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        )
    }

    #[test]
    fn selective_and_whole_scope_are_classified_explicitly() {
        let operation = Sym::from("Ask.ask");
        let direct = vec![function(&performed(operation))];
        let (_, direct_plan) = planned(&direct);
        let main = Sym::from(ENTRY_POINT);
        assert_eq!(direct_plan.scope, MonadicScope::Selective);
        assert_eq!(direct_plan.members, BTreeSet::from([main]));
        assert_eq!(direct_plan.genuine_effects, BTreeSet::from([main]));
        assert_eq!(direct_plan.entries, BTreeSet::from([main]));

        let thunk_body = performed(operation);
        let thunk_ty = CoreType::Thunk(Box::new(thunk_body.sig().clone()));
        let escaped = TypedComp::new(
            CompSig::new(thunk_ty.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                thunk_ty,
                TypedValueKind::Thunk(Box::new(thunk_body)),
            )),
        );
        let whole = vec![function(&escaped)];
        let (_, whole_plan) = planned(&whole);
        // The thunk escapes by being returned to a caller the
        // program does not name, so no signature describes what forcing it
        // performs and the region cannot reach through it. This is the
        // classification the confinement flip deliberately left alone.
        assert_eq!(whole_plan.scope, MonadicScope::WholeProgram);
        assert_eq!(whole_plan.members, BTreeSet::from([main]));
        assert_eq!(whole_plan.entries, BTreeSet::from([main]));
    }

    fn handled(escaping: bool) -> TypedComp {
        fixtures::handling_ask(performed(Sym::from(fixtures::ASK_OP)), escaping)
    }

    #[test]
    fn one_plan_owns_openness_and_native_eligibility() {
        let closed = handled(false);
        let closed_functions = vec![function(&closed)];
        let (closed_effects, closed_plan) = planned(&closed_functions);
        let closed_effects = Effects::of(&closed_effects);
        let scope = flow::Loc::new();
        assert_eq!(closed_plan.scope, MonadicScope::Selective);
        assert!(!closed_plan.handler_is_open(&closed, closed_effects, &scope));
        assert!(closed_plan.native_eligible(&closed, closed_effects, &scope, true));
        assert!(!closed_plan.native_eligible(&closed, closed_effects, &scope, false));

        let open = handled(true);
        let open_functions = vec![function(&open)];
        let (open_effects, open_plan) = planned(&open_functions);
        let open_effects = Effects::of(&open_effects);
        assert!(open_plan.handler_is_open(&open, open_effects, &scope));
        assert!(!open_plan.native_eligible(&open, open_effects, &scope, true));
    }
}
