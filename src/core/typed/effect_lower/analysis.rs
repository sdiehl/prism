//! Typed monadic calling-convention planning.
//!
//! This module decides which declarations share the free-monad convention
//! before any computation is rewritten. The plan is declaration-owned: later
//! handler, native-region, and `LocalPartial` builders consume it rather than
//! re-inferring openness or scope from partially lowered trees.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::ptr;

use crate::names::ENTRY_POINT;
use crate::sym::Sym;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::{
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue,
    TypedValueKind,
};
use super::flow::{self, ThunkFlow};
use super::latent::{self, Latent};
use super::walk::{each_subcomp, each_subterm, each_value, thunks_in_comp};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum MonadicScope {
    Selective,
    WholeProgram,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct MonadicRegionPlan {
    pub(super) members: BTreeSet<Sym>,
    pub(super) entries: BTreeSet<Sym>,
    pub(super) genuine_effects: BTreeSet<Sym>,
    pub(super) scope: MonadicScope,
}

impl MonadicRegionPlan {
    pub(super) fn handler_is_open(&self, comp: &TypedComp, latent: &Latent) -> bool {
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
        latent::handle_escapes(body, return_body.as_deref(), ops, latent, &mut escaping);
        !escaping.is_empty()
    }

    pub(super) fn native_closed(
        &self,
        comp: &TypedComp,
        latent: &Latent,
        native_enabled: bool,
    ) -> bool {
        if !native_enabled || self.handler_is_open(comp, latent) {
            return false;
        }
        let TypedCompKind::Handle { ops, .. } = comp.kind() else {
            return false;
        };
        !ops.arms().is_empty()
    }

    pub(super) fn native_eligible(
        &self,
        comp: &TypedComp,
        latent: &Latent,
        native_enabled: bool,
    ) -> bool {
        if !self.native_closed(comp, latent, native_enabled) {
            return false;
        }
        let TypedCompKind::Handle { ops, .. } = comp.kind() else {
            return false;
        };
        resume_tail_only(ops.arms())
    }
}

pub(super) fn plan(
    functions: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
) -> MonadicRegionPlan {
    let genuine_effects: BTreeSet<Sym> = latent
        .iter()
        .filter_map(|(name, operations)| (!operations.is_empty()).then_some(*name))
        .collect();
    let mut escaping = flow::escaping_fns(functions, latent, flow);
    escaping.extend(
        functions
            .iter()
            .filter(|function| open_resume_escapes(function.body(), latent))
            .map(TypedCoreFn::name),
    );
    let whole = !escaping.is_empty()
        || functions.iter().any(|function| {
            let mut thunks = Vec::new();
            thunks_in_comp(function.body(), &mut thunks);
            thunks
                .iter()
                .any(|body| calls_any(body, &genuine_effects) || raw_effects(body))
        });
    let members = if whole {
        functions.iter().map(TypedCoreFn::name).collect()
    } else {
        genuine_effects.clone()
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
        scope: if whole {
            MonadicScope::WholeProgram
        } else {
            MonadicScope::Selective
        },
    }
}

/// The clean whole-style component for `LocalPartial`, and the declarations the
/// fused rest calls across its bare-returning boundary.
pub(super) fn local_region(
    functions: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
) -> Option<(BTreeSet<Sym>, BTreeSet<Sym>)> {
    let closure_flow = closure_flow(functions);
    let mut escaping = flow::escaping_fns(functions, latent, flow);
    escaping.extend(
        functions
            .iter()
            .filter(|function| open_resume_escapes(function.body(), latent))
            .map(TypedCoreFn::name),
    );
    if escaping.is_empty() {
        return None;
    }

    let by_name: BTreeMap<Sym, &TypedCoreFn> = functions.iter().map(|f| (f.name(), f)).collect();
    let footprint: BTreeMap<Sym, BTreeSet<Sym>> = functions
        .iter()
        .map(|function| {
            let mut operations = BTreeSet::new();
            super::walk::collect_ops(function.body(), &mut operations);
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

fn collect_calls(comp: &TypedComp, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = comp.kind() {
        out.insert(*callee);
    }
    each_subterm(comp, &mut |child| collect_calls(child, out));
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

struct ClosureSites<'a> {
    // Pointers are lookup keys only while the borrowed tree is stationary. Site
    // numbers come from structural traversal order, so addresses cannot affect
    // the fixpoint or any compiler output.
    thunk_ids: BTreeMap<*const TypedComp, usize>,
    thunks: Vec<&'a TypedComp>,
    handle_ids: BTreeMap<*const TypedComp, usize>,
    operation_arities: BTreeMap<Sym, usize>,
}

impl<'a> ClosureSites<'a> {
    fn new(functions: &'a [TypedCoreFn]) -> Self {
        let mut sites = Self {
            thunk_ids: BTreeMap::new(),
            thunks: Vec::new(),
            handle_ids: BTreeMap::new(),
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
            let key = ptr::from_ref(comp);
            let next = self.handle_ids.len();
            self.handle_ids.entry(key).or_insert(next);
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
                let key = ptr::from_ref(body.as_ref());
                if !self.thunk_ids.contains_key(&key) {
                    let id = self.thunks.len();
                    self.thunk_ids.insert(key, id);
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

    fn thunk_id(&self, body: &TypedComp) -> usize {
        self.thunk_ids[&ptr::from_ref(body)]
    }

    fn handle_id(&self, comp: &TypedComp) -> usize {
        self.handle_ids[&ptr::from_ref(comp)]
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
            let id = flow.sites.thunk_id(body);
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
                extended.insert(
                    operation.resume().name(),
                    ClosureShape::atom(ClosureAtom::Resume(id, operation.name())),
                );
                result.merge(&closure_props(
                    operation.body(),
                    &extended,
                    flow,
                    updates,
                    on_call,
                ));
            }
            updates.handle_ret[id].merge(&result);
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

fn calls_any(comp: &TypedComp, names: &BTreeSet<Sym>) -> bool {
    let mut found =
        matches!(comp.kind(), TypedCompKind::Call { callee, .. } if names.contains(callee));
    each_subterm(comp, &mut |child| found |= calls_any(child, names));
    found
}

fn raw_effects(comp: &TypedComp) -> bool {
    if matches!(
        comp.kind(),
        TypedCompKind::Do { .. } | TypedCompKind::Handle { .. } | TypedCompKind::Mask(..)
    ) {
        return true;
    }
    let mut found = false;
    each_value(comp, &mut |value| found |= raw_effects_value(value));
    super::walk::each_subcomp(comp, &mut |child| found |= raw_effects(child));
    found
}

fn raw_effects_value(value: &TypedValue) -> bool {
    match &value.kind {
        TypedValueKind::Thunk(comp) => raw_effects(comp),
        TypedValueKind::Reinterpret(value)
        | TypedValueKind::LoweredRepr { value, .. }
        | TypedValueKind::NewtypeRepr { value, .. } => raw_effects_value(value),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => fields.iter().any(raw_effects_value),
        TypedValueKind::UnboxedRecord(fields) => {
            fields.iter().any(|(_, field)| raw_effects_value(field))
        }
        _ => false,
    }
}

pub(super) fn open_resume_escapes(comp: &TypedComp, latent: &Latent) -> bool {
    if let TypedCompKind::Handle { body, ops, .. } = comp.kind() {
        // The warning measures escape from the handled action's residue alone,
        // not the clause/return contributions `handle_escapes` folds in for
        // planning.
        let mut escaping = BTreeSet::new();
        latent::body_escapes(body, ops, latent, &mut escaping);
        if !escaping.is_empty()
            && ops
                .clone()
                .erase()
                .iter_with_use()
                .any(|(_, usage)| usage.in_thunk)
        {
            return true;
        }
    }
    let mut found = false;
    super::walk::each_subcomp(comp, &mut |child| {
        found |= open_resume_escapes(child, latent);
    });
    found
}

#[cfg(test)]
mod tests {
    use crate::core::typed::{
        CompSig, CoreFnSig, CoreType, TypedComp, TypedCompKind, TypedCoreFn, TypedValue,
        TypedValueKind,
    };
    use crate::types::ty::EffRow;
    use crate::types::Type;

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
        let latent = latent::latent_map(functions);
        let flow = flow::analyze(functions, &latent);
        plan(functions, &latent, &flow)
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
        assert_eq!(actual.scope, MonadicScope::WholeProgram);
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
        CompSig, CoreFnSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
        TypedHandleOp, TypedHandler, TypedValue, TypedValueKind,
    };
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::*;

    fn value(name: Sym, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        )
    }

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

    fn planned(functions: &[TypedCoreFn]) -> (Latent, MonadicRegionPlan) {
        let latent = latent::latent_map(functions);
        let flow = flow::analyze(functions, &latent);
        let plan = plan(functions, &latent, &flow);
        (latent, plan)
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
        assert_eq!(whole_plan.scope, MonadicScope::WholeProgram);
        assert_eq!(whole_plan.members, BTreeSet::from([main]));
        assert_eq!(whole_plan.entries, BTreeSet::from([main]));
    }

    fn handled(escaping: bool) -> TypedComp {
        let operation = Sym::from("Ask.ask");
        let leak = Sym::from("Leak.leak");
        let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Int)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature.clone())),
                EffRow::Empty,
            ))),
        );
        let force = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ),
            TypedCompKind::Force(value(resume.name(), resume.ty().clone())),
        );
        let resumed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![value(parameter.name(), parameter.ty().clone())],
            },
        );
        let clause_body = if escaping {
            let leaked = TypedComp::new(
                CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
                TypedCompKind::Do {
                    operation: leak,
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            );
            TypedComp::new(
                CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Leak")),
                TypedCompKind::Bind(
                    Box::new(leaked),
                    TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
                    Box::new(resumed),
                ),
            )
        } else {
            resumed
        };
        let handler = TypedHandler::new(vec![TypedHandleOp::new(
            operation,
            Vec::new(),
            vec![parameter],
            resume,
            clause_body,
        )])
        .expect("one unique clause");
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed(operation)),
                return_binder: None,
                return_body: None,
                ops: handler,
            },
        )
    }

    #[test]
    fn one_plan_owns_openness_and_native_eligibility() {
        let closed = handled(false);
        let closed_functions = vec![function(&closed)];
        let (closed_latent, closed_plan) = planned(&closed_functions);
        assert_eq!(closed_plan.scope, MonadicScope::Selective);
        assert!(!closed_plan.handler_is_open(&closed, &closed_latent));
        assert!(closed_plan.native_eligible(&closed, &closed_latent, true));
        assert!(!closed_plan.native_eligible(&closed, &closed_latent, false));

        let open = handled(true);
        let open_functions = vec![function(&open)];
        let (open_latent, open_plan) = planned(&open_functions);
        assert!(open_plan.handler_is_open(&open, &open_latent));
        assert!(!open_plan.native_eligible(&open, &open_latent, true));
    }
}
