//! Consumer/stream recognition and conservative purity analysis.

use super::{
    as_var, calls_in, copy_prop, is_unit, normalize, peel, subst, substitute_core_type,
    substitute_witnesses, unit_value, Arg, Arm, BTreeMap, BTreeSet, CompSig, CoreInstantiation,
    CoreType, Cx, EffRow, Role, StepCtors, StreamExpr, Sym, Type, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind, Visit,
};

// --- consumer recognition -------------------------------------------------------

/// A fold-shaped consumer resolved to its driving form: it forces its sequence
/// parameter, matches the two `Step` constructors, and tail-recurses on the
/// cons tail. Wrapper consumers (`sum = fold(s, 0, add)`) are peeled to the
/// underlying fold, carrying the wrapper's fixed arguments.
pub(super) struct Consumer {
    pub(super) ctors: StepCtors,
    /// The sequence argument at the seed call site (before let-resolution).
    pub(super) seq_arg: TypedValue,
    /// The accumulator arguments at the seed call site (non-sequence,
    /// non-closure state), paired with how each advances in the recursive call.
    pub(super) accs: Vec<Acc>,
    /// The closure arguments baked into the fold (mappers/fold-functions), by
    /// the fold's parameter name, substituted into every body.
    pub(super) baked: BTreeMap<Sym, TypedValue>,
    /// The empty-arm body (the fold's result when the sequence is exhausted),
    /// over the accumulator parameters.
    pub(super) done_body: TypedComp,
    /// The cons-arm body up to (not including) the self-call: the per-element
    /// action computing the next accumulators. Binds the element variable
    /// `elem`.
    pub(super) step_body: TypedComp,
    /// The element binder introduced by the cons pattern.
    pub(super) elem: Sym,
    /// The fold's own accumulator parameters, in order, with call-site
    /// instantiated types (they become the trailing join parameters).
    pub(super) acc_params: Vec<TypedBinder>,
    /// Every function name reachable in the consumer's driven region (for
    /// purity).
    pub(super) fn_names: Vec<Sym>,
    /// The fully instantiated seed call-site signature: the join function's
    /// declared body signature and the redirected call's witness.
    pub(super) call_sig: CompSig,
}

/// One accumulator: its seed value at the call site and its advance expression
/// (the corresponding self-call argument, over the parameters and the element).
pub(super) struct Acc {
    pub(super) seed: TypedValue,
    pub(super) advance: TypedValue,
}

impl Consumer {
    pub(super) fn pure(&self, cx: &mut Cx) -> bool {
        comp_pure(&self.done_body, cx)
            && comp_pure(&self.step_body, cx)
            && self.baked.values().all(|v| value_pure(v, cx))
            && self.fn_names.iter().all(|n| fn_pure(*n, cx))
    }
}

// Resolve the seed call head to a fold-shaped consumer, peeling wrapper
// functions (a body that is a single call to another consumer with the
// sequence threaded). The declared scheme is instantiated at the call site's
// explicit arguments before any analysis, so every extracted piece carries
// concrete witnesses; the term structure the legacy pass matches is untouched.
pub(super) fn resolve_consumer(
    f: Sym,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
    call_sig: &CompSig,
    cx: &mut Cx,
) -> Option<Consumer> {
    let def = cx.fns.get(&f)?.clone();
    if def.params.len() != args.len() {
        return None;
    }
    let quantifiers = def.sig.quantifiers().to_vec();
    let inst_body = substitute_witnesses(&def.body, &quantifiers, instantiation);
    let inst_params: Vec<TypedBinder> = def
        .params
        .iter()
        .map(|binder| {
            TypedBinder::new(
                binder.name(),
                substitute_core_type(binder.ty(), &quantifiers, instantiation),
            )
        })
        .collect();
    // A direct fold analyses the raw body (parameters intact, so its forcing
    // site names a parameter). A wrapper (`sum = fold(s, 0, add)`) needs the
    // arguments substituted to expose its single delegate call.
    if let Some(consumer) = fold_consumer(f, &inst_params, args, &inst_body, call_sig, cx) {
        return Some(consumer);
    }
    let sub: BTreeMap<Sym, TypedValue> = inst_params
        .iter()
        .map(TypedBinder::name)
        .zip(args.iter().cloned())
        .collect();
    let body = normalize(&subst(&inst_body, &sub, cx), cx)?;
    if let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = body.kind()
    {
        if *callee != f {
            return resolve_consumer(*callee, instantiation, args, call_sig, cx);
        }
    }
    None
}

// Match the canonical fold shape on the (copy-propagated) raw body and extract
// its driving pieces, filling accumulator seeds from the seed call `args`.
// Returns `None` if the body is not a fold over one of its parameters.
fn fold_consumer(
    f: Sym,
    params: &[TypedBinder],
    args: &[TypedValue],
    raw_body: &TypedComp,
    call_sig: &CompSig,
    cx: &mut Cx,
) -> Option<Consumer> {
    // Copy-propagate the elaboration's `return x to t` aliases so the forcing
    // site, match, and self-call read structurally, then expect
    // `Bind(force(seq)(()), st, Case st arms)`.
    let body = copy_prop(raw_body, cx);
    let (seq, _st, arms) = match_force_case(&body)?;
    // `seq` must be one of the fold's own parameters (the sequence being
    // folded).
    let seq_idx = params.iter().position(|p| p.name() == seq)?;
    let (ctors, done_body, elem, tail, step_body) = match_step_arms(arms)?;
    // The self-call in the cons arm: `Call(f, [tail, adv...])`, tail in the seq
    // slot.
    let (callee, cargs) = tail_self_call(&step_body, f)?;
    if callee != f || cargs.len() != params.len() {
        return None;
    }
    if as_var(&cargs[seq_idx]) != Some(tail) {
        return None;
    }
    // Partition the non-sequence parameters into accumulators (advancing) and
    // baked closures (invariant). A parameter whose self-call argument is
    // itself and whose seed argument is a thunk is baked; otherwise it is an
    // accumulator.
    let mut accs = Vec::new();
    let mut baked = BTreeMap::new();
    let mut acc_params = Vec::new();
    for (i, p) in params.iter().enumerate() {
        if i == seq_idx {
            continue;
        }
        let advance = cargs[i].clone();
        let invariant = as_var(&advance) == Some(p.name());
        if invariant && matches!(&peel(&args[i]).kind, TypedValueKind::Thunk(_)) {
            baked.insert(p.name(), args[i].clone());
        } else {
            accs.push(Acc {
                seed: args[i].clone(),
                advance,
            });
            acc_params.push(p.clone());
        }
    }
    let mut fn_names = calls_in(&done_body);
    fn_names.extend(calls_in(&step_body));
    fn_names.retain(|n| *n != f);
    Some(Consumer {
        ctors,
        seq_arg: args[seq_idx].clone(),
        accs,
        baked,
        done_body,
        step_body: strip_self_call(&step_body, f),
        elem,
        acc_params,
        fn_names,
        call_sig: call_sig.clone(),
    })
}

// Match `Bind(App(Force(Var seq), [Unit]), st, Case(Var st, arms))`.
fn match_force_case(body: &TypedComp) -> Option<(Sym, Sym, &[Arm])> {
    if let TypedCompKind::Bind(first, st, rest) = body.kind() {
        if let TypedCompKind::App {
            callee,
            instantiation: _,
            args,
        } = first.kind()
        {
            if let TypedCompKind::Force(head) = callee.kind() {
                if let Some(seq) = as_var(head) {
                    if args.len() == 1 && is_unit(&args[0]) {
                        if let TypedCompKind::Case(scrutinee, arms) = rest.kind() {
                            if as_var(scrutinee) == Some(st.name()) {
                                return Some((seq, st.name(), arms));
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

// Split the two-arm `Step` match into (ctors, done-body, elem, tail,
// cons-body).
fn match_step_arms(arms: &[Arm]) -> Option<(StepCtors, TypedComp, Sym, Sym, TypedComp)> {
    if arms.len() != 2 {
        return None;
    }
    let mut done: Option<(Sym, TypedComp)> = None;
    let mut more: Option<(Sym, Sym, Sym, TypedComp)> = None;
    for (pattern, body) in arms {
        match pattern {
            TypedPattern::Ctor { name, fields, .. } if fields.is_empty() => {
                done = Some((*name, body.clone()));
            }
            TypedPattern::Ctor { name, fields, .. } if fields.len() == 2 => {
                let head = fields[0].as_ref()?;
                let next = fields[1].as_ref()?;
                more = Some((*name, head.name(), next.name(), body.clone()));
            }
            _ => return None,
        }
    }
    let (dc, db) = done?;
    let (mc, elem, tail, mb) = more?;
    Some((StepCtors { done: dc, more: mc }, db, elem, tail, mb))
}

// The tail self-call reachable through the cons-arm's straight-line binds (the
// recursion is the last computation).
fn tail_self_call(body: &TypedComp, f: Sym) -> Option<(Sym, Vec<TypedValue>)> {
    match body.kind() {
        TypedCompKind::Call { callee, args, .. } if *callee == f => Some((*callee, args.clone())),
        TypedCompKind::Bind(_, _, rest) => tail_self_call(rest, f),
        _ => None,
    }
}

// Replace the tail self-call with a `Return(Unit)` marker: the cons-arm body
// then holds exactly the per-element action as a straight-line prefix, which
// the residualizer re-emits before the recursive join call. The marker's sig is
// a placeholder; `graft_return` replaces the node wholesale before the body
// reaches output, restoring the enclosing binds' stored sigs.
fn strip_self_call(body: &TypedComp, f: Sym) -> TypedComp {
    match body.kind() {
        TypedCompKind::Call { callee, .. } if *callee == f => TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::Return(unit_value()),
        ),
        TypedCompKind::Bind(first, binder, rest) => TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Bind(
                first.clone(),
                binder.clone(),
                Box::new(strip_self_call(rest, f)),
            ),
        ),
        _ => body.clone(),
    }
}

// --- stream resolution ----------------------------------------------------------

// Resolve a sequence argument (a value, usually a `Var` bound upstream to a
// combinator call) into a pipeline tree. Producers bottom the recursion.
pub(super) fn resolve_stream(
    seq: &TypedValue,
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    let v = as_var(seq)?;
    let def = env.get(&v)?.clone();
    resolve_stream_comp(&def, env, cx)
}

// Resolve a stream-valued computation to a pipeline tree. Elaboration nests a
// whole pipeline as one `Bind`-chain leading to the outermost call, so
// copy-propagate to inline the value aliases, flatten the chain into the
// resolution environment, and resolve the trailing call.
fn resolve_stream_comp(
    def: &TypedComp,
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    let def = copy_prop(def, cx);
    let mut local = env.clone();
    let mut cur = &def;
    while let TypedCompKind::Bind(first, binder, rest) = cur.kind() {
        local.insert(binder.name(), first.as_ref().clone());
        cur = rest;
    }
    match cur.kind() {
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } => stream_of_call(*callee, instantiation, args, &local, cx),
        TypedCompKind::Return(value) if as_var(value).is_some() => {
            resolve_stream(value, &local, cx)
        }
        _ => None,
    }
}

// Chase let-aliases (`x = Return v`) to a ground value: a literal or a thunk. A
// producer bound or a mapper/predicate closure reaches its definition this way,
// so it is baked into the join as a value rather than a reference to a
// caller-local.
fn resolve_value(v: &TypedValue, env: &BTreeMap<Sym, TypedComp>) -> TypedValue {
    if let Some(x) = as_var(v) {
        if let Some(TypedCompKind::Return(inner)) = env.get(&x).map(TypedComp::kind) {
            return resolve_value(inner, env);
        }
    }
    v.clone()
}

fn stream_of_call(
    comb: Sym,
    instantiation: &[CoreInstantiation],
    cargs: &[TypedValue],
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    let stream_idx = match stream_role(comb, cx)? {
        Role::Producer => None,
        Role::Transformer(i) => Some(i),
    };
    let mut args = Vec::with_capacity(cargs.len());
    for (i, a) in cargs.iter().enumerate() {
        if Some(i) == stream_idx {
            args.push(Arg::Stream(Box::new(resolve_stream(a, env, cx)?)));
        } else {
            args.push(Arg::Val(resolve_value(a, env)));
        }
    }
    Some(StreamExpr {
        comb,
        instantiation: instantiation.to_vec(),
        args,
    })
}

// The role of combinator `comb`: a producer (forces no parameter) or a
// transformer (forces exactly one). `None` when `comb` is unknown or forces
// more than one parameter (a binary combinator like `zip`), which this cut does
// not fuse.
pub(super) fn stream_role(comb: Sym, cx: &mut Cx) -> Option<Role> {
    let (params, body_src) = {
        let def = cx.fns.get(&comb)?;
        (
            def.params.iter().map(TypedBinder::name).collect::<Vec<_>>(),
            def.body.clone(),
        )
    };
    // Copy-propagate first: elaboration forces an alias (`return s to t; force
    // t`), so the raw body never names the parameter at the forcing site.
    let body = copy_prop(&body_src, cx);
    let forced = forced_params(&body, &params);
    match forced.len() {
        0 => Some(Role::Producer),
        1 => Some(Role::Transformer(forced[0])),
        _ => None,
    }
}

// The parameter indices that appear as `force(param)(())` anywhere in `body`,
// in first-occurrence order.
pub(super) fn forced_params(body: &TypedComp, params: &[Sym]) -> Vec<usize> {
    let mut scan = ForcedParamScan {
        params,
        hits: Vec::new(),
    };
    scan.walk_comp(body);
    scan.hits
}

struct ForcedParamScan<'a> {
    params: &'a [Sym],
    hits: Vec<usize>,
}

impl Visit for ForcedParamScan<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        let TypedCompKind::App { callee, args, .. } = comp.kind() else {
            return true;
        };
        let TypedCompKind::Force(head) = callee.kind() else {
            return true;
        };
        if args.len() != 1 || !is_unit(&args[0]) {
            return true;
        }
        let Some(name) = as_var(head) else {
            return true;
        };
        let Some(index) = self.params.iter().position(|param| *param == name) else {
            return true;
        };
        if !self.hits.contains(&index) {
            self.hits.push(index);
        }
        true
    }
}

// --- purity ---------------------------------------------------------------------

// The row witness. A row carrying a concrete label proves the node it sits on
// can perform that operation, whatever the syntax underneath looks like; the
// checker has already paid for the fact, so no walk here may contradict it. An
// open tail (`Var`, `Exist`) is evidence in neither direction and decides
// nothing: a row-polymorphic combinator keeps whatever verdict its structure
// earns, and stays fusible at a pure instantiation.
fn row_effectful(row: &EffRow) -> bool {
    !row.labels().is_empty()
}

// The same witness for a value, which performs nothing by itself: what a fused
// loop can perform through it is what forcing and applying it yields. A thunk
// type carries the row of the computation it suspends, and a function type the
// row of its body, so `\() -> choose(2)` is `Thunk(pure -> Function(! choose))`
// and the operation is two levels in. This is the only purity evidence an
// opaque value offers, and reading it is what stops an effectful thunk arriving
// through a parameter, syntactically absent at every use site, from passing as
// pure.
fn ty_effectful(mut ty: &CoreType) -> bool {
    loop {
        ty = match ty {
            CoreType::Thunk(suspended) => {
                if row_effectful(suspended.effects()) {
                    return true;
                }
                suspended.result()
            }
            CoreType::Function(signature) => {
                if row_effectful(signature.body().effects()) {
                    return true;
                }
                signature.body().result()
            }
            // A source type, a cell, a reuse shell, and a lowered word are all inert
            // as values: whatever they contain becomes forcible only by being
            // projected out, and the projection is a node with its own row.
            CoreType::Source(_)
            | CoreType::Ref(_)
            | CoreType::ReuseToken(_)
            | CoreType::Lowered(_) => {
                return false;
            }
        };
    }
}

pub(super) fn stream_pure(s: &StreamExpr, cx: &mut Cx) -> bool {
    enum Item<'a> {
        Stream(&'a StreamExpr),
        Value(&'a TypedValue),
    }

    let mut work = vec![Item::Stream(s)];
    while let Some(item) = work.pop() {
        match item {
            Item::Stream(stream) => {
                if !fn_pure(stream.comb, cx) {
                    return false;
                }
                work.extend(stream.args.iter().rev().map(|arg| match arg {
                    Arg::Val(value) => Item::Value(value),
                    Arg::Stream(inner) => Item::Stream(inner),
                }));
            }
            Item::Value(value) => {
                if !value_pure(value, cx) {
                    return false;
                }
            }
        }
    }
    true
}

// A function is fusion-pure when no path through the call graph from its body
// reaches a direct effect node or an unknown call head. This is a reachability
// property, so an optimistic seed is not a sound recursion breaker: one member
// of a mutually recursive component can otherwise be finalized against a
// sibling's provisional `true` verdict. Condense the reachable graph into
// strongly connected components and commit one shared verdict only after the
// whole component has resolved.
pub(super) fn fn_pure(name: Sym, cx: &mut Cx) -> bool {
    if let Some(&p) = cx.pure.get(&name) {
        return p;
    }
    if !cx.fns.contains_key(&name) {
        // An unknown call head cannot be proven pure.
        cx.pure.insert(name, false);
        return false;
    }
    let mut walk = PurityWalk::default();
    walk.connect(name, cx);
    cx.pure.get(&name).copied().unwrap_or(false)
}

// One function body's local contribution to the call-graph fixpoint.
struct BodyInfo {
    self_bad: bool,
    callees: Vec<Sym>,
}

fn body_info(def: &TypedCoreFn, fns: &BTreeMap<Sym, TypedCoreFn>) -> BodyInfo {
    let mut info = BodyInfo {
        self_bad: comp_has_direct_effect(def.body()),
        callees: Vec::new(),
    };
    for callee in calls_in(def.body()) {
        if fns.contains_key(&callee) {
            if !info.callees.contains(&callee) {
                info.callees.push(callee);
            }
        } else {
            info.self_bad = true;
        }
    }
    info
}

// Direct effects include effects suspended inside values. Calls themselves are
// handled as graph edges by `body_info`, so recursion cannot influence this
// local predicate.
fn comp_has_direct_effect(c: &TypedComp) -> bool {
    let mut scan = DirectEffectScan::default();
    scan.walk_comp(c);
    scan.found
}

fn comp_directly_effectful(comp: &TypedComp) -> bool {
    row_effectful(comp.sig().effects())
        || matches!(
            comp.kind(),
            TypedCompKind::Io(..)
                | TypedCompKind::Do { .. }
                | TypedCompKind::Handle { .. }
                | TypedCompKind::Mask(..)
                | TypedCompKind::Error(_)
                | TypedCompKind::RefNew(_)
                | TypedCompKind::RefGet(_)
                | TypedCompKind::RefSet(..)
        )
}

#[derive(Default)]
struct DirectEffectScan {
    found: bool,
}

impl Visit for DirectEffectScan {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        if comp_directly_effectful(comp) {
            self.found = true;
        }
        !self.found
    }

    fn value(&mut self, value: &TypedValue) -> bool {
        if ty_effectful(value.ty()) {
            self.found = true;
        }
        !self.found
    }
}

// Scratch state for one Tarjan walk. Every discovered node is finalized into
// `cx.pure` before `fn_pure` returns; no provisional verdict escapes the walk.
#[derive(Default)]
struct PurityWalk {
    index: BTreeMap<Sym, u32>,
    low: BTreeMap<Sym, u32>,
    stack: Vec<Sym>,
    on_stack: BTreeSet<Sym>,
    info: BTreeMap<Sym, BodyInfo>,
    counter: u32,
}

impl PurityWalk {
    fn connect(&mut self, name: Sym, cx: &mut Cx) {
        self.discover(name, cx);
        let mut work = vec![ConnectFrame { name, next: 0 }];
        while !work.is_empty() {
            let (name, next) = {
                let frame = work.last_mut().expect("purity work stack is non-empty");
                let callee = self.info[&frame.name].callees.get(frame.next).copied();
                frame.next += usize::from(callee.is_some());
                (frame.name, callee)
            };
            if let Some(callee) = next {
                if cx.pure.contains_key(&callee) {
                    continue;
                }
                if self.on_stack.contains(&callee) {
                    self.low
                        .insert(name, self.low[&name].min(self.index[&callee]));
                } else {
                    self.discover(callee, cx);
                    work.push(ConnectFrame {
                        name: callee,
                        next: 0,
                    });
                }
                continue;
            }

            let finished = work.pop().expect("purity work stack is non-empty").name;
            self.finish_component(finished, cx);
            if let Some(parent) = work.last() {
                self.low
                    .insert(parent.name, self.low[&parent.name].min(self.low[&finished]));
            }
        }
    }

    fn discover(&mut self, name: Sym, cx: &Cx) {
        let info = cx.fns.get(&name).map_or(
            BodyInfo {
                self_bad: true,
                callees: Vec::new(),
            },
            |def| body_info(def, &cx.fns),
        );
        let index = self.counter;
        self.counter += 1;
        self.index.insert(name, index);
        self.low.insert(name, index);
        self.stack.push(name);
        self.on_stack.insert(name);
        self.info.insert(name, info);
    }

    fn finish_component(&mut self, name: Sym, cx: &mut Cx) {
        if self.low[&name] == self.index[&name] {
            let mut component = Vec::new();
            loop {
                let member = self.stack.pop().expect("purity walk stack underflow");
                self.on_stack.remove(&member);
                component.push(member);
                if member == name {
                    break;
                }
            }
            let members: BTreeSet<Sym> = component.iter().copied().collect();
            let pure = component.iter().all(|member| {
                let info = &self.info[member];
                !info.self_bad
                    && info.callees.iter().all(|callee| {
                        members.contains(callee) || cx.pure.get(callee) == Some(&true)
                    })
            });
            for member in component {
                cx.pure.insert(member, pure);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct ConnectFrame {
    name: Sym,
    next: usize,
}

pub(super) fn comp_pure(c: &TypedComp, cx: &mut Cx) -> bool {
    let mut scan = PurityScan { cx, pure: true };
    scan.walk_comp(c);
    scan.pure
}

// Every thunk anywhere inside `v` has a pure body (the deep descent the legacy
// visitor performs inside computations).
#[cfg(test)]
pub(super) fn value_thunks_pure(v: &TypedValue, cx: &mut Cx) -> bool {
    let mut scan = PurityScan { cx, pure: true };
    scan.walk_value(v);
    scan.pure
}

struct PurityScan<'a> {
    cx: &'a mut Cx,
    pure: bool,
}

impl Visit for PurityScan<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        if !self.pure {
            return false;
        }
        if comp_directly_effectful(comp) {
            self.pure = false;
            return false;
        }
        if let TypedCompKind::Call { callee, .. } = comp.kind() {
            self.pure = fn_pure(*callee, self.cx);
        }
        self.pure
    }

    fn value(&mut self, value: &TypedValue) -> bool {
        if self.pure && ty_effectful(value.ty()) {
            self.pure = false;
        }
        self.pure
    }
}

// The shallow value gate the legacy pass applies to baked closures and pipeline
// value arguments: a thunk's body must be pure; anything else passes its type
// witness or nothing.
pub(super) fn value_pure(v: &TypedValue, cx: &mut Cx) -> bool {
    let peeled = peel(v);
    if ty_effectful(peeled.ty()) {
        return false;
    }
    match &peeled.kind {
        TypedValueKind::Thunk(body) => comp_pure(body, cx),
        _ => true,
    }
}
