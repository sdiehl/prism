//! Exact-size destination allocation for growable builder chains.
//!
//! The stdlib materializes a list into an array by pushing one element at a
//! time onto a growable destination. When the element count is already proven
//! exact at a call site (a literal, or an integer parameter the summary
//! domain tracked through the chain), that shape pays for amortized growth it
//! never needs: the destination could be allocated once at its final size and
//! filled by index.
//!
//! This pass recognizes the builder chain structurally, synthesizes sized
//! clones that allocate the destination once, and redirects only the call
//! sites whose count is proven. The originals remain for every unproven site,
//! so the rewrite is a pure cost decision: both paths produce the same array,
//! in the same order, with the same effects (none; every recognized function
//! must be pure), and neither tier can observe which fired.
//!
//! Recognition fails closed. Clone synthesis mints fresh bodies, so any
//! computation the recognizer cannot account for (an effect, an unknown call,
//! even a pure primitive in a bind head) would be silently dropped by the
//! clone; the walkers therefore decline the whole chain on the first
//! construct outside their inventory, and every decline keeps the growable
//! fallback.
//!
//! The chain has three recognized shapes:
//! - a *growable* builder `g(dst, xs)`: a case on `xs` that returns `dst` on
//!   the empty spine and otherwise pushes the head onto `dst` and recurses on
//!   the tail;
//! - a *seed* wrapper: one list parameter, tail-calling a growable with a
//!   fresh empty destination and its own list;
//! - a *forward* wrapper: one list parameter, delegating the whole list to a
//!   seed or forward wrapper and returning that result unchanged.
//!
//! A proven site `w(xs)` with count `n` becomes `w$xs1(n, xs)`, where the
//! sized clones thread `n` down to the growable's replacement: an entry that
//! allocates `array_new(n, head)` and a fill loop that writes the remaining
//! elements by index. A wrong exact count would change which array both
//! tiers agree on, so the count fact must stay a theorem of the summary
//! domain, never a heuristic.

use std::collections::BTreeMap;

use prism_common::sym::Sym;
use prism_syntax::names;

use crate::core::builtins::Builtin;
use crate::core::CoreOp;
use crate::types::ty::EffRow;
use crate::types::Type;

use super::facts::peel;
use super::specialize_support::{binder_occurrence, next_fresh, Rewrite};
use super::summary::{local_counts, summarize, CardExpr, Cardinality};
use super::{
    on_core_stack, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder,
    TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
    UncheckedTypedCore,
};

/// The index the entry clone hands the fill loop after writing the head
/// element into slot zero via the sized allocation itself.
const FIRST_FILL_INDEX: i64 = 1;
const GROWABLE_PARAM_COUNT: usize = 2;
const LAST_GROWABLE_PARAM: usize = GROWABLE_PARAM_COUNT - 1;
const WRAPPER_PARAM_COUNT: usize = 1;
const EMPTY_PATTERN_FIELDS: usize = 0;
const CONS_PATTERN_FIELDS: usize = 2;
const ENTRY_CLONE_ORDINAL: usize = 1;
const FILL_CLONE_ORDINAL: usize = 2;

/// What the pass did, for `dump`-level accounting.
#[derive(Clone, Copy, Debug, Default)]
pub struct ExactSizeStats {
    ticks: u64,
}

impl ExactSizeStats {
    /// Call sites redirected to a sized clone.
    #[must_use]
    pub const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Redirect proven-count builder call sites to sized clones.
#[must_use]
pub fn exact_size<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, ExactSizeStats) {
    on_core_stack(|| exact_size_on_core_stack(core))
}

fn exact_size_on_core_stack<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, ExactSizeStats) {
    let functions = core.into_unchecked().into_functions();
    let (functions, ticks) = run(functions);
    (UncheckedTypedCore::new(functions), ExactSizeStats { ticks })
}

fn run(functions: Vec<TypedCoreFn>) -> (Vec<TypedCoreFn>, u64) {
    let builders = classify_builders(&functions);
    if builders.is_empty() {
        return (functions, 0);
    }
    let table = summarize(&functions);
    let by_name: BTreeMap<Sym, &TypedCoreFn> = functions
        .iter()
        .map(|function| (function.name, function))
        .collect();
    let mut cx = Cx {
        builders: &builders,
        fns: &by_name,
        sized: BTreeMap::new(),
        emitted: Vec::new(),
        fresh: 0,
        ticks: 0,
    };
    let mut rewritten = Vec::with_capacity(functions.len());
    for function in &functions {
        let counts = local_counts(function, &table);
        if counts.is_empty() {
            rewritten.push(function.clone());
            continue;
        }
        let mut sites = Sites {
            cx: &mut cx,
            counts: &counts,
            params: &function.params,
        };
        rewritten.push(sites.function(function, &()));
    }
    let ticks = cx.ticks;
    rewritten.append(&mut cx.emitted);
    (rewritten, ticks)
}

// --- recognition -----------------------------------------------------------

/// What a recognized binder provably names inside a builder body. The walker
/// that maintains these is strict: a bind head it cannot express as an atom
/// declines the whole recognition.
#[derive(Clone, Debug, PartialEq, Eq)]
enum BuildAtom {
    /// The function's own parameter at this slot.
    Param(usize),
    /// A field bound by the recognized cons pattern.
    Field(Sym),
    /// The first atom's array with the second atom pushed onto it.
    Pushed(Box<Self>, Box<Self>),
    /// A fresh empty destination.
    Empty,
    /// The result of a forward wrapper's one delegated call.
    Result,
}

/// The strict walker's state: proven atoms per binder, plus the harvested
/// witness of every push (its checked signature and instantiation), which
/// clone synthesis reuses verbatim for the sized allocation builtins.
#[derive(Default)]
struct AtomEnv {
    atoms: BTreeMap<Sym, BuildAtom>,
    pushes: Vec<(CompSig, Vec<CoreInstantiation>)>,
}

impl AtomEnv {
    fn of_params(params: &[TypedBinder]) -> Self {
        let mut env = Self::default();
        for (slot, binder) in params.iter().enumerate() {
            env.atoms.insert(binder.name, BuildAtom::Param(slot));
        }
        env
    }
}

fn atom_of_value(value: &TypedValue, env: &AtomEnv) -> Option<BuildAtom> {
    match &peel(value).kind {
        TypedValueKind::Var { name, .. } => env.atoms.get(name).cloned(),
        _ => None,
    }
}

/// Record what one bind head proves about its binder, declining on any head
/// outside the inventory (see the module doc for why this must fail closed).
fn learn_atom(binder: Sym, head: &TypedComp, env: &mut AtomEnv) -> Option<()> {
    match &head.kind {
        TypedCompKind::Bind(inner, inner_binder, rest) => {
            learn_atom(inner_binder.name, inner, env)?;
            learn_atom(binder, rest, env)
        }
        TypedCompKind::Return(value) => {
            let atom = atom_of_value(value, env)?;
            env.atoms.insert(binder, atom);
            Some(())
        }
        TypedCompKind::StrBuiltin {
            op: Builtin::ArrayPush,
            instantiation,
            args,
        } => {
            let [dst, item] = args.as_slice() else {
                return None;
            };
            let dst = atom_of_value(dst, env)?;
            let item = atom_of_value(item, env)?;
            env.pushes.push((head.sig.clone(), instantiation.clone()));
            env.atoms
                .insert(binder, BuildAtom::Pushed(Box::new(dst), Box::new(item)));
            Some(())
        }
        TypedCompKind::StrBuiltin {
            op: Builtin::ArrayEmpty,
            args,
            ..
        } if args.is_empty() => {
            env.atoms.insert(binder, BuildAtom::Empty);
            Some(())
        }
        _ => None,
    }
}

/// Strip a body's bind chain down to its tail, learning every binder on the
/// way; `None` when any head is outside the strict inventory.
fn strip<'c>(comp: &'c TypedComp, env: &mut AtomEnv) -> Option<&'c TypedComp> {
    match &comp.kind {
        TypedCompKind::Bind(head, binder, rest) => {
            learn_atom(binder.name, head, env)?;
            strip(rest, env)
        }
        _ => Some(comp),
    }
}

/// A recognized growable builder, with everything clone synthesis needs
/// harvested from the checked original so every synthesized witness is one
/// the verifier has already accepted in this quantifier context.
#[derive(Clone, Debug)]
struct Growable {
    dst_slot: usize,
    list_slot: usize,
    nil_pattern: TypedPattern,
    cons_pattern: TypedPattern,
    head: TypedBinder,
    tail: TypedBinder,
    push_sig: CompSig,
    push_instantiation: Vec<CoreInstantiation>,
    self_instantiation: Vec<CoreInstantiation>,
}

#[derive(Clone, Debug)]
enum BuilderKind {
    Growable(Box<Growable>),
    Seed { inner: Sym },
    Forward { inner: Sym },
}

/// Every recognized chain function, growables first, then wrappers to a
/// fixed point (a forward may delegate to another forward).
fn classify_builders(functions: &[TypedCoreFn]) -> BTreeMap<Sym, BuilderKind> {
    let mut builders = BTreeMap::new();
    for function in functions {
        if let Some(growable) = classify_growable(function) {
            builders.insert(function.name, BuilderKind::Growable(Box::new(growable)));
        }
    }
    if builders.is_empty() {
        return builders;
    }
    loop {
        let mut changed = false;
        for function in functions {
            if builders.contains_key(&function.name) {
                continue;
            }
            if let Some(inner) = classify_seed(function, &builders) {
                builders.insert(function.name, BuilderKind::Seed { inner });
                changed = true;
            } else if let Some(inner) = classify_forward(function, &builders) {
                builders.insert(function.name, BuilderKind::Forward { inner });
                changed = true;
            }
        }
        if !changed {
            return builders;
        }
    }
}

/// A candidate must be pure and dictionary-free so its clones preserve the
/// original body's effects.
const fn plain_pure(function: &TypedCoreFn, arity: usize) -> bool {
    function.dict_arity == 0
        && function.params.len() == arity
        && matches!(function.sig.body.effects(), EffRow::Empty)
}

/// The instantiation that maps every quantifier to itself. Requiring it of
/// the growable's self-call lets the clones reuse the declared signature as
/// the instantiated one without substituting anything.
fn is_identity_instantiation(
    quantifiers: &[CoreQuantifier],
    instantiation: &[CoreInstantiation],
) -> bool {
    quantifiers.len() == instantiation.len()
        && quantifiers
            .iter()
            .zip(instantiation)
            .all(|pair| match pair {
                (CoreQuantifier::Type(q), CoreInstantiation::Type(Type::Var(v)))
                | (CoreQuantifier::Row(q), CoreInstantiation::Row(EffRow::Var(v))) => q == v,
                _ => false,
            })
}

#[allow(clippy::too_many_lines)]
fn classify_growable(function: &TypedCoreFn) -> Option<Growable> {
    if !plain_pure(function, GROWABLE_PARAM_COUNT) {
        return None;
    }
    let mut env = AtomEnv::of_params(&function.params);
    let tail = strip(&function.body, &mut env)?;
    let TypedCompKind::Case(scrutinee, arms) = &tail.kind else {
        return None;
    };
    let BuildAtom::Param(list_slot) = atom_of_value(scrutinee, &env)? else {
        return None;
    };
    let dst_slot = LAST_GROWABLE_PARAM - list_slot;
    let [(first_pattern, first_body), (second_pattern, second_body)] = arms.as_slice() else {
        return None;
    };
    let arity = |pattern: &TypedPattern| match pattern {
        TypedPattern::Ctor { fields, .. } => Some(fields.len()),
        _ => None,
    };
    let (nil_pattern, nil_body, cons_pattern, cons_body) =
        match (arity(first_pattern)?, arity(second_pattern)?) {
            (EMPTY_PATTERN_FIELDS, CONS_PATTERN_FIELDS) => {
                (first_pattern, first_body, second_pattern, second_body)
            }
            (CONS_PATTERN_FIELDS, EMPTY_PATTERN_FIELDS) => {
                (second_pattern, second_body, first_pattern, first_body)
            }
            _ => return None,
        };

    // The empty spine must hand back the destination untouched.
    let mut nil_env = AtomEnv::of_params(&function.params);
    let nil_tail = strip(nil_body, &mut nil_env)?;
    let TypedCompKind::Return(returned) = &nil_tail.kind else {
        return None;
    };
    if atom_of_value(returned, &nil_env)? != BuildAtom::Param(dst_slot) {
        return None;
    }

    // The cons pattern binds a head and a tail; the tail is the one field
    // typed like the list parameter, and that identification must be
    // unambiguous or the recursion check below could pass on the wrong field.
    let TypedPattern::Ctor { fields, .. } = cons_pattern else {
        return None;
    };
    let bound: Vec<&TypedBinder> = fields.iter().flatten().collect();
    let [first_field, second_field] = bound.as_slice() else {
        return None;
    };
    let list_ty = &function.params[list_slot].ty;
    let (head, tail_binder) = match (&first_field.ty == list_ty, &second_field.ty == list_ty) {
        (false, true) => (*first_field, *second_field),
        (true, false) => (*second_field, *first_field),
        _ => return None,
    };

    let mut cons_env = AtomEnv::of_params(&function.params);
    cons_env
        .atoms
        .insert(head.name, BuildAtom::Field(head.name));
    cons_env
        .atoms
        .insert(tail_binder.name, BuildAtom::Field(tail_binder.name));
    let cons_tail = strip(cons_body, &mut cons_env)?;
    let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = &cons_tail.kind
    else {
        return None;
    };
    if *callee != function.name
        || args.len() != 2
        || !is_identity_instantiation(&function.sig.quantifiers, instantiation)
    {
        return None;
    }
    let expected_dst = BuildAtom::Pushed(
        Box::new(BuildAtom::Param(dst_slot)),
        Box::new(BuildAtom::Field(head.name)),
    );
    if atom_of_value(&args[dst_slot], &cons_env)? != expected_dst
        || atom_of_value(&args[list_slot], &cons_env)? != BuildAtom::Field(tail_binder.name)
    {
        return None;
    }
    // Several pushes may alias the same step; they must be interchangeable
    // witnesses or the harvested one might not describe the used one.
    let (push_sig, push_instantiation) = cons_env.pushes.first()?.clone();
    if !cons_env
        .pushes
        .iter()
        .all(|push| *push == (push_sig.clone(), push_instantiation.clone()))
    {
        return None;
    }
    Some(Growable {
        dst_slot,
        list_slot,
        nil_pattern: nil_pattern.clone(),
        cons_pattern: cons_pattern.clone(),
        head: head.clone(),
        tail: tail_binder.clone(),
        push_sig,
        push_instantiation,
        self_instantiation: instantiation.clone(),
    })
}

fn classify_seed(function: &TypedCoreFn, builders: &BTreeMap<Sym, BuilderKind>) -> Option<Sym> {
    if !plain_pure(function, WRAPPER_PARAM_COUNT) {
        return None;
    }
    let mut env = AtomEnv::of_params(&function.params);
    let tail = strip(&function.body, &mut env)?;
    let TypedCompKind::Call { callee, args, .. } = &tail.kind else {
        return None;
    };
    let Some(BuilderKind::Growable(growable)) = builders.get(callee) else {
        return None;
    };
    if args.len() != 2
        || atom_of_value(&args[growable.dst_slot], &env)? != BuildAtom::Empty
        || atom_of_value(&args[growable.list_slot], &env)? != BuildAtom::Param(0)
    {
        return None;
    }
    Some(*callee)
}

/// Whether a call delegates this wrapper's whole list to an already
/// classified wrapper. Arity one keeps "the same list, unchanged" checkable.
fn delegating_call(
    kind: &TypedCompKind,
    env: &AtomEnv,
    builders: &BTreeMap<Sym, BuilderKind>,
) -> Option<Sym> {
    let TypedCompKind::Call { callee, args, .. } = kind else {
        return None;
    };
    if !matches!(
        builders.get(callee),
        Some(BuilderKind::Seed { .. } | BuilderKind::Forward { .. })
    ) {
        return None;
    }
    let [list] = args.as_slice() else {
        return None;
    };
    (atom_of_value(list, env)? == BuildAtom::Param(0)).then_some(*callee)
}

/// The forward walker: the strict inventory plus exactly one delegated call,
/// whose binder becomes the [`BuildAtom::Result`] the tail must return.
fn forward_learn(
    binder: Sym,
    head: &TypedComp,
    env: &mut AtomEnv,
    inner: &mut Option<Sym>,
    builders: &BTreeMap<Sym, BuilderKind>,
) -> Option<()> {
    match &head.kind {
        TypedCompKind::Bind(nested, nested_binder, rest) => {
            forward_learn(nested_binder.name, nested, env, inner, builders)?;
            forward_learn(binder, rest, env, inner, builders)
        }
        TypedCompKind::Call { .. } => {
            if inner.is_some() {
                return None;
            }
            *inner = Some(delegating_call(&head.kind, env, builders)?);
            env.atoms.insert(binder, BuildAtom::Result);
            Some(())
        }
        _ => learn_atom(binder, head, env),
    }
}

fn classify_forward(function: &TypedCoreFn, builders: &BTreeMap<Sym, BuilderKind>) -> Option<Sym> {
    if !plain_pure(function, WRAPPER_PARAM_COUNT) {
        return None;
    }
    let mut env = AtomEnv::of_params(&function.params);
    let mut inner = None;
    let mut comp = &function.body;
    loop {
        match &comp.kind {
            TypedCompKind::Bind(head, binder, rest) => {
                forward_learn(binder.name, head, &mut env, &mut inner, builders)?;
                comp = rest;
            }
            TypedCompKind::Return(value) => {
                return (atom_of_value(value, &env)? == BuildAtom::Result)
                    .then_some(())
                    .and(inner);
            }
            TypedCompKind::Call { .. } => {
                return match inner {
                    Some(_) => None,
                    None => delegating_call(&comp.kind, &env, builders),
                };
            }
            _ => return None,
        }
    }
}

// --- clone synthesis -------------------------------------------------------

struct Cx<'a> {
    builders: &'a BTreeMap<Sym, BuilderKind>,
    fns: &'a BTreeMap<Sym, &'a TypedCoreFn>,
    /// Wrapper (or growable) to its sized clone's name, memoized so one
    /// clone serves every proven site.
    sized: BTreeMap<Sym, Sym>,
    emitted: Vec<TypedCoreFn>,
    fresh: u32,
    ticks: u64,
}

const fn int_type() -> CoreType {
    CoreType::Source(Type::Int)
}

const fn int_sig() -> CompSig {
    CompSig::new(int_type(), EffRow::Empty)
}

const fn int_value(count: i64) -> TypedValue {
    TypedValue::new(int_type(), TypedValueKind::Int(count))
}

/// Rebuild a recognized body with every call to `target` replaced. The
/// recognized shapes only nest computations through binds, so this walks
/// exactly the spine the recognizer walked.
fn redirect(
    comp: &TypedComp,
    target: Sym,
    rebuild: &impl Fn(&[CoreInstantiation], &[TypedValue]) -> (Sym, Vec<TypedValue>),
) -> TypedComp {
    let kind = match &comp.kind {
        TypedCompKind::Bind(head, binder, rest) => TypedCompKind::Bind(
            Box::new(redirect(head, target, rebuild)),
            binder.clone(),
            Box::new(redirect(rest, target, rebuild)),
        ),
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } if *callee == target => {
            let (callee, args) = rebuild(instantiation, args);
            TypedCompKind::Call {
                callee,
                instantiation: instantiation.clone(),
                args,
            }
        }
        other => other.clone(),
    };
    TypedComp::new(comp.sig.clone(), kind)
}

impl Cx<'_> {
    fn fresh_int_binder(&mut self) -> TypedBinder {
        TypedBinder::new(
            next_fresh(&mut self.fresh, names::FRESH_EXACT_SIZE),
            int_type(),
        )
    }

    /// The sized clone's name for one chain function, synthesizing it (and
    /// its dependencies down to the growable's entry and fill) on first use.
    fn ensure(&mut self, name: Sym) -> Sym {
        if let Some(&sized) = self.sized.get(&name) {
            return sized;
        }
        let sized = match &self.builders[&name] {
            BuilderKind::Growable(growable) => self.growable_clones(name, &growable.clone()),
            BuilderKind::Seed { inner } => self.seed_clone(name, *inner),
            BuilderKind::Forward { inner } => self.forward_clone(name, *inner),
        };
        self.sized.insert(name, sized);
        sized
    }

    /// The growable's replacement pair. The entry allocates the whole
    /// destination from the count and the witnessed head, which also writes
    /// slot zero; the fill loop overwrites the remaining slots by index. An
    /// empty list never reaches the sized allocation, so a zero count is the
    /// one case the entry answers with the same empty array the seed built.
    fn growable_clones(&mut self, name: Sym, growable: &Growable) -> Sym {
        let base = self.fns[&name];
        let entry_name = Sym::from(&names::exact_sized_clone(
            name.as_str(),
            ENTRY_CLONE_ORDINAL,
        ));
        let fill_name = Sym::from(&names::exact_sized_clone(name.as_str(), FILL_CLONE_ORDINAL));
        let dst_param = base.params[growable.dst_slot].clone();
        let list_param = base.params[growable.list_slot].clone();
        let body_sig = base.sig.body.clone();
        let dst_ty = growable.push_sig.result.clone();

        // fill(dst, i, xs): case xs of nil => dst | cons(h, t) =>
        //   let dst = array_set(dst, i, h) in fill(dst, i + 1, t)
        let index_param = self.fresh_int_binder();
        let written = TypedBinder::new(
            next_fresh(&mut self.fresh, names::FRESH_EXACT_SIZE),
            dst_ty.clone(),
        );
        let bumped = self.fresh_int_binder();
        let write = TypedComp::new(
            growable.push_sig.clone(),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArraySet,
                instantiation: growable.push_instantiation.clone(),
                args: vec![
                    binder_occurrence(&dst_param),
                    binder_occurrence(&index_param),
                    binder_occurrence(&growable.head),
                ],
            },
        );
        let bump = TypedComp::new(
            int_sig(),
            TypedCompKind::Prim(
                CoreOp::Add,
                binder_occurrence(&index_param),
                int_value(FIRST_FILL_INDEX),
            ),
        );
        let recurse = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Call {
                callee: fill_name,
                instantiation: growable.self_instantiation.clone(),
                args: vec![
                    binder_occurrence(&written),
                    binder_occurrence(&bumped),
                    binder_occurrence(&growable.tail),
                ],
            },
        );
        let fill_cons = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Bind(
                Box::new(write),
                written,
                Box::new(TypedComp::new(
                    body_sig.clone(),
                    TypedCompKind::Bind(Box::new(bump), bumped, Box::new(recurse)),
                )),
            ),
        );
        let fill_nil = TypedComp::new(
            CompSig::new(dst_param.ty.clone(), EffRow::Empty),
            TypedCompKind::Return(binder_occurrence(&dst_param)),
        );
        let fill_body = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Case(
                binder_occurrence(&list_param),
                vec![
                    (growable.nil_pattern.clone(), fill_nil),
                    (growable.cons_pattern.clone(), fill_cons),
                ],
            ),
        );
        let fill_sig = CoreFnSig::new(
            base.sig.quantifiers.clone(),
            vec![dst_param.ty.clone(), int_type(), list_param.ty.clone()],
            body_sig.clone(),
        );
        self.emitted.push(TypedCoreFn::new(
            fill_name,
            vec![dst_param, index_param, list_param.clone()],
            fill_body,
            fill_sig,
            0,
        ));

        // entry(n, xs): case xs of nil => array_empty() | cons(h, t) =>
        //   let dst = array_new(n, h) in fill(dst, 1, t)
        let count_param = self.fresh_int_binder();
        let allocated =
            TypedBinder::new(next_fresh(&mut self.fresh, names::FRESH_EXACT_SIZE), dst_ty);
        let allocate = TypedComp::new(
            growable.push_sig.clone(),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayNew,
                instantiation: growable.push_instantiation.clone(),
                args: vec![
                    binder_occurrence(&count_param),
                    binder_occurrence(&growable.head),
                ],
            },
        );
        let start_fill = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Call {
                callee: fill_name,
                instantiation: growable.self_instantiation.clone(),
                args: vec![
                    binder_occurrence(&allocated),
                    int_value(FIRST_FILL_INDEX),
                    binder_occurrence(&growable.tail),
                ],
            },
        );
        let entry_cons = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Bind(Box::new(allocate), allocated, Box::new(start_fill)),
        );
        let entry_nil = TypedComp::new(
            growable.push_sig.clone(),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayEmpty,
                instantiation: growable.push_instantiation.clone(),
                args: Vec::new(),
            },
        );
        let entry_body = TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Case(
                binder_occurrence(&list_param),
                vec![
                    (growable.nil_pattern.clone(), entry_nil),
                    (growable.cons_pattern.clone(), entry_cons),
                ],
            ),
        );
        let entry_sig = CoreFnSig::new(
            base.sig.quantifiers.clone(),
            vec![int_type(), list_param.ty.clone()],
            body_sig,
        );
        self.emitted.push(TypedCoreFn::new(
            entry_name,
            vec![count_param, list_param],
            entry_body,
            entry_sig,
            0,
        ));
        entry_name
    }

    /// The seed's clone drops the empty destination in favor of the sized
    /// entry; the dead `array_empty` bind stays behind for the simplifier.
    fn seed_clone(&mut self, name: Sym, inner: Sym) -> Sym {
        let sized_inner = self.ensure(inner);
        let BuilderKind::Growable(growable) = &self.builders[&inner] else {
            unreachable!("a seed's inner is a growable by classification");
        };
        let list_slot = growable.list_slot;
        self.wrapper_clone(name, inner, |count, _, args| {
            (sized_inner, vec![count, args[list_slot].clone()])
        })
    }

    fn forward_clone(&mut self, name: Sym, inner: Sym) -> Sym {
        let sized_inner = self.ensure(inner);
        self.wrapper_clone(name, inner, |count, _, args| {
            let mut sized_args = vec![count];
            sized_args.extend(args.iter().cloned());
            (sized_inner, sized_args)
        })
    }

    /// Copy a wrapper with its one recognized inner call redirected through
    /// `rebuild`, threading the new leading count parameter down.
    fn wrapper_clone(
        &mut self,
        name: Sym,
        inner: Sym,
        rebuild: impl Fn(TypedValue, &[CoreInstantiation], &[TypedValue]) -> (Sym, Vec<TypedValue>),
    ) -> Sym {
        let base = self.fns[&name];
        let clone_name = Sym::from(&names::exact_sized_clone(
            name.as_str(),
            ENTRY_CLONE_ORDINAL,
        ));
        let count_param = self.fresh_int_binder();
        let count = binder_occurrence(&count_param);
        let body = redirect(&base.body, inner, &|instantiation, args| {
            rebuild(count.clone(), instantiation, args)
        });
        let mut params = vec![count_param];
        params.extend(base.params.iter().cloned());
        let mut param_tys = vec![int_type()];
        param_tys.extend(base.sig.params.iter().cloned());
        let sig = CoreFnSig::new(
            base.sig.quantifiers.clone(),
            param_tys,
            base.sig.body.clone(),
        );
        self.emitted
            .push(TypedCoreFn::new(clone_name, params, body, sig, 0));
        clone_name
    }
}

// --- site rewriting --------------------------------------------------------

/// Rewrites the proven call sites of one function. Values are left alone
/// (a site inside a thunk is a conservative miss, never a wrong rewrite).
struct Sites<'a, 'b> {
    cx: &'b mut Cx<'a>,
    counts: &'b BTreeMap<Sym, Cardinality>,
    params: &'b [TypedBinder],
}

impl Sites<'_, '_> {
    /// The count argument for one proven site, when the proof is a form the
    /// clone can take at runtime: a literal, or an integer parameter of the
    /// calling function. Anything else declines the site.
    fn count_value(&self, list: Option<&TypedValue>) -> Option<TypedValue> {
        let name = match &peel(list?).kind {
            TypedValueKind::Var { name, .. } => *name,
            _ => return None,
        };
        let Cardinality::Exact(expr) = self.counts.get(&name)? else {
            return None;
        };
        match expr {
            CardExpr::Lit(count) => Some(int_value(*count)),
            CardExpr::Param(slot) => {
                let param = self.params.get(*slot)?;
                (param.ty == int_type()).then(|| binder_occurrence(param))
            }
            CardExpr::Span(..) | CardExpr::CardOf(_) => None,
        }
    }
}

impl Rewrite for Sites<'_, '_> {
    type Ctx = ();

    fn value(&mut self, value: &TypedValue, _cx: &Self::Ctx) -> TypedValue {
        value.clone()
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        if let TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } = &comp.kind
        {
            if matches!(
                self.cx.builders.get(callee),
                Some(BuilderKind::Seed { .. } | BuilderKind::Forward { .. })
            ) {
                if let Some(count) = self.count_value(args.first()) {
                    let sized = self.cx.ensure(*callee);
                    self.cx.ticks += 1;
                    let mut sized_args = vec![count];
                    sized_args.extend(args.iter().cloned());
                    return TypedComp::new(
                        comp.sig.clone(),
                        TypedCompKind::Call {
                            callee: sized,
                            instantiation: instantiation.clone(),
                            args: sized_args,
                        },
                    );
                }
            }
        }
        self.descend_comp(comp, cx)
    }
}

#[cfg(test)]
mod tests {
    use super::super::summary::tests::{
        bind, call, case_of, ctor_pat, function_with, int, listy, lit, lvar, range_fn, ret, sym,
        var,
    };
    use super::*;

    fn push(dst: &str, item: &str) -> TypedComp {
        TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayPush,
                instantiation: Vec::new(),
                args: vec![var(dst), var(item)],
            },
        )
    }

    fn empty() -> TypedComp {
        TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayEmpty,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        )
    }

    fn cons_pattern() -> TypedPattern {
        ctor_pat(
            "Cons",
            vec![
                Some(TypedBinder::new(sym("h"), int())),
                Some(TypedBinder::new(sym("t"), listy())),
            ],
        )
    }

    /// The `push_all` shape: `pa(arr, xs) = case xs of Nil => arr
    /// | Cons(h, t) => pa(push(arr, h), t)`, aliases and all.
    fn growable_fn() -> TypedCoreFn {
        let cons_body = bind(
            ret(var("arr")),
            "d",
            int(),
            bind(
                push("d", "h"),
                "p",
                int(),
                call("pa", vec![var("p"), lvar("t")]),
            ),
        );
        let body = case_of(
            lvar("xs"),
            vec![
                (ctor_pat("Nil", Vec::new()), ret(var("arr"))),
                (cons_pattern(), cons_body),
            ],
        );
        function_with("pa", vec![("arr", int()), ("xs", listy())], body)
    }

    /// The `array_of_list` shape: `s(xs) = pa(array_empty(), xs)`.
    fn seed_fn() -> TypedCoreFn {
        let body = bind(
            empty(),
            "e",
            int(),
            bind(
                ret(lvar("xs")),
                "x2",
                listy(),
                call("pa", vec![var("e"), lvar("x2")]),
            ),
        );
        function_with("s", vec![("xs", listy())], body)
    }

    /// The `fz_of_list` shape: `f(xs) = let r = s(xs) in r`.
    fn forward_fn() -> TypedCoreFn {
        let body = bind(call("s", vec![lvar("xs")]), "r", listy(), ret(lvar("r")));
        function_with("f", vec![("xs", listy())], body)
    }

    fn tail_of(comp: &TypedComp) -> &TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(_, _, rest) => tail_of(rest),
            _ => comp,
        }
    }

    #[test]
    fn the_chain_classifies_as_growable_seed_and_forward() {
        let functions = vec![growable_fn(), seed_fn(), forward_fn()];
        let builders = classify_builders(&functions);
        assert!(matches!(
            builders.get(&sym("pa")),
            Some(BuilderKind::Growable(growable))
                if growable.dst_slot == 0 && growable.list_slot == 1
        ));
        assert!(
            matches!(builders.get(&sym("s")), Some(BuilderKind::Seed { inner }) if *inner == sym("pa"))
        );
        assert!(
            matches!(builders.get(&sym("f")), Some(BuilderKind::Forward { inner }) if *inner == sym("s"))
        );
    }

    /// A builder that recurses without pushing can drop elements, so its
    /// count is not the input's; it must stay unclassified.
    #[test]
    fn a_dropping_builder_declines() {
        let cons_body = bind(
            ret(var("arr")),
            "d",
            int(),
            call("pa", vec![var("d"), lvar("t")]),
        );
        let body = case_of(
            lvar("xs"),
            vec![
                (ctor_pat("Nil", Vec::new()), ret(var("arr"))),
                (cons_pattern(), cons_body),
            ],
        );
        let dropping = function_with("pa", vec![("arr", int()), ("xs", listy())], body);
        assert!(classify_builders(&[dropping]).is_empty());
    }

    /// Any bind head outside the strict inventory declines, even a pure
    /// primitive: clone synthesis would silently drop it.
    #[test]
    fn an_unaccounted_bind_head_declines() {
        let cons_body = bind(
            TypedComp::new(
                CompSig::new(int(), EffRow::Empty),
                TypedCompKind::Prim(CoreOp::Add, var("h"), lit(1)),
            ),
            "z",
            int(),
            bind(
                push("arr", "h"),
                "p",
                int(),
                call("pa", vec![var("p"), lvar("t")]),
            ),
        );
        let body = case_of(
            lvar("xs"),
            vec![
                (ctor_pat("Nil", Vec::new()), ret(var("arr"))),
                (cons_pattern(), cons_body),
            ],
        );
        let touched = function_with("pa", vec![("arr", int()), ("xs", listy())], body);
        assert!(classify_builders(&[touched]).is_empty());
    }

    /// Two same-typed cons fields make head and tail ambiguous; the
    /// recursion check could pass on the wrong one, so classification must
    /// refuse to guess.
    #[test]
    fn ambiguous_cons_fields_decline() {
        let pattern = ctor_pat(
            "Cons",
            vec![
                Some(TypedBinder::new(sym("h"), listy())),
                Some(TypedBinder::new(sym("t"), listy())),
            ],
        );
        let cons_body = bind(
            push("arr", "h"),
            "p",
            int(),
            call("pa", vec![var("p"), lvar("t")]),
        );
        let body = case_of(
            lvar("xs"),
            vec![
                (ctor_pat("Nil", Vec::new()), ret(var("arr"))),
                (pattern, cons_body),
            ],
        );
        let ambiguous = function_with("pa", vec![("arr", int()), ("xs", listy())], body);
        assert!(classify_builders(&[ambiguous]).is_empty());
    }

    /// End to end over the whole chain: a literal-count site through the
    /// forward wrapper redirects to a sized clone family, and the clones
    /// carry the count down to a sized allocation plus an indexed fill.
    #[test]
    fn a_proven_site_redirects_through_sized_clones() {
        let main = function_with(
            "main0",
            Vec::new(),
            bind(
                call("rng", vec![lit(1), lit(20)]),
                "l",
                listy(),
                call("f", vec![lvar("l")]),
            ),
        );
        let functions = vec![range_fn(), growable_fn(), seed_fn(), forward_fn(), main];
        let (out, ticks) = run(functions);
        assert_eq!(ticks, 1);

        let by_name: BTreeMap<Sym, &TypedCoreFn> = out
            .iter()
            .map(|function| (function.name, function))
            .collect();
        for expected in ["f", "s", "pa", "f$xs1", "s$xs1", "pa$xs1", "pa$xs2"] {
            assert!(by_name.contains_key(&sym(expected)), "missing {expected}");
        }

        // The site: f(l) became f$xs1(19, l).
        let TypedCompKind::Call { callee, args, .. } = &tail_of(&by_name[&sym("main0")].body).kind
        else {
            panic!("main0 ends in a call");
        };
        assert_eq!(*callee, sym("f$xs1"));
        assert!(matches!(&args[0].kind, TypedValueKind::Int(19)));

        // The forward clone threads its count into the sized seed.
        let forward_clone = by_name[&sym("f$xs1")];
        assert_eq!(forward_clone.params.len(), 2);
        assert_eq!(forward_clone.params[0].ty, int_type());
        let TypedCompKind::Bind(head, ..) = &forward_clone.body.kind else {
            panic!("forward clone keeps its bind shape");
        };
        let TypedCompKind::Call { callee, args, .. } = &head.kind else {
            panic!("forward clone delegates in its bind head");
        };
        assert_eq!(*callee, sym("s$xs1"));
        assert_eq!(args.len(), 2);

        // The seed clone reaches the sized entry with count and list only.
        let TypedCompKind::Call { callee, args, .. } = &tail_of(&by_name[&sym("s$xs1")].body).kind
        else {
            panic!("seed clone ends in a call");
        };
        assert_eq!(*callee, sym("pa$xs1"));
        assert_eq!(args.len(), 2);

        // The entry allocates once from the count; the fill writes by index.
        let TypedCompKind::Case(_, arms) = &by_name[&sym("pa$xs1")].body.kind else {
            panic!("sized entry is a case on the list");
        };
        let allocated = arms.iter().any(|(_, body)| {
            matches!(
                &body.kind,
                TypedCompKind::Bind(head, ..)
                    if matches!(&head.kind, TypedCompKind::StrBuiltin { op: Builtin::ArrayNew, .. })
            )
        });
        assert!(allocated, "the entry's cons arm allocates the destination");
        let TypedCompKind::Case(_, arms) = &by_name[&sym("pa$xs2")].body.kind else {
            panic!("fill is a case on the list");
        };
        let writes = arms.iter().any(|(_, body)| {
            matches!(
                &body.kind,
                TypedCompKind::Bind(head, ..)
                    if matches!(&head.kind, TypedCompKind::StrBuiltin { op: Builtin::ArraySet, .. })
            )
        });
        assert!(writes, "the fill's cons arm writes by index");

        // The unproven originals are untouched.
        let TypedCompKind::Call { callee, .. } = &tail_of(&by_name[&sym("s")].body).kind else {
            panic!("original seed still calls the growable");
        };
        assert_eq!(*callee, sym("pa"));
    }

    /// No proven count anywhere: the pass is the identity.
    #[test]
    fn without_a_proven_count_nothing_changes() {
        let main = function_with("main0", vec![("xs", listy())], call("f", vec![lvar("xs")]));
        let functions = vec![growable_fn(), seed_fn(), forward_fn(), main];
        let (out, ticks) = run(functions.clone());
        assert_eq!(ticks, 0);
        assert_eq!(out.len(), functions.len());
    }
}
