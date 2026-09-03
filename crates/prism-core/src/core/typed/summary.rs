//! Per-function summaries over verified typed Core.
//!
//! One bottom-up pass over the call graph produces, for every function, the
//! interprocedural facts the optimizer and its diagnostics would otherwise
//! rediscover locally: the shape of the result its tail produces, its checked
//! effect row, whether its body can allocate a heap cell, whether the closures
//! it builds capture mutable state, which of its parameters it may invoke as
//! callables, and how many elements a collection result provably holds.
//!
//! Summaries are cost facts. No consumer may change evaluation order, effects,
//! failure, or observable behavior on their strength; a fact that cannot be
//! proven is `Unknown` and every consumer must keep its conservative fallback.
//! The analysis is deterministic: iteration is over `BTreeMap`/`BTreeSet` and
//! strongly connected components are visited callee-first, so equal input
//! programs yield byte-equal summary tables.
//!
//! Recursive components get a bounded fixed point: every per-function fact
//! lives in a small finite lattice (a shape either stays, joins to `Unknown`,
//! or the allocation bound saturates), so recomputing members until a round
//! changes nothing terminates without a widening step.
//!
//! [`ResultShape`] deliberately does not extend the per-binding fact
//! environment's kinds: those facts describe one binding inside one body and
//! are killed by scope, while a result shape is a whole-function claim joined
//! across every completing path and remapped through call sites, including
//! recursive ones mid-fixpoint. The two meet only at `peel`, which both share.
//!
//! The callable-parameter set here is the summary-facing counterpart of the
//! specializer's force-and-apply analysis: both mean "this slot's callable may
//! run inside the callee". This one is computed together with the allocation
//! bound (a call forwarding a parameter into a callee's callable slot inherits
//! the requirement), and deliberately without the specializer's local alias
//! chasing; losing an alias only makes a claim more conservative.
//!
//! [`discharge`] resolves one such requirement at a higher-order call site
//! from the bound callable's own summary, without inlining either body. It is
//! how a consumer asks "does this callback keep the callee's conditional
//! allocation bound unconditional?"; the answer never rewrites anything.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use prism_common::fixpoint::stabilize;
use prism_common::scc::tarjan_scc;
use prism_common::sym::Sym;
use prism_syntax::names;

use super::effect_lower::walk::{each_subcomp, each_value, thunks_in_comp, top_thunks_in_value};
use super::facts::peel;
use super::inline::calls_in;
use crate::core::builtins::Builtin;
use crate::core::{CoreOp, IoOp};
use crate::types::ty::EffRow;

use super::{TypedComp, TypedCompKind, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind};

/// The proven shape of the value a function's tail produces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResultShape {
    /// A scalar literal on every path.
    Constant,
    /// The named parameter's value, unchanged.
    Param(usize),
    /// An application of the named constructor.
    Constructor(Sym),
    /// A tuple or unboxed product.
    Product,
    /// A function or thunk value.
    Closure,
    /// A primitive arithmetic result.
    Scalar,
    /// Nothing proven: joined branches disagree, or the tail is a construct
    /// the domain does not model.
    Unknown,
}

/// How much a function's own body may allocate, excluding what the callables
/// bound to its [`FunctionSummary::callbacks`] slots do when invoked.
///
/// Shaped as a bound rather than a boolean so a counted budget can extend it
/// without changing consumers that only compare against `Zero`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AllocBound {
    /// No path materializes a fresh heap cell. Mirrors the allocation
    /// checker's witness set: constructors, tuples, and thunks allocate;
    /// unboxed products, scalars, reuse-token spends, and the output/seed
    /// builtins do not; a performed arena `alloc` still counts.
    Zero,
    /// At least one path may allocate.
    Unbounded,
}

/// Whether the closures a function builds capture mutable state, in
/// increasing order of obstruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CaptureState {
    /// The body builds no closure at all.
    NoClosures,
    /// Every closure the body builds is free of mutable-state operations.
    Stateless,
    /// Some closure reads a mutable cell.
    ReadsMutable,
    /// Some closure writes a mutable cell.
    WritesMutable,
}

/// A compile-time size expression for a collection result.
///
/// `Span` and `CardOf` are produced only by the structural spine recognizers,
/// and a `Span` side is always a `Lit` or `Param` leaf: substitution folds a
/// fully literal span to a `Lit` and never nests spans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CardExpr {
    /// A literal element count.
    Lit(i64),
    /// The value of the named integer parameter.
    Param(usize),
    /// `max(hi - lo, 0)`: the count a counting builder produces stepping
    /// from `lo` (inclusive) to `hi` (exclusive). The clamp is part of the
    /// meaning, so an inverted span is zero elements, never a negative
    /// count.
    Span(Box<Self>, Box<Self>),
    /// The element count of the collection bound at the parameter slot.
    CardOf(usize),
}

/// How many elements a collection result provably holds. A cost fact only:
/// `Exact` licenses allocating the destination once, everything else keeps
/// the growable fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cardinality {
    /// Exactly this many elements on every completing path.
    Exact(CardExpr),
    /// At most this many elements.
    UpperBound(CardExpr),
    /// No proven count.
    Unknown,
}

/// One function's interprocedural fact record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummary {
    /// The proven tail result shape.
    pub result: ResultShape,
    /// The checked effect row from the function's signature.
    pub effects: EffRow,
    /// The body's own allocation bound, conditional on `callbacks`.
    pub allocation: AllocBound,
    /// Mutable-state capture of the closures the body builds.
    pub capture: CaptureState,
    /// Parameter slots whose callable may be invoked, directly or by being
    /// forwarded into another function's callable slot.
    pub callbacks: BTreeSet<usize>,
    /// The proven element count of a collection result.
    pub cardinality: Cardinality,
}

// --- canonical rendering and encoding --------------------------------------
//
// One home for the strings a summary prints as. The fact sheet, the encoded
// artifact, and any future consumer all render through these, so two surfaces
// can never spell the same fact differently.

impl ResultShape {
    /// The canonical rendering of a result-shape claim.
    #[must_use]
    pub fn render(&self) -> String {
        match self {
            Self::Constant => "constant".to_string(),
            Self::Param(slot) => format!("param {slot}"),
            Self::Constructor(name) => format!("constructor `{}`", name.as_str()),
            Self::Product => "product".to_string(),
            Self::Closure => "closure".to_string(),
            Self::Scalar => "scalar".to_string(),
            Self::Unknown => "unknown".to_string(),
        }
    }
}

impl AllocBound {
    /// The canonical rendering of an allocation bound.
    #[must_use]
    pub const fn render(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::Unbounded => "unbounded",
        }
    }
}

impl CaptureState {
    /// The canonical rendering of a capture classification.
    #[must_use]
    pub const fn render(self) -> &'static str {
        match self {
            Self::NoClosures => "no-closures",
            Self::Stateless => "stateless",
            Self::ReadsMutable => "reads-mutable",
            Self::WritesMutable => "writes-mutable",
        }
    }
}

impl CardExpr {
    /// The canonical rendering of a size expression.
    #[must_use]
    pub fn render(&self) -> String {
        match self {
            Self::Lit(count) => count.to_string(),
            Self::Param(slot) => format!("param {slot}"),
            Self::Span(lo, hi) => format!("{} - {}", hi.render(), lo.render()),
            Self::CardOf(slot) => format!("count of param {slot}"),
        }
    }
}

impl Cardinality {
    /// The canonical rendering of a cardinality claim.
    #[must_use]
    pub fn render(&self) -> String {
        match self {
            Self::Exact(expr) => format!("exact {}", expr.render()),
            Self::UpperBound(expr) => format!("at-most {}", expr.render()),
            Self::Unknown => "unknown".to_string(),
        }
    }
}

/// The version tag heading the canonical summary encoding.
///
/// A cache-bust counter, not a compat version: it joins the artifact's first
/// line and its query key, so a layout change misses every stale entry and no
/// old layout is ever read back.
pub const SUMMARY_ENCODING_SCHEMA: &str = "prism-function-summaries-v1";

/// The canonical byte encoding of a summary table: the schema line, then one
/// tab-separated row per function, each field rendered by the canonical
/// renderer above and the callback slots comma-joined.
///
/// Rows sort by name STRING, not by the map's own key order: symbol ordering depends on
/// interner history, which must never leak into a durable artifact. Equal
/// tables therefore encode to equal bytes, which is the whole contract a
/// store reconcile verifies; there is deliberately no decoder until a
/// cross-compile consumer exists to need one.
#[must_use]
pub fn encode_summaries(table: &BTreeMap<Sym, FunctionSummary>) -> Vec<u8> {
    let mut rows: Vec<(&str, &FunctionSummary)> = table
        .iter()
        .map(|(name, summary)| (name.as_str(), summary))
        .collect();
    rows.sort_unstable_by_key(|(name, _)| *name);
    let mut out = String::new();
    out.push_str(SUMMARY_ENCODING_SCHEMA);
    out.push('\n');
    for (name, summary) in rows {
        let callbacks = summary
            .callbacks
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",");
        // Writing to a String is infallible; the unit result carries no error.
        let _ = writeln!(
            out,
            "{name}\t{}\t{}\t{}\t{}\t{callbacks}\t{}",
            summary.result.render(),
            summary.effects.show(),
            summary.allocation.render(),
            summary.capture.render(),
            summary.cardinality.render(),
        );
    }
    out.into_bytes()
}

/// The resolution of one callback requirement at a higher-order call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Discharge {
    /// The callable's summary meets the requirement: it allocates nothing
    /// and imposes no requirement of its own. Binding it leaves the callee's
    /// allocation bound unconditional.
    Met,
    /// The callable's summary shows it may allocate on its own.
    Unmet,
    /// Nothing proven: a summary is missing, or the callable carries
    /// requirements of its own that this site has no arguments to meet.
    Unknown,
}

/// Resolve the callback requirement `callee` imposes on parameter `slot`
/// against the summary of the named callable bound there, without inlining
/// either body.
///
/// A slot the callee never invokes discharges trivially; use
/// [`crate::core::typed::specialize::callable_identity`] to name the
/// callable a call-site value carries.
///
/// A cost and diagnostic fact only: `Met` licenses treating the callee's
/// conditional allocation bound as unconditional at this site, everything
/// else keeps every conservative fallback.
#[must_use]
pub fn discharge(
    table: &BTreeMap<Sym, FunctionSummary>,
    callee: Sym,
    slot: usize,
    callable: Sym,
) -> Discharge {
    let Some(requirement) = table.get(&callee) else {
        return Discharge::Unknown;
    };
    if !requirement.callbacks.contains(&slot) {
        return Discharge::Met;
    }
    let Some(candidate) = table.get(&callable) else {
        return Discharge::Unknown;
    };
    match candidate.allocation {
        AllocBound::Unbounded => Discharge::Unmet,
        AllocBound::Zero if candidate.callbacks.is_empty() => Discharge::Met,
        AllocBound::Zero => Discharge::Unknown,
    }
}

/// The facts that flow through the recursive fixed point. `None` is the
/// bottom of the shape and cardinality lattices: no completing path observed
/// yet (or ever, for a function that always diverges).
#[derive(Clone, Debug, PartialEq)]
struct Flowing {
    result: Option<ResultShape>,
    allocation: AllocBound,
    callbacks: BTreeSet<usize>,
    cardinality: Option<Cardinality>,
}

impl Flowing {
    const fn bottom() -> Self {
        Self {
            result: None,
            allocation: AllocBound::Zero,
            callbacks: BTreeSet::new(),
            cardinality: None,
        }
    }
}

/// One callee's facts as seen from a call site: still iterating in the same
/// component, already summarized, or outside the table entirely.
enum Callee<'a> {
    InFlight(&'a Flowing),
    Done(&'a FunctionSummary),
    Unknown,
}

impl Callee<'_> {
    fn result(&self) -> Option<ResultShape> {
        match self {
            Self::InFlight(flowing) => flowing.result.clone(),
            Self::Done(summary) => Some(summary.result.clone()),
            Self::Unknown => Some(ResultShape::Unknown),
        }
    }

    fn cardinality(&self) -> Option<Cardinality> {
        match self {
            Self::InFlight(flowing) => flowing.cardinality.clone(),
            Self::Done(summary) => Some(summary.cardinality.clone()),
            Self::Unknown => Some(Cardinality::Unknown),
        }
    }

    const fn allocation(&self) -> (AllocBound, &BTreeSet<usize>) {
        const NO_SLOTS: &BTreeSet<usize> = &BTreeSet::new();
        match self {
            Self::InFlight(flowing) => (flowing.allocation, &flowing.callbacks),
            Self::Done(summary) => (summary.allocation, &summary.callbacks),
            Self::Unknown => (AllocBound::Unbounded, NO_SLOTS),
        }
    }
}

/// The per-function view a transfer function computes against.
struct Ctx<'a> {
    params: BTreeMap<Sym, usize>,
    state: &'a BTreeMap<Sym, Flowing>,
    table: &'a BTreeMap<Sym, FunctionSummary>,
}

impl Ctx<'_> {
    fn callee(&self, name: Sym) -> Callee<'_> {
        if let Some(flowing) = self.state.get(&name) {
            return Callee::InFlight(flowing);
        }
        self.table.get(&name).map_or(Callee::Unknown, Callee::Done)
    }

    /// The parameter index a value transparently names, through
    /// representation wrappers only.
    fn param_of(&self, value: &TypedValue) -> Option<usize> {
        match &peel(value).kind {
            TypedValueKind::Var { name, .. } => self.params.get(name).copied(),
            _ => None,
        }
    }
}

/// Scalability counters for one `summarize` run.
///
/// The analysis must stay bounded as the corpus grows, so a measurement (and
/// any future budget) reads these rather than re-deriving cost from wall
/// clock: one fact vector per function, one bounded fixed point per
/// component, and one transfer evaluation as the unit of join work (each
/// transfer performs the branch joins for one body).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct SummaryStats {
    /// Functions summarized (one fact vector each).
    pub functions: usize,
    /// Strongly connected components visited.
    pub components: usize,
    /// Components that are genuinely recursive (more than one member, or a
    /// self-edge), the only ones whose fixed point can iterate.
    pub recursive: usize,
    /// Fixed-point rounds across all components; every component takes at
    /// least two (one settling, one confirming).
    pub rounds: u64,
    /// Transfer-function evaluations (members times rounds, summed).
    pub transfers: u64,
}

/// Summarize every function, callee-first over strongly connected components.
#[must_use]
pub fn summarize(functions: &[TypedCoreFn]) -> BTreeMap<Sym, FunctionSummary> {
    summarize_counted(functions).0
}

/// `summarize`, also reporting the run's scalability counters.
#[must_use]
pub fn summarize_counted(
    functions: &[TypedCoreFn],
) -> (BTreeMap<Sym, FunctionSummary>, SummaryStats) {
    let index: BTreeMap<Sym, usize> = functions
        .iter()
        .enumerate()
        .map(|(position, function)| (function.name(), position))
        .collect();
    let adjacency: Vec<Vec<usize>> = functions
        .iter()
        .map(|function| {
            let callees: BTreeSet<usize> = calls_in(function.body())
                .into_iter()
                .filter_map(|callee| index.get(&callee).copied())
                .collect();
            callees.into_iter().collect()
        })
        .collect();

    let mut table: BTreeMap<Sym, FunctionSummary> = BTreeMap::new();
    let mut counters = SummaryStats {
        functions: functions.len(),
        ..SummaryStats::default()
    };
    for component in tarjan_scc(&adjacency) {
        counters.components += 1;
        if component.len() > 1
            || component
                .first()
                .is_some_and(|&position| adjacency[position].contains(&position))
        {
            counters.recursive += 1;
        }
        let members: Vec<&TypedCoreFn> = component
            .iter()
            .map(|&position| &functions[position])
            .collect();
        let seed: BTreeMap<Sym, Flowing> = members
            .iter()
            .map(|function| (function.name(), Flowing::bottom()))
            .collect();
        let state = stabilize(seed, |state| {
            counters.rounds += 1;
            counters.transfers += members.len() as u64;
            let mut changed = false;
            for function in &members {
                let ctx = Ctx {
                    params: param_index(function),
                    state,
                    table: &table,
                };
                let next = transfer(function, &ctx);
                if state.get(&function.name()) != Some(&next) {
                    state.insert(function.name(), next);
                    changed = true;
                }
            }
            changed
        });
        for function in &members {
            let flowing = &state[&function.name()];
            table.insert(
                function.name(),
                FunctionSummary {
                    result: flowing.result.clone().unwrap_or(ResultShape::Unknown),
                    effects: function.sig().body().effects().clone(),
                    allocation: flowing.allocation,
                    capture: capture_state(function.body()),
                    callbacks: flowing.callbacks.clone(),
                    cardinality: flowing.cardinality.clone().unwrap_or(Cardinality::Unknown),
                },
            );
        }
    }
    (table, counters)
}

fn param_index(function: &TypedCoreFn) -> BTreeMap<Sym, usize> {
    function
        .params()
        .iter()
        .enumerate()
        .map(|(position, binder)| (binder.name(), position))
        .collect()
}

fn transfer(function: &TypedCoreFn, ctx: &Ctx<'_>) -> Flowing {
    let mut flowing = Flowing::bottom();
    alloc_comp(function.body(), ctx, &mut flowing);
    flowing.result = tail_shape(function.body(), ctx);
    flowing.cardinality = spine_cardinality(function, ctx)
        .or_else(|| tail_cardinality(function.body(), ctx, &mut CardEnv::default()));
    flowing
}

// --- allocation and callback requirements ---------------------------------

/// Walk a body recording every fresh-cell site and every callable-parameter
/// invocation, mirroring the allocation checker's witness inventory over
/// typed Core: constructors, tuples, and thunks allocate; unboxed products
/// and scalars do not; a `Reuse` head spends a token instead of allocating; a
/// performed arena `alloc` still counts. Newtype coercions are transparent
/// representation nodes at this phase, so no erased-constructor set is
/// needed.
fn alloc_comp(comp: &TypedComp, ctx: &Ctx<'_>, out: &mut Flowing) {
    match comp.kind() {
        TypedCompKind::Reuse(_, value) => {
            match &peel(value).kind {
                TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
                    for field in fields {
                        alloc_value(field, out);
                    }
                }
                _ => alloc_value(value, out),
            }
            return;
        }
        TypedCompKind::Call { callee, args, .. } => {
            let view = ctx.callee(*callee);
            let (bound, slots) = view.allocation();
            out.allocation = out.allocation.max(bound);
            for &slot in slots {
                match args.get(slot).and_then(|argument| ctx.param_of(argument)) {
                    Some(param) => {
                        out.callbacks.insert(param);
                    }
                    // An unknown callable reaches an invoked slot; nothing
                    // bounds what it does.
                    None => out.allocation = AllocBound::Unbounded,
                }
            }
            for argument in args {
                alloc_value(argument, out);
            }
            return;
        }
        TypedCompKind::App { callee, args, .. } => {
            match forced_param(callee, ctx) {
                Some(param) => {
                    out.callbacks.insert(param);
                }
                None => out.allocation = AllocBound::Unbounded,
            }
            alloc_comp(callee, ctx, out);
            for argument in args {
                alloc_value(argument, out);
            }
            return;
        }
        TypedCompKind::Do { operation, .. } => {
            if operation.as_str() == names::ALLOC_OP {
                out.allocation = AllocBound::Unbounded;
            }
        }
        TypedCompKind::Io(op, _) => match op {
            IoOp::Print | IoOp::PrintF | IoOp::PrintS | IoOp::PrintNl | IoOp::Srand => {}
            IoOp::ReadInt | IoOp::ReadLine | IoOp::Rand => {
                out.allocation = AllocBound::Unbounded;
            }
        },
        // No per-op allocation attribute exists in the builtin registry yet,
        // so every string/collection builtin is conservatively allocating.
        TypedCompKind::StrBuiltin { .. } | TypedCompKind::RefNew(_) => {
            out.allocation = AllocBound::Unbounded;
        }
        _ => {}
    }
    each_value(comp, &mut |value| alloc_value(value, out));
    each_subcomp(comp, &mut |child| alloc_comp(child, ctx, out));
}

fn alloc_value(value: &TypedValue, out: &mut Flowing) {
    match &peel(value).kind {
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            out.allocation = AllocBound::Unbounded;
            for field in fields {
                alloc_value(field, out);
            }
        }
        // A thunk is one closure cell; what its body does when forced is
        // irrelevant to the bound, which this cell already saturates.
        TypedValueKind::Thunk(_) => out.allocation = AllocBound::Unbounded,
        TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                alloc_value(field, out);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                alloc_value(field, out);
            }
        }
        _ => {}
    }
}

/// The parameter a computed call head forces, when it is one.
fn forced_param(callee: &TypedComp, ctx: &Ctx<'_>) -> Option<usize> {
    match callee.kind() {
        TypedCompKind::Force(value) => ctx.param_of(value),
        _ => None,
    }
}

// --- result shape ----------------------------------------------------------

fn tail_shape(comp: &TypedComp, ctx: &Ctx<'_>) -> Option<ResultShape> {
    match comp.kind() {
        TypedCompKind::Bind(_, _, rest) => tail_shape(rest, ctx),
        TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
            tail_shape(body, ctx)
        }
        TypedCompKind::Lam(..) => Some(ResultShape::Closure),
        TypedCompKind::Return(value) | TypedCompKind::Reuse(_, value) => {
            Some(value_shape(value, ctx))
        }
        TypedCompKind::Prim(..) | TypedCompKind::FloatBuiltin(..) | TypedCompKind::Neg(..) => {
            Some(ResultShape::Scalar)
        }
        // An aborting tail completes on no path: the join identity.
        TypedCompKind::Error(_) => None,
        TypedCompKind::If(_, yes, no) => join_shape(tail_shape(yes, ctx), tail_shape(no, ctx)),
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .map(|(_, body)| tail_shape(body, ctx))
            .fold(None, join_shape),
        TypedCompKind::Call { callee, args, .. } => {
            match ctx.callee(*callee).result()? {
                // The callee returns its own parameter, so the site returns
                // that argument; read the argument's shape without chasing.
                ResultShape::Param(slot) => Some(
                    args.get(slot)
                        .map_or(ResultShape::Unknown, |argument| value_shape(argument, ctx)),
                ),
                shape => Some(shape),
            }
        }
        _ => Some(ResultShape::Unknown),
    }
}

fn value_shape(value: &TypedValue, ctx: &Ctx<'_>) -> ResultShape {
    match &peel(value).kind {
        TypedValueKind::Var { name, .. } => ctx
            .params
            .get(name)
            .map_or(ResultShape::Unknown, |&position| {
                ResultShape::Param(position)
            }),
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => ResultShape::Constant,
        TypedValueKind::Ctor { name, .. } => ResultShape::Constructor(*name),
        TypedValueKind::Tuple(_)
        | TypedValueKind::UnboxedTuple(_)
        | TypedValueKind::UnboxedRecord(_) => ResultShape::Product,
        TypedValueKind::Thunk(_) => ResultShape::Closure,
        TypedValueKind::Reinterpret(_)
        | TypedValueKind::LoweredRepr { .. }
        | TypedValueKind::NewtypeRepr { .. } => ResultShape::Unknown,
    }
}

fn join_shape(left: Option<ResultShape>, right: Option<ResultShape>) -> Option<ResultShape> {
    match (left, right) {
        (None, other) | (other, None) => other,
        (Some(a), Some(b)) if a == b => Some(a),
        _ => Some(ResultShape::Unknown),
    }
}

// --- cardinality -----------------------------------------------------------

/// The sized allocators, all of which take the element count first.
const fn is_sized_allocator(op: Builtin) -> bool {
    matches!(
        op,
        Builtin::ArrayNew | Builtin::BufNew | Builtin::TbufNew | Builtin::IbufNew
    )
}

/// What the walk down to a tail has learned about in-scope binders: integer
/// aliases usable inside size expressions, and proven counts for collection
/// binders. Typed Core threads most values through `bind t = return v`
/// aliases until the late simplifier collapses them, so a walk without this
/// environment would be blind to nearly every real count.
#[derive(Default)]
struct CardEnv {
    sizes: BTreeMap<Sym, CardExpr>,
    counts: BTreeMap<Sym, Cardinality>,
}

impl CardEnv {
    /// Record what one bind head teaches about its binder.
    fn learn(&mut self, binder: Sym, head: &TypedComp, ctx: &Ctx<'_>) {
        match head.kind() {
            // Binds nest on the left as well: the head's own inner chain
            // teaches its binders, and the chain's tail is the head's value.
            TypedCompKind::Bind(inner, inner_binder, rest) => {
                self.learn(inner_binder.name, inner, ctx);
                self.learn(binder, rest, ctx);
            }
            TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
                self.learn(binder, body, ctx);
            }
            TypedCompKind::Return(value) => {
                if let Some(expr) = card_expr(value, ctx, self) {
                    self.sizes.insert(binder, expr);
                }
                match self.count_of(value, ctx) {
                    Cardinality::Unknown => {}
                    known => {
                        self.counts.insert(binder, known);
                    }
                }
            }
            TypedCompKind::Call { callee, args, .. } => {
                if let Some(callee_count) = ctx.callee(*callee).cardinality() {
                    match call_cardinality(callee_count, args, ctx, self) {
                        Cardinality::Unknown => {}
                        known => {
                            self.counts.insert(binder, known);
                        }
                    }
                }
            }
            TypedCompKind::StrBuiltin { op, args, .. } if is_sized_allocator(*op) => {
                if let Some(expr) = args.first().and_then(|count| card_expr(count, ctx, self)) {
                    self.counts.insert(binder, Cardinality::Exact(expr));
                }
            }
            _ => {}
        }
    }

    /// The proven count of the collection a value names: a parameter is its
    /// own `CardOf`, a local is whatever its binding established. Vacuous on
    /// a non-collection value; a consumer only acts where it has proven the
    /// value a spine by independent means.
    fn count_of(&self, value: &TypedValue, ctx: &Ctx<'_>) -> Cardinality {
        match &peel(value).kind {
            TypedValueKind::Var { name, .. } => match ctx.params.get(name) {
                Some(&slot) => Cardinality::Exact(CardExpr::CardOf(slot)),
                None => self
                    .counts
                    .get(name)
                    .cloned()
                    .unwrap_or(Cardinality::Unknown),
            },
            _ => Cardinality::Unknown,
        }
    }
}

/// Every collection count provable for the binders of one body, keyed by
/// binder name. Binders are globally unique in typed Core, so one flat map
/// over the whole body (all arms included) is unambiguous; a consumer looks
/// up the binder it holds and ignores the rest. `table` supplies finished
/// callee summaries, so this is only meaningful after [`summarize`] has run.
pub(super) fn local_counts(
    function: &TypedCoreFn,
    table: &BTreeMap<Sym, FunctionSummary>,
) -> BTreeMap<Sym, Cardinality> {
    let unflowing = BTreeMap::new();
    let ctx = Ctx {
        params: param_index(function),
        state: &unflowing,
        table,
    };
    let mut env = CardEnv::default();
    learn_all(function.body(), &ctx, &mut env);
    env.counts
}

/// Teach a [`CardEnv`] every bind in a body, descending into branch arms and
/// wrapper computations. [`CardEnv::learn`] already recurses through a
/// left-nested head chain; revisiting those binders here re-inserts the same
/// facts, which is harmless.
fn learn_all(comp: &TypedComp, ctx: &Ctx<'_>, env: &mut CardEnv) {
    match comp.kind() {
        TypedCompKind::Bind(head, binder, rest) => {
            env.learn(binder.name, head, ctx);
            learn_all(head, ctx, env);
            learn_all(rest, ctx, env);
        }
        TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
            learn_all(body, ctx, env);
        }
        TypedCompKind::If(_, yes, no) => {
            learn_all(yes, ctx, env);
            learn_all(no, ctx, env);
        }
        TypedCompKind::Case(_, arms) => {
            for (_, body) in arms {
                learn_all(body, ctx, env);
            }
        }
        _ => {}
    }
}

fn tail_cardinality(comp: &TypedComp, ctx: &Ctx<'_>, env: &mut CardEnv) -> Option<Cardinality> {
    match comp.kind() {
        TypedCompKind::Bind(head, binder, rest) => {
            env.learn(binder.name, head, ctx);
            tail_cardinality(rest, ctx, env)
        }
        TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
            tail_cardinality(body, ctx, env)
        }
        TypedCompKind::Error(_) => None,
        TypedCompKind::Return(value) => Some(env.count_of(value, ctx)),
        // A sized allocator's recognizable count argument is the whole fact.
        TypedCompKind::StrBuiltin { op, args, .. } if is_sized_allocator(*op) => Some(
            args.first()
                .and_then(|count| card_expr(count, ctx, env))
                .map_or(Cardinality::Unknown, Cardinality::Exact),
        ),
        // Arms share one environment: binders are globally unique in typed
        // Core, so facts learned in one arm cannot capture names in another.
        TypedCompKind::If(_, yes, no) => join_cardinality(
            tail_cardinality(yes, ctx, env),
            tail_cardinality(no, ctx, env),
        ),
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .map(|(_, body)| tail_cardinality(body, ctx, env))
            .fold(None, join_cardinality),
        TypedCompKind::Call { callee, args, .. } => Some(call_cardinality(
            ctx.callee(*callee).cardinality()?,
            args,
            ctx,
            env,
        )),
        _ => Some(Cardinality::Unknown),
    }
}

/// A callee's cardinality composed into the caller at one call site:
/// substitute the size expression, and demote to an upper bound when either
/// side of the composition is one.
fn call_cardinality(
    callee: Cardinality,
    args: &[TypedValue],
    ctx: &Ctx<'_>,
    env: &CardEnv,
) -> Cardinality {
    let (expr, exact) = match callee {
        Cardinality::Exact(expr) => (expr, true),
        Cardinality::UpperBound(expr) => (expr, false),
        Cardinality::Unknown => return Cardinality::Unknown,
    };
    match substitute(&expr, args, ctx, env) {
        Some((expr, preserved)) if exact && preserved => Cardinality::Exact(expr),
        Some((expr, _)) => Cardinality::UpperBound(expr),
        None => Cardinality::Unknown,
    }
}

/// A callee's size expression rewritten into the caller's vocabulary,
/// together with whether exactness survived the composition: routing a
/// `CardOf` through an argument whose count is only an upper bound weakens
/// an exact claim to a bound.
fn substitute(
    expr: &CardExpr,
    args: &[TypedValue],
    ctx: &Ctx<'_>,
    env: &CardEnv,
) -> Option<(CardExpr, bool)> {
    match expr {
        CardExpr::Lit(count) => Some((CardExpr::Lit(*count), true)),
        CardExpr::Param(slot) => args
            .get(*slot)
            .and_then(|argument| card_expr(argument, ctx, env))
            .map(|expr| (expr, true)),
        CardExpr::Span(lo, hi) => {
            let (lo, _) = substitute(lo, args, ctx, env)?;
            let (hi, _) = substitute(hi, args, ctx, env)?;
            Some(match (lo, hi) {
                (CardExpr::Lit(lo), CardExpr::Lit(hi)) => {
                    (CardExpr::Lit(hi.saturating_sub(lo).max(0)), true)
                }
                (lo, hi) => (CardExpr::Span(Box::new(lo), Box::new(hi)), true),
            })
        }
        CardExpr::CardOf(slot) => {
            let argument = args.get(*slot)?;
            if let Some(&param) = match &peel(argument).kind {
                TypedValueKind::Var { name, .. } => ctx.params.get(name),
                _ => None,
            } {
                return Some((CardExpr::CardOf(param), true));
            }
            match env.count_of(argument, ctx) {
                Cardinality::Exact(expr) => Some((expr, true)),
                Cardinality::UpperBound(expr) => Some((expr, false)),
                Cardinality::Unknown => None,
            }
        }
    }
}

fn card_expr(value: &TypedValue, ctx: &Ctx<'_>, env: &CardEnv) -> Option<CardExpr> {
    match &peel(value).kind {
        TypedValueKind::Int(count) => Some(CardExpr::Lit(*count)),
        TypedValueKind::Var { name, .. } => match ctx.params.get(name) {
            Some(&slot) => Some(CardExpr::Param(slot)),
            None => env.sizes.get(name).cloned(),
        },
        _ => None,
    }
}

fn join_cardinality(left: Option<Cardinality>, right: Option<Cardinality>) -> Option<Cardinality> {
    match (left, right) {
        (None, other) | (other, None) => other,
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(Cardinality::Exact(a)), Some(Cardinality::UpperBound(b)))
        | (Some(Cardinality::UpperBound(a)), Some(Cardinality::Exact(b)))
            if a == b =>
        {
            Some(Cardinality::UpperBound(a))
        }
        _ => Some(Cardinality::Unknown),
    }
}

// --- structural cardinality ------------------------------------------------

/// What a spine walk knows about one in-scope binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpineAtom {
    /// A literal integer.
    Lit(i64),
    /// The parameter at this slot, unchanged.
    Param(usize),
    /// The parameter at this slot plus one.
    Step(usize),
    /// The comparison `params[lo] >= params[hi]`.
    Ge(usize, usize),
    /// The result of a bound structural self-call.
    Rec,
    /// The named field bound by the cons arm's pattern.
    Field(Sym),
    /// Anything the walk does not model.
    Opaque,
}

fn spine_atom(
    value: &TypedValue,
    params: &BTreeMap<Sym, usize>,
    env: &BTreeMap<Sym, SpineAtom>,
) -> SpineAtom {
    match &peel(value).kind {
        TypedValueKind::Int(literal) => SpineAtom::Lit(*literal),
        TypedValueKind::Var { name, .. } => match params.get(name) {
            Some(&slot) => SpineAtom::Param(slot),
            None => env.get(name).copied().unwrap_or(SpineAtom::Opaque),
        },
        _ => SpineAtom::Opaque,
    }
}

/// Count the direct self-calls in a computation, including inside the thunks
/// it builds: a recursion hidden in a suspended value must still be seen, or
/// a recognizer would count a spine the hidden call extends.
fn self_calls(comp: &TypedComp, name: Sym) -> usize {
    let mut count = 0;
    if let TypedCompKind::Call { callee, .. } = comp.kind() {
        if *callee == name {
            count += 1;
        }
    }
    each_subcomp(comp, &mut |child| count += self_calls(child, name));
    each_value(comp, &mut |value| {
        let mut nested = Vec::new();
        top_thunks_in_value(value, &mut nested);
        for thunk in nested {
            count += self_calls(thunk, name);
        }
    });
    count
}

/// A structural walk down one function's recursion paths. Alias binds resolve
/// to atoms; the argument vector of every bound self-call is collected and
/// validated after the walk, which sees the same atoms because binders are
/// globally unique and the environment only grows.
struct SpineWalk<'a> {
    name: Sym,
    params: &'a BTreeMap<Sym, usize>,
    env: BTreeMap<Sym, SpineAtom>,
    rec_args: Vec<Vec<TypedValue>>,
}

impl<'a> SpineWalk<'a> {
    const fn new(name: Sym, params: &'a BTreeMap<Sym, usize>) -> Self {
        Self {
            name,
            params,
            env: BTreeMap::new(),
            rec_args: Vec::new(),
        }
    }

    fn atom(&self, value: &TypedValue) -> SpineAtom {
        spine_atom(value, self.params, &self.env)
    }

    /// Strip the bind prefix of a computation, learning each binder, and
    /// return the tail. `None` declines the whole recognition: a head hides
    /// a self-call the walk cannot model, so any count would be a guess.
    fn strip<'c>(&mut self, mut comp: &'c TypedComp) -> Option<&'c TypedComp> {
        loop {
            match comp.kind() {
                TypedCompKind::Bind(head, binder, rest) => {
                    let learned = self.head_atom(head)?;
                    self.env.insert(binder.name, learned);
                    comp = rest;
                }
                TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
                    comp = body;
                }
                _ => return Some(comp),
            }
        }
    }

    fn head_atom(&mut self, head: &TypedComp) -> Option<SpineAtom> {
        Some(match head.kind() {
            // Binds nest on the left as well: the head's own inner chain
            // teaches its binders, and the chain's tail is the head's value.
            TypedCompKind::Bind(inner, binder, rest) => {
                let learned = self.head_atom(inner)?;
                self.env.insert(binder.name, learned);
                return self.head_atom(rest);
            }
            TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
                return self.head_atom(body);
            }
            TypedCompKind::Return(value) => self.atom(value),
            TypedCompKind::Prim(CoreOp::Ge, lhs, rhs) => match (self.atom(lhs), self.atom(rhs)) {
                (SpineAtom::Param(lo), SpineAtom::Param(hi)) => SpineAtom::Ge(lo, hi),
                _ => SpineAtom::Opaque,
            },
            TypedCompKind::Prim(CoreOp::Add, lhs, rhs) => match (self.atom(lhs), self.atom(rhs)) {
                (SpineAtom::Param(slot), SpineAtom::Lit(1))
                | (SpineAtom::Lit(1), SpineAtom::Param(slot)) => SpineAtom::Step(slot),
                _ => SpineAtom::Opaque,
            },
            TypedCompKind::Call { callee, args, .. } if *callee == self.name => {
                self.rec_args.push(args.clone());
                SpineAtom::Rec
            }
            // A self-call anywhere else in a head (a nested branch, a thunk
            // forced later) recurses where the walk cannot see it.
            _ if self_calls(head, self.name) > 0 => return None,
            _ => SpineAtom::Opaque,
        })
    }
}

/// The tail must return a nullary constructor; its name is the proof.
fn nullary_ctor(comp: &TypedComp, walk: &mut SpineWalk<'_>) -> Option<Sym> {
    let tail = walk.strip(comp)?;
    match tail.kind() {
        TypedCompKind::Return(value) => match &peel(value).kind {
            TypedValueKind::Ctor { name, fields, .. } if fields.is_empty() => Some(*name),
            _ => None,
        },
        _ => None,
    }
}

/// Recognize the counting builder `if lo >= hi then Empty else
/// Cons(_, self(.., lo + 1, .., hi, ..))`: a nullary constructor on the stop
/// branch, a two-field constructor whose second field is the single bound
/// self-call, the counter stepped by one and the limit passed through
/// unchanged. The proven count is `max(hi - lo, 0)`; every other argument
/// slot is free, since the induction is on the counter alone.
fn counting_builder(function: &TypedCoreFn, params: &BTreeMap<Sym, usize>) -> Option<Cardinality> {
    if self_calls(function.body(), function.name()) != 1 {
        return None;
    }
    let mut walk = SpineWalk::new(function.name(), params);
    let tail = walk.strip(function.body())?;
    let TypedCompKind::If(cond, stop, grow) = tail.kind() else {
        return None;
    };
    let SpineAtom::Ge(lo, hi) = walk.atom(cond) else {
        return None;
    };
    if lo == hi {
        return None;
    }
    nullary_ctor(stop, &mut walk)?;
    let grow_tail = walk.strip(grow)?;
    let TypedCompKind::Return(value) = grow_tail.kind() else {
        return None;
    };
    let TypedValueKind::Ctor { fields, .. } = &peel(value).kind else {
        return None;
    };
    let [element, spine] = &fields[..] else {
        return None;
    };
    // The spine continues through the second field; identical field types
    // would make the produced cell's spine side ambiguous.
    if walk.atom(spine) != SpineAtom::Rec
        || walk.atom(element) == SpineAtom::Rec
        || element.ty() == spine.ty()
    {
        return None;
    }
    let [args] = &walk.rec_args[..] else {
        return None;
    };
    if args.len() != function.params().len()
        || args.get(lo).map(|argument| walk.atom(argument)) != Some(SpineAtom::Step(lo))
        || args.get(hi).map(|argument| walk.atom(argument)) != Some(SpineAtom::Param(hi))
    {
        return None;
    }
    Some(Cardinality::Exact(CardExpr::Span(
        Box::new(CardExpr::Param(lo)),
        Box::new(CardExpr::Param(hi)),
    )))
}

/// The facts one spine-transformer recognition validates every leaf against.
struct SpineSpec {
    list_slot: usize,
    tail_name: Sym,
    tail_index: usize,
    empty_ctor: Sym,
    cons_ctor: Sym,
    arity: usize,
}

/// Recognize the spine transformer `case xs of Empty => Empty
/// | Cons(h, t) => ..`: recursion strictly on the scrutinized parameter's
/// tail. A leaf rebuilding the cons around the single recursive field keeps
/// the count exact (a map step); a leaf that stops with the same empty
/// constructor or tail-calls straight into the recursion truncates, demoting
/// the claim to an upper bound (a filter or take step).
fn spine_transformer(function: &TypedCoreFn, params: &BTreeMap<Sym, usize>) -> Option<Cardinality> {
    let mut walk = SpineWalk::new(function.name(), params);
    let tail = walk.strip(function.body())?;
    let TypedCompKind::Case(scrutinee, arms) = tail.kind() else {
        return None;
    };
    let SpineAtom::Param(list_slot) = walk.atom(scrutinee) else {
        return None;
    };
    if arms.len() != 2 {
        return None;
    }
    let mut empty = None;
    let mut cons = None;
    for (pattern, body) in arms {
        let TypedPattern::Ctor { name, fields, .. } = pattern else {
            return None;
        };
        let bound: Vec<_> = fields.iter().flatten().collect();
        match (fields.len(), bound.len()) {
            (0, 0) => empty = Some((*name, body)),
            (2, 2) => cons = Some((*name, bound, body)),
            _ => return None,
        }
    }
    let (empty_ctor, empty_body) = empty?;
    let (cons_ctor, cons_binders, cons_body) = cons?;
    if nullary_ctor(empty_body, &mut walk)? != empty_ctor {
        return None;
    }
    // The recursion tail is the single cons field carrying the scrutinized
    // list's own type; two same-typed fields leave the spine side ambiguous.
    let list_ty = function.params().get(list_slot)?.ty();
    let tails: Vec<(usize, Sym)> = cons_binders
        .iter()
        .enumerate()
        .filter(|(_, binder)| binder.ty() == list_ty)
        .map(|(index, binder)| (index, binder.name))
        .collect();
    let [(tail_index, tail_name)] = tails[..] else {
        return None;
    };
    for binder in &cons_binders {
        walk.env.insert(binder.name, SpineAtom::Field(binder.name));
    }
    let spec = SpineSpec {
        list_slot,
        tail_name,
        tail_index,
        empty_ctor,
        cons_ctor,
        arity: function.params().len(),
    };
    let mut exact = true;
    transform_paths(cons_body, &mut walk, &spec, &mut exact)?;
    if !walk
        .rec_args
        .iter()
        .all(|args| spine_args_ok(args, &walk, &spec))
    {
        return None;
    }
    Some(if exact {
        Cardinality::Exact(CardExpr::CardOf(list_slot))
    } else {
        Cardinality::UpperBound(CardExpr::CardOf(list_slot))
    })
}

/// Every completing path of a transformer's cons arm ends in one of three
/// leaves: the same cons rebuilt around the recursive field (exact), the
/// same empty constructor (truncation), or a bare tail call into the
/// recursion (truncation). Anything else declines the recognition.
fn transform_paths(
    comp: &TypedComp,
    walk: &mut SpineWalk<'_>,
    spec: &SpineSpec,
    exact: &mut bool,
) -> Option<()> {
    let tail = walk.strip(comp)?;
    match tail.kind() {
        TypedCompKind::If(_, yes, no) => {
            transform_paths(yes, walk, spec, exact)?;
            transform_paths(no, walk, spec, exact)
        }
        TypedCompKind::Call { callee, args, .. } if *callee == walk.name => {
            if !spine_args_ok(args, walk, spec) {
                return None;
            }
            *exact = false;
            Some(())
        }
        TypedCompKind::Return(value) => match &peel(value).kind {
            TypedValueKind::Ctor { name, fields, .. }
                if *name == spec.cons_ctor && fields.len() == 2 =>
            {
                let spine = fields.get(spec.tail_index)?;
                let element = fields.get(1 - spec.tail_index)?;
                (walk.atom(spine) == SpineAtom::Rec && walk.atom(element) != SpineAtom::Rec)
                    .then_some(())
            }
            TypedValueKind::Ctor { name, fields, .. }
                if *name == spec.empty_ctor && fields.is_empty() =>
            {
                *exact = false;
                Some(())
            }
            _ => None,
        },
        _ => None,
    }
}

/// A structural self-call must pass the scrutinized list's tail at the list
/// slot; every other slot is free, since the induction is on the spine alone.
fn spine_args_ok(args: &[TypedValue], walk: &SpineWalk<'_>, spec: &SpineSpec) -> bool {
    args.len() == spec.arity
        && args
            .get(spec.list_slot)
            .is_some_and(|argument| walk.atom(argument) == SpineAtom::Field(spec.tail_name))
}

/// A whole-function cardinality proven from the recursion shape itself,
/// tried before the tail walk.
fn spine_cardinality(function: &TypedCoreFn, ctx: &Ctx<'_>) -> Option<Cardinality> {
    counting_builder(function, &ctx.params).or_else(|| spine_transformer(function, &ctx.params))
}

// --- capture state ---------------------------------------------------------

/// Classify the closures a body builds by the strongest mutable-state
/// operation any of them performs. Conservative on ownership: a cell the
/// closure itself creates still counts, which only weakens a claim.
fn capture_state(body: &TypedComp) -> CaptureState {
    let mut thunks = Vec::new();
    thunks_in_comp(body, &mut thunks);
    if thunks.is_empty() {
        return CaptureState::NoClosures;
    }
    thunks
        .iter()
        .map(|thunk| thunk_state(thunk))
        .fold(CaptureState::Stateless, CaptureState::max)
}

fn thunk_state(body: &TypedComp) -> CaptureState {
    let mut strongest = CaptureState::Stateless;
    mutable_ops(body, &mut strongest);
    strongest
}

fn mutable_ops(comp: &TypedComp, strongest: &mut CaptureState) {
    match comp.kind() {
        TypedCompKind::Do { operation, .. } => {
            if names::parse_var_set(operation.as_str()).is_some() {
                *strongest = (*strongest).max(CaptureState::WritesMutable);
            } else if names::parse_var_get(operation.as_str()).is_some() {
                *strongest = (*strongest).max(CaptureState::ReadsMutable);
            }
        }
        TypedCompKind::RefSet(..) | TypedCompKind::RefNew(_) => {
            *strongest = (*strongest).max(CaptureState::WritesMutable);
        }
        TypedCompKind::RefGet(_) => {
            *strongest = (*strongest).max(CaptureState::ReadsMutable);
        }
        _ => {}
    }
    each_subcomp(comp, &mut |child| mutable_ops(child, strongest));
    each_value(comp, &mut |value| {
        let mut nested = Vec::new();
        top_thunks_in_value(value, &mut nested);
        for thunk in nested {
            mutable_ops(thunk, strongest);
        }
    });
}

#[cfg(test)]
pub(crate) mod tests {
    use super::super::{CompSig, CoreFnSig, CoreType, TypedBinder};
    use super::*;
    use crate::types::ty::Type;

    pub(crate) fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    pub(crate) fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    pub(crate) fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    pub(crate) fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(int()), TypedCompKind::Return(value))
    }

    pub(crate) fn lit(value: i64) -> TypedValue {
        TypedValue::new(int(), TypedValueKind::Int(value))
    }

    pub(crate) fn var(name: &str) -> TypedValue {
        TypedValue::new(
            int(),
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    pub(crate) fn call(callee: &str, args: Vec<TypedValue>) -> TypedComp {
        TypedComp::new(
            pure(int()),
            TypedCompKind::Call {
                callee: sym(callee),
                instantiation: Vec::new(),
                args,
            },
        )
    }

    pub(crate) fn function(name: &str, params: &[&str], body: TypedComp) -> TypedCoreFn {
        let binders: Vec<TypedBinder> = params
            .iter()
            .map(|param| TypedBinder::new(sym(param), int()))
            .collect();
        let sig = CoreFnSig::new(Vec::new(), vec![int(); params.len()], pure(int()));
        TypedCoreFn::new(sym(name), binders, body, sig, 0)
    }

    pub(crate) fn thunk(body: TypedComp) -> TypedValue {
        TypedValue::new(
            CoreType::Thunk(Box::new(body.sig().clone())),
            TypedValueKind::Thunk(Box::new(body)),
        )
    }

    /// A stand-in collection type, distinct from `int()` so the recognizers'
    /// spine-side type checks have something to distinguish.
    pub(crate) fn listy() -> CoreType {
        CoreType::Source(Type::Str)
    }

    pub(crate) fn lvar(name: &str) -> TypedValue {
        TypedValue::new(
            listy(),
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    pub(crate) fn bind(head: TypedComp, binder: &str, ty: CoreType, rest: TypedComp) -> TypedComp {
        let sig = rest.sig().clone();
        TypedComp::new(
            sig,
            TypedCompKind::Bind(
                Box::new(head),
                TypedBinder::new(sym(binder), ty),
                Box::new(rest),
            ),
        )
    }

    pub(crate) fn prim(op: CoreOp, lhs: TypedValue, rhs: TypedValue) -> TypedComp {
        TypedComp::new(pure(int()), TypedCompKind::Prim(op, lhs, rhs))
    }

    pub(crate) fn iff(cond: TypedValue, yes: TypedComp, no: TypedComp) -> TypedComp {
        TypedComp::new(
            pure(int()),
            TypedCompKind::If(cond, Box::new(yes), Box::new(no)),
        )
    }

    pub(crate) fn ctor(name: &str, fields: Vec<TypedValue>) -> TypedValue {
        TypedValue::new(
            listy(),
            TypedValueKind::Ctor {
                name: sym(name),
                tag: 0,
                instantiation: Vec::new(),
                fields,
            },
        )
    }

    pub(crate) fn ctor_pat(name: &str, fields: Vec<Option<TypedBinder>>) -> TypedPattern {
        TypedPattern::Ctor {
            name: sym(name),
            instantiation: Vec::new(),
            fields,
        }
    }

    pub(crate) fn case_of(
        scrutinee: TypedValue,
        arms: Vec<(TypedPattern, TypedComp)>,
    ) -> TypedComp {
        TypedComp::new(pure(int()), TypedCompKind::Case(scrutinee, arms))
    }

    pub(crate) fn function_with(
        name: &str,
        params: Vec<(&str, CoreType)>,
        body: TypedComp,
    ) -> TypedCoreFn {
        let mut binders = Vec::with_capacity(params.len());
        let mut tys = Vec::with_capacity(params.len());
        for (param, ty) in params {
            binders.push(TypedBinder::new(sym(param), ty.clone()));
            tys.push(ty);
        }
        let sig = CoreFnSig::new(Vec::new(), tys, pure(int()));
        TypedCoreFn::new(sym(name), binders, body, sig, 0)
    }

    /// The counting-builder shape as real typed Core spells it, aliases and
    /// all: `if lo >= hi then Nil else Cons(lo, self(lo + 1, hi))`.
    pub(crate) fn range_fn() -> TypedCoreFn {
        let grow = bind(
            prim(CoreOp::Add, var("lo"), lit(1)),
            "n",
            int(),
            bind(
                call("rng", vec![var("n"), var("hi")]),
                "r",
                listy(),
                ret(ctor("Cons", vec![var("lo"), lvar("r")])),
            ),
        );
        let body = bind(
            prim(CoreOp::Ge, var("lo"), var("hi")),
            "c",
            int(),
            iff(var("c"), ret(ctor("Nil", Vec::new())), grow),
        );
        function("rng", &["lo", "hi"], body)
    }

    /// The spine-transformer map shape: every cons is rebuilt around the
    /// single recursive tail call, so the count is preserved exactly.
    pub(crate) fn map_fn() -> TypedCoreFn {
        let cons_body = bind(
            prim(CoreOp::Add, var("h"), lit(1)),
            "e",
            int(),
            bind(
                call("m", vec![var("f"), lvar("t")]),
                "r",
                listy(),
                ret(ctor("Cons", vec![var("e"), lvar("r")])),
            ),
        );
        let arms = vec![
            (ctor_pat("Nil", Vec::new()), ret(ctor("Nil", Vec::new()))),
            (
                ctor_pat(
                    "Cons",
                    vec![
                        Some(TypedBinder::new(sym("h"), int())),
                        Some(TypedBinder::new(sym("t"), listy())),
                    ],
                ),
                cons_body,
            ),
        ];
        function_with(
            "m",
            vec![("f", int()), ("xs", listy())],
            case_of(lvar("xs"), arms),
        )
    }

    #[test]
    fn literal_tail_is_constant_and_allocation_free() {
        let table = summarize(&[function("answer", &[], ret(lit(7)))]);
        let summary = &table[&sym("answer")];
        assert_eq!(summary.result, ResultShape::Constant);
        assert_eq!(summary.allocation, AllocBound::Zero);
        assert_eq!(summary.capture, CaptureState::NoClosures);
        assert!(summary.callbacks.is_empty());
        assert_eq!(summary.cardinality, Cardinality::Unknown);
    }

    #[test]
    fn constructor_tail_allocates_and_propagates_through_calls() {
        let wrapped = TypedValue::new(
            int(),
            TypedValueKind::Ctor {
                name: sym("Some"),
                tag: 0,
                instantiation: Vec::new(),
                fields: vec![var("x")],
            },
        );
        let wrap = function("wrap", &["x"], ret(wrapped));
        let caller = function("caller", &[], call("wrap", vec![lit(7)]));
        let table = summarize(&[wrap, caller]);
        assert_eq!(
            table[&sym("wrap")].result,
            ResultShape::Constructor(sym("Some"))
        );
        assert_eq!(table[&sym("wrap")].allocation, AllocBound::Unbounded);
        assert_eq!(
            table[&sym("caller")].result,
            ResultShape::Constructor(sym("Some"))
        );
        assert_eq!(table[&sym("caller")].allocation, AllocBound::Unbounded);
    }

    #[test]
    fn identity_result_remaps_to_the_argument_at_the_call_site() {
        let id = function("id", &["x"], ret(var("x")));
        let seven = function("seven", &[], call("id", vec![lit(7)]));
        let pass = function("pass", &["y"], call("id", vec![var("y")]));
        let table = summarize(&[id, seven, pass]);
        assert_eq!(table[&sym("id")].result, ResultShape::Param(0));
        assert_eq!(table[&sym("seven")].result, ResultShape::Constant);
        assert_eq!(table[&sym("pass")].result, ResultShape::Param(0));
    }

    #[test]
    fn counters_report_components_recursion_and_rounds() {
        let id = function("id", &["x"], ret(var("x")));
        let looping = TypedComp::new(
            pure(int()),
            TypedCompKind::If(
                var("x"),
                Box::new(call("again", vec![var("x")])),
                Box::new(ret(var("x"))),
            ),
        );
        let again = function("again", &["x"], looping);
        let (table, stats) = summarize_counted(&[id, again]);
        assert_eq!(table.len(), 2);
        assert_eq!(stats.functions, 2);
        assert_eq!(stats.components, 2);
        assert_eq!(stats.recursive, 1);
        // Each component settles then confirms, so two singleton components
        // take at least four rounds with one transfer per round.
        assert!(stats.rounds >= 4);
        assert_eq!(stats.transfers, stats.rounds);
    }

    #[test]
    fn self_recursion_reaches_a_fixed_point() {
        let body = TypedComp::new(
            pure(int()),
            TypedCompKind::If(
                var("x"),
                Box::new(call("again", vec![var("x")])),
                Box::new(ret(var("x"))),
            ),
        );
        let table = summarize(&[function("again", &["x"], body)]);
        let summary = &table[&sym("again")];
        assert_eq!(summary.result, ResultShape::Param(0));
        assert_eq!(summary.allocation, AllocBound::Zero);
    }

    #[test]
    fn invoking_a_parameter_records_the_slot_and_forwarding_inherits_it() {
        let apply_body = TypedComp::new(
            pure(int()),
            TypedCompKind::App {
                callee: Box::new(TypedComp::new(pure(int()), TypedCompKind::Force(var("f")))),
                instantiation: Vec::new(),
                args: vec![lit(7)],
            },
        );
        let apply = function("apply", &["f"], apply_body);
        let forward = function("forward", &["g"], call("apply", vec![var("g")]));
        let concrete = function("concrete", &[], call("apply", vec![thunk(ret(lit(1)))]));
        let table = summarize(&[apply, forward, concrete]);
        assert_eq!(table[&sym("apply")].allocation, AllocBound::Zero);
        assert!(table[&sym("apply")].callbacks.contains(&0));
        assert_eq!(table[&sym("forward")].allocation, AllocBound::Zero);
        assert!(table[&sym("forward")].callbacks.contains(&0));
        // A literal thunk in the invoked slot is a fresh closure cell and an
        // unbounded callable, both of which saturate the caller's bound.
        assert_eq!(table[&sym("concrete")].allocation, AllocBound::Unbounded);
        assert!(table[&sym("concrete")].callbacks.is_empty());
    }

    #[test]
    fn sized_allocators_carry_exact_cardinality_through_calls() {
        let make_body = TypedComp::new(
            pure(int()),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayNew,
                instantiation: Vec::new(),
                args: vec![var("n"), lit(0)],
            },
        );
        let make = function("make", &["n"], make_body);
        let five = function("five", &[], call("make", vec![lit(5)]));
        let table = summarize(&[make, five]);
        assert_eq!(
            table[&sym("make")].cardinality,
            Cardinality::Exact(CardExpr::Param(0))
        );
        assert_eq!(
            table[&sym("five")].cardinality,
            Cardinality::Exact(CardExpr::Lit(5))
        );
    }

    #[test]
    fn discharge_resolves_a_requirement_from_the_callable_summary() {
        let apply_body = TypedComp::new(
            pure(int()),
            TypedCompKind::App {
                callee: Box::new(TypedComp::new(pure(int()), TypedCompKind::Force(var("f")))),
                instantiation: Vec::new(),
                args: vec![lit(7)],
            },
        );
        let apply = function("apply", &["f"], apply_body);
        let lean = function("lean", &["x"], ret(var("x")));
        let heavy = function("heavy", &[], ret(thunk(ret(lit(1)))));
        let table = summarize(&[apply, lean, heavy]);
        assert_eq!(
            discharge(&table, sym("apply"), 0, sym("lean")),
            Discharge::Met
        );
        assert_eq!(
            discharge(&table, sym("apply"), 0, sym("heavy")),
            Discharge::Unmet
        );
        // The callee never invokes slot 1, so anything discharges it.
        assert_eq!(
            discharge(&table, sym("apply"), 1, sym("heavy")),
            Discharge::Met
        );
        // Forwarding leaves `apply`'s own requirement standing, so binding it
        // as the callback resolves nothing without this site's arguments.
        assert_eq!(
            discharge(&table, sym("apply"), 0, sym("apply")),
            Discharge::Unknown
        );
        assert_eq!(
            discharge(&table, sym("apply"), 0, sym("absent")),
            Discharge::Unknown
        );
    }

    #[test]
    fn callable_identity_names_the_eta_wrapped_function() {
        use super::super::specialize::callable_identity;
        let param = TypedBinder::new(sym("p0"), int());
        let body = TypedComp::new(
            pure(int()),
            TypedCompKind::Lam(vec![param], Box::new(call("target", vec![var("p0")]))),
        );
        let wrapper = thunk(body);
        assert_eq!(callable_identity(&wrapper), Some(sym("target")));
        assert_eq!(callable_identity(&lit(1)), None);
        assert_eq!(callable_identity(&thunk(ret(lit(1)))), None);
    }

    #[test]
    fn closures_are_classified_by_their_mutable_state_operations() {
        let stateless = function("stateless", &[], ret(thunk(ret(lit(1)))));
        let writer_thunk = thunk(TypedComp::new(
            pure(int()),
            TypedCompKind::RefSet(var("cell"), lit(1)),
        ));
        let writer = function("writer", &["cell"], ret(writer_thunk));
        let table = summarize(&[stateless, writer]);
        assert_eq!(table[&sym("stateless")].capture, CaptureState::Stateless);
        assert_eq!(table[&sym("writer")].capture, CaptureState::WritesMutable);
    }

    #[test]
    fn counting_builder_recursion_proves_a_span_count() {
        let nineteen = function("nineteen", &[], call("rng", vec![lit(1), lit(20)]));
        let table = summarize(&[range_fn(), nineteen]);
        assert_eq!(
            table[&sym("rng")].cardinality,
            Cardinality::Exact(CardExpr::Span(
                Box::new(CardExpr::Param(0)),
                Box::new(CardExpr::Param(1)),
            ))
        );
        // The exclusive span folds at a fully literal call site.
        assert_eq!(
            table[&sym("nineteen")].cardinality,
            Cardinality::Exact(CardExpr::Lit(19))
        );
    }

    #[test]
    fn spine_transformer_map_shape_is_exact_in_the_list_count() {
        let table = summarize(&[map_fn()]);
        assert_eq!(
            table[&sym("m")].cardinality,
            Cardinality::Exact(CardExpr::CardOf(1))
        );
    }

    #[test]
    fn spine_transformer_filter_shape_is_an_upper_bound() {
        let keep = TypedComp::new(
            pure(int()),
            TypedCompKind::App {
                callee: Box::new(TypedComp::new(pure(int()), TypedCompKind::Force(var("p")))),
                instantiation: Vec::new(),
                args: vec![var("h")],
            },
        );
        let cons_body = bind(
            keep,
            "keep",
            int(),
            iff(
                var("keep"),
                bind(
                    call("flt", vec![var("p"), lvar("t")]),
                    "r",
                    listy(),
                    ret(ctor("Cons", vec![var("h"), lvar("r")])),
                ),
                call("flt", vec![var("p"), lvar("t")]),
            ),
        );
        let arms = vec![
            (ctor_pat("Nil", Vec::new()), ret(ctor("Nil", Vec::new()))),
            (
                ctor_pat(
                    "Cons",
                    vec![
                        Some(TypedBinder::new(sym("h"), int())),
                        Some(TypedBinder::new(sym("t"), listy())),
                    ],
                ),
                cons_body,
            ),
        ];
        let flt = function_with(
            "flt",
            vec![("p", int()), ("xs", listy())],
            case_of(lvar("xs"), arms),
        );
        let table = summarize(&[flt]);
        assert_eq!(
            table[&sym("flt")].cardinality,
            Cardinality::UpperBound(CardExpr::CardOf(1))
        );
    }

    #[test]
    fn a_built_count_composes_through_a_transformer_call() {
        let body = bind(
            call("rng", vec![lit(1), lit(20)]),
            "built",
            listy(),
            call("m", vec![lit(0), lvar("built")]),
        );
        let composed = function("composed", &[], body);
        let table = summarize(&[range_fn(), map_fn(), composed]);
        assert_eq!(
            table[&sym("composed")].cardinality,
            Cardinality::Exact(CardExpr::Lit(19))
        );
    }

    #[test]
    fn summary_encoding_is_deterministic_and_name_ordered() {
        // Summarize in reverse-alphabetical definition order so the interner
        // sees `zeta` first; the encoding must still order rows by string.
        let table = summarize(&[
            function("zeta", &[], ret(lit(1))),
            function("alpha", &["x"], ret(var("x"))),
        ]);
        let bytes = encode_summaries(&table);
        assert_eq!(bytes, encode_summaries(&table));
        let text = String::from_utf8(bytes).unwrap();
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some(SUMMARY_ENCODING_SCHEMA));
        let rows: Vec<&str> = lines.collect();
        assert_eq!(
            rows,
            [
                "alpha\tparam 0\t{}\tzero\tno-closures\t\texact count of param 0",
                "zeta\tconstant\t{}\tzero\tno-closures\t\tunknown",
            ]
        );
    }

    #[test]
    fn summary_encoding_covers_every_field() {
        // A row exercising the non-default value of every column: a callback
        // slot, a constructor result behind an allocating body, a proven span
        // cardinality, and a mutable-state closure.
        let table = summarize(&[range_fn()]);
        let text = String::from_utf8(encode_summaries(&table)).unwrap();
        assert!(
            text.contains("rng\tunknown\t{}\tunbounded\tno-closures\t\texact param 1 - param 0")
        );
        assert_eq!(
            ResultShape::Constructor(sym("Some")).render(),
            "constructor `Some`"
        );
        assert_eq!(CaptureState::WritesMutable.render(), "writes-mutable");
        assert_eq!(
            Cardinality::UpperBound(CardExpr::CardOf(2)).render(),
            "at-most count of param 2"
        );
    }

    #[test]
    fn a_transformer_recursing_on_the_whole_list_is_declined() {
        // Identical to the map shape except the self-call passes the
        // scrutinized list back instead of its tail: no count is claimable.
        let cons_body = bind(
            call("w", vec![var("f"), lvar("xs")]),
            "r",
            listy(),
            ret(ctor("Cons", vec![var("h"), lvar("r")])),
        );
        let arms = vec![
            (ctor_pat("Nil", Vec::new()), ret(ctor("Nil", Vec::new()))),
            (
                ctor_pat(
                    "Cons",
                    vec![
                        Some(TypedBinder::new(sym("h"), int())),
                        Some(TypedBinder::new(sym("t"), listy())),
                    ],
                ),
                cons_body,
            ),
        ];
        let whole = function_with(
            "w",
            vec![("f", int()), ("xs", listy())],
            case_of(lvar("xs"), arms),
        );
        let table = summarize(&[whole]);
        assert_eq!(table[&sym("w")].cardinality, Cardinality::Unknown);
    }
}
