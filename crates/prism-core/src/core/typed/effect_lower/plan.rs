//! Reachable operations and the conditions that require free-monad lowering.
//!
//! [`EffectPlan`] centralizes operation reachability for the cascade and erasure
//! passes. Each pass computes it for the tree it receives.
//!
//! Reachability is the least fixpoint of:
//!
//! * the operations a body names directly (its `do`s, handler arms, and masks,
//!   including inside thunk literals),
//! * the reachable set of every function it calls by name, and
//! * the signatures that flowed into its thunk-valued parameters.
//!
//! The third contribution covers forced thunk parameters, which do not appear as
//! named call-graph edges.
//!
//! [`EffectPlan::opaque_thunks`] records thunks hidden in constructors or tuples,
//! whose forcing sites cannot be bounded by the call graph or [`ThunkFlow`].
//!
//! [`EffectPlan::tracked_captures`] contains captures described by a signature;
//! [`EffectPlan::opaque_captures`] contains the rest. Their union is available as
//! [`EffectPlan::thunk_effects`].
//!
//! Erasure passes use the reachable set from their input tree because their work
//! removes the effectful state represented there.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use prism_common::fixpoint::least_fixpoint;
use prism_common::sym::Sym;

use crate::core::EffectStrategy;

use super::super::inline::calls_in;
use super::super::traverse::Visit;
use super::super::{on_core_stack, TypedComp, TypedCompKind, TypedCoreFn, TypedValue};
use super::decline::Decline;
use super::flow::{self, ThunkFlow};
use super::latent::{self, Latent};
use super::walk::{
    collect_ops, each_subcomp, each_subterm, each_value, is_thunk, thunks_in_comp,
    top_thunks_in_value,
};

/// The reachable-operation set of a function that is not in the plan (a driver
/// generated after the plan was computed, or a callee outside the program).
static NO_OPS: BTreeSet<Sym> = BTreeSet::new();

/// The empty cell in a rendered plan, so an absent set reads as a value rather
/// than as a missing column.
const NOTHING: &str = "-";

/// The column a rendered plan's header rows put their values in, wide enough
/// for the longest label so every value starts at the same offset.
const LABEL_WIDTH: usize = 17;

// The marks a rendered plan can carry on one function's row, in one place so a
// reader of the artifact and a writer of it share one vocabulary.
const GENUINE: &str = "genuine";
const ESCAPING: &str = "escaping";
const CAPTURES: &str = "captures";
const CAPTURES_OPAQUE: &str = "captures-opaque";

/// Which functions capture an effectful computation in a first-class thunk, and
/// for each one whether the plan can name what forcing that thunk will run.
///
/// A capture is *tracked* when the function lets nothing escape, and every
/// effectful thunk its body builds is a thunk over a lambda standing in a value
/// position of its own: the one shape a thunk signature describes, so the
/// position the thunk flows from carries what it performs. It is *opaque*
/// otherwise, which is the case where nothing bounds the forcing.
///
/// The distinction is a precision fact, not a semantic one. Both halves capture,
/// and every consumer that acts on the capture reads the union.
#[derive(Default, Debug)]
struct Captures {
    tracked: BTreeSet<Sym>,
    opaque: BTreeSet<Sym>,
    // The union, materialized rather than recomputed so the long-standing fact
    // the cascade and the fallback warning read stays a borrow of one set.
    all: BTreeSet<Sym>,
}

/// Every reachability and purity fact the lowering passes are entitled to ask
/// about one program tree.
#[derive(Debug)]
pub struct EffectPlan {
    latent: Latent,
    flow: ThunkFlow,
    reach: BTreeMap<Sym, BTreeSet<Sym>>,
    parameters: BTreeMap<Sym, BTreeSet<Sym>>,
    escaping: BTreeSet<Sym>,
    genuine: BTreeSet<Sym>,
    captures: Captures,
}

impl EffectPlan {
    /// Compute the plan for one program tree.
    #[must_use]
    pub fn analyze(functions: &[TypedCoreFn]) -> Self {
        on_core_stack(|| {
            let latent = latent::latent_map(functions);
            let flow = flow::analyze(functions, &latent);
            Self::from_parts_on_core_stack(functions, latent, flow)
        })
    }

    /// The plan for a tree whose latent map and thunk flow are already in hand,
    /// so the cascade pays for each fixpoint once.
    #[must_use]
    pub fn from_parts(functions: &[TypedCoreFn], latent: Latent, flow: ThunkFlow) -> Self {
        on_core_stack(|| Self::from_parts_on_core_stack(functions, latent, flow))
    }

    fn from_parts_on_core_stack(
        functions: &[TypedCoreFn],
        latent: Latent,
        flow: ThunkFlow,
    ) -> Self {
        // What arrived in each function's thunk-valued parameters, with the mask
        // depth dropped: reachability asks whether an op can run at all, not how
        // many handlers of it are still to be skipped.
        let parameters: BTreeMap<Sym, BTreeSet<Sym>> = flow
            .param
            .iter()
            .map(|(name, slots)| {
                (
                    *name,
                    slots
                        .iter()
                        .flat_map(|slot| slot.iter().map(|masked| masked.id))
                        .collect(),
                )
            })
            .collect();

        let own: BTreeMap<Sym, BTreeSet<Sym>> = functions
            .iter()
            .map(|function| {
                let mut operations = BTreeSet::new();
                collect_ops(function.body(), &mut operations);
                operations.extend(parameters.get(&function.name()).into_iter().flatten());
                (function.name(), operations)
            })
            .collect();
        let calls: BTreeMap<Sym, BTreeSet<Sym>> = functions
            .iter()
            .map(|function| {
                (
                    function.name(),
                    calls_in(function.body()).into_iter().collect(),
                )
            })
            .collect();
        let seed: BTreeMap<Sym, BTreeSet<Sym>> = functions
            .iter()
            .map(|function| (function.name(), BTreeSet::new()))
            .collect();
        let reach = least_fixpoint(seed, |name, current| {
            let mut reachable = own[name].clone();
            for callee in &calls[name] {
                if let Some(callee_reach) = current.get(callee) {
                    reachable.extend(callee_reach.iter().copied());
                }
            }
            reachable
        });

        let genuine = genuine_effects(&latent);
        let mut escaping = flow::escaping_fns(functions, &latent, &flow);
        escaping.extend(
            functions
                .iter()
                .filter(|function| open_resume_escapes(function.body(), &latent))
                .map(TypedCoreFn::name),
        );
        let captures = captures(functions, &genuine, &escaping, &latent);

        Self {
            latent,
            flow,
            reach,
            parameters,
            escaping,
            genuine,
            captures,
        }
    }

    /// The mask-aware latent map this plan was built from.
    #[must_use]
    pub const fn latent(&self) -> &Latent {
        &self.latent
    }

    /// The interprocedural thunk flow this plan was built from.
    #[must_use]
    pub const fn flow(&self) -> &ThunkFlow {
        &self.flow
    }

    /// Every operation `function` can perform, transitively over calls and over
    /// the thunks that flow into it.
    #[must_use]
    pub fn ops(&self, function: Sym) -> &BTreeSet<Sym> {
        self.reach.get(&function).unwrap_or(&NO_OPS)
    }

    /// Every operation the computation `comp`, occurring in `owner`'s body, can
    /// perform: what it names directly, what the functions it calls by name can
    /// reach, and, when it applies a value rather than a name, whatever flowed
    /// into `owner`'s thunk-valued parameters.
    #[must_use]
    pub fn ops_in(&self, owner: Sym, comp: &TypedComp) -> BTreeSet<Sym> {
        let mut operations = BTreeSet::new();
        collect_ops(comp, &mut operations);
        let mut callees = BTreeSet::new();
        collect_calls(comp, &mut callees);
        for callee in callees {
            operations.extend(self.ops(callee).iter().copied());
        }
        // A value application forces whatever flowed to it. The plan can name
        // that only for a thunk that arrived as a parameter, so anything else
        // applied here is answered with the whole enclosing function's reach.
        if applies_value(comp) {
            operations.extend(self.parameters.get(&owner).into_iter().flatten());
            if self.opaque_thunks() {
                operations.extend(self.ops(owner).iter().copied());
            }
        }
        operations
    }

    /// Every operation the computation `comp`, occurring in `owner`'s body, can
    /// still perform in its enclosing context: what its own evaluation leaves
    /// unhandled, what any thunk under it would perform when forced (forcing is
    /// out of `comp`'s control, so a handler `comp` installs does not discharge
    /// it), and, at a value application, whatever flowed into `owner`'s
    /// thunk-valued parameters.
    ///
    /// This is the question a pass asks before rewriting `comp` in a way an
    /// enclosing handler could observe. Contrast [`EffectPlan::ops_in`], which
    /// asks what `comp` can run at all, handled or not.
    #[must_use]
    pub fn escapes_in(&self, owner: Sym, comp: &TypedComp) -> BTreeSet<Sym> {
        let mut escaping = BTreeSet::new();
        latent::latent(comp, &self.latent, &mut escaping);
        let mut thunks = Vec::new();
        thunks_in_comp(comp, &mut thunks);
        for thunk in thunks {
            latent::latent(thunk, &self.latent, &mut escaping);
        }
        let mut out: BTreeSet<Sym> = escaping.into_iter().map(|masked| masked.id).collect();
        if applies_value(comp) {
            out.extend(self.parameters.get(&owner).into_iter().flatten());
        }
        out
    }

    /// Whether some effectful thunk in this program is untrackable: buried in a
    /// constructor or tuple, or handed to a dynamic callee, so no reachable set
    /// covers what forcing it will run. A guard whose wrong answer is unsound
    /// (rather than merely slow) declines outright when this holds.
    #[must_use]
    pub fn opaque_thunks(&self) -> bool {
        !self.escaping.is_empty()
    }

    /// The functions that let an effectful thunk escape untrackably, or whose
    /// handler resumes from inside one. These seed every free-monad region.
    #[must_use]
    pub const fn escaping(&self) -> &BTreeSet<Sym> {
        &self.escaping
    }

    /// The functions with a non-empty latent set: those that still perform an
    /// operation once every erasure has run.
    #[must_use]
    pub const fn genuine(&self) -> &BTreeSet<Sym> {
        &self.genuine
    }

    /// The functions that capture an effectful computation in a first-class
    /// thunk. This is what widens a confined region to the whole program, and
    /// the same fact the fallback warning reports as a cause.
    #[must_use]
    pub const fn thunk_effects(&self) -> &BTreeSet<Sym> {
        &self.captures.all
    }

    /// The capturing functions whose captured thunks the plan can name: each
    /// one lets nothing escape, and builds its effectful thunks as thunks over
    /// lambdas standing in value positions of their own, which is the shape a
    /// thunk signature describes. A subset of [`EffectPlan::thunk_effects`],
    /// disjoint from [`EffectPlan::opaque_captures`].
    #[must_use]
    pub const fn tracked_captures(&self) -> &BTreeSet<Sym> {
        &self.captures.tracked
    }

    /// The capturing functions whose captured thunks the plan cannot name: what
    /// forcing them runs is bounded by nothing. A subset of
    /// [`EffectPlan::thunk_effects`], disjoint from
    /// [`EffectPlan::tracked_captures`].
    #[must_use]
    pub const fn opaque_captures(&self) -> &BTreeSet<Sym> {
        &self.captures.opaque
    }

    /// The functions the plan covers, in name order.
    pub fn functions(&self) -> impl Iterator<Item = Sym> + '_ {
        self.reach.keys().copied()
    }

    /// The plan as a stable text artifact, headed by the strategy it explains.
    ///
    /// Every input to the tier decision is a row here, so a rung is read off one
    /// artifact rather than reverse-engineered from which passes fired. Rows and
    /// cells are ordered by name, not by interning order, so the artifact is a
    /// function of the program alone.
    #[must_use]
    pub fn render(&self, strategy: EffectStrategy, declined: Option<Decline>) -> String {
        let mut out = String::new();
        let mut row = |label: &str, value: &str| {
            writeln!(out, "{label:<LABEL_WIDTH$}{value}").unwrap();
        };
        row("strategy", &strategy.to_string());
        // Why the confined region was refused, when one was attempted and
        // refused. A strategy nobody expected is read back to the shape that
        // caused it from this row rather than from a rebuilt lowering.
        row(
            "confined-decline",
            &declined.map_or_else(|| NOTHING.to_string(), |declined| declined.cell()),
        );
        row("opaque-thunks", &self.opaque_thunks().to_string());
        row("escaping", &names(&self.escaping));
        row("thunk-effects", &names(self.thunk_effects()));
        let mut rows: Vec<(&Sym, &BTreeSet<Sym>)> = self.reach.iter().collect();
        rows.sort_unstable_by_key(|(name, _)| name.as_str());
        for (name, operations) in rows {
            let marks = [
                self.genuine.contains(name).then_some(GENUINE),
                self.escaping.contains(name).then_some(ESCAPING),
                self.captures.tracked.contains(name).then_some(CAPTURES),
                self.captures
                    .opaque
                    .contains(name)
                    .then_some(CAPTURES_OPAQUE),
            ];
            let marks: Vec<&str> = marks.into_iter().flatten().collect();
            write!(out, "fn  {}  ops={}", name.as_str(), names(operations)).unwrap();
            if let Some(parameters) = self.parameters.get(name) {
                let flattened: BTreeSet<Sym> = parameters.iter().copied().collect();
                if !flattened.is_empty() {
                    write!(out, "  thunk-params={}", names(&flattened)).unwrap();
                }
            }
            if !marks.is_empty() {
                write!(out, "  {}", marks.join(",")).unwrap();
            }
            out.push('\n');
        }
        out
    }
}

// A set of names as one comma-separated cell, so every row is a single line.
fn names(set: &BTreeSet<Sym>) -> String {
    if set.is_empty() {
        return NOTHING.to_string();
    }
    let mut parts: Vec<&str> = set.iter().map(|name| name.as_str()).collect();
    parts.sort_unstable();
    parts.join(",")
}

/// The capturing functions of one tree, split by whether the plan can name what
/// forcing the captured thunk will run. See [`Captures`].
fn captures(
    functions: &[TypedCoreFn],
    genuine: &BTreeSet<Sym>,
    escaping: &BTreeSet<Sym>,
    latent: &Latent,
) -> Captures {
    let mut out = Captures::default();
    for function in functions {
        let mut thunks = Vec::new();
        thunks_in_comp(function.body(), &mut thunks);
        thunks.retain(|body| performs_when_forced(body, genuine));
        if thunks.is_empty() {
            continue;
        }
        let name = function.name();
        // A thunk over anything but a lambda has no signature to thread, so one
        // of those is enough to make every capture in this body unnameable. So
        // is one the convention predicate reports as pure while the capture
        // fact reports it as effectful: what a confined region would do with
        // that thunk is copy it verbatim, effect nodes and all.
        let tracked = !escaping.contains(&name)
            && thunks
                .iter()
                .all(|body| matches!(body.kind(), TypedCompKind::Lam(..)))
            && thunks.iter().all(|body| body_is_monadic(body, latent))
            && !captures_out_of_reach(function.body(), genuine);
        if tracked {
            out.tracked.insert(name);
        } else {
            out.opaque.insert(name);
        }
        out.all.insert(name);
    }
    out
}

/// Whether forcing this thunk body would still perform an operation: it calls a
/// function that does, or a source effect node survives inside it.
fn performs_when_forced(comp: &TypedComp, genuine: &BTreeSet<Sym>) -> bool {
    calls_any(comp, genuine) || raw_effects(comp)
}

/// Whether a value stands for a computation the free-monad convention owns.
///
/// Forcing it can still perform an operation, so its body must be built by the
/// monadic builder and every force of it must sit in a monadic context.
///
/// This is the *one* convention predicate. The producer asks it of a thunk it
/// is about to rewrite and the consumer asks it of the value it is about to
/// force, both against the same in-scope signatures, because a thunk built at
/// one convention and forced at the other is a silently wrong lowering that no
/// later phase can see: a thunk's convention has no type-level carrier, so the
/// representation retag every crossing goes through accepts it unconditionally.
///
/// Two questions are deliberately not the same one. This predicate asks what
/// forcing a thunk *performs*; the private measure the capture survey in this
/// module runs on asks whether the thunk holds an effectful computation at all,
/// and is true where this one is false for a thunk whose body still holds a
/// closed `handle` or an inert `mask`. That gap matters because the direct
/// builder copies a thunk it is told is pure verbatim, source effect nodes and
/// all, so a capture this predicate cannot see is recorded as an opaque one,
/// and an opaque capture still widens the region.
#[must_use]
pub fn thunk_is_monadic(value: &TypedValue, scope: &flow::Loc, latent: &Latent) -> bool {
    !flow::value_sig(value, scope, latent).is_empty()
}

/// [`thunk_is_monadic`] asked of a thunk's body rather than of the value the
/// thunk stands in.
#[must_use]
pub fn body_is_monadic(body: &TypedComp, latent: &Latent) -> bool {
    !flow::body_sig(body, latent).is_empty()
}

/// Whether any effectful thunk in `comp` stands where nothing carries its
/// signature: in a field of an aggregate, which a later `case` extracts without
/// the flow following it, or in an argument of a value application or an
/// operation, whose callee is not a statically known function.
///
/// This is the same condition [`flow::escaping_fns`] reports, asked of the
/// thunks a capture is measured by rather than of the latent map, so a thunk
/// whose own handler discharges everything it performs is still seen as the
/// first-class computation it is.
fn captures_out_of_reach(comp: &TypedComp, genuine: &BTreeSet<Sym>) -> bool {
    let dynamic = matches!(
        comp.kind(),
        TypedCompKind::App { .. } | TypedCompKind::Do { .. }
    );
    let mut found = false;
    each_value(comp, &mut |value| {
        found |= effectful_thunk(value, genuine) && (dynamic || !is_thunk(value));
    });
    each_subterm(comp, &mut |child| {
        found |= captures_out_of_reach(child, genuine);
    });
    found
}

// Whether a value holds a thunk, at any aggregate depth, that still performs an
// operation when forced.
fn effectful_thunk(value: &TypedValue, genuine: &BTreeSet<Sym>) -> bool {
    let mut thunks = Vec::new();
    top_thunks_in_value(value, &mut thunks);
    thunks
        .iter()
        .any(|body| performs_when_forced(body, genuine))
}

/// The functions that still perform an operation, read off the latent map.
#[must_use]
pub fn genuine_effects(latent: &Latent) -> BTreeSet<Sym> {
    latent
        .iter()
        .filter_map(|(name, operations)| (!operations.is_empty()).then_some(*name))
        .collect()
}

/// Whether any source effect node (`do`, `handle`, `mask`) survives anywhere in
/// `comp`, including inside thunks and inside boxed or unboxed aggregate
/// fields.
///
/// Representation wrappers are transparent to this shape query.
#[must_use]
pub fn raw_effects(comp: &TypedComp) -> bool {
    any_comp(comp, |node| {
        matches!(
            node.kind(),
            TypedCompKind::Do { .. } | TypedCompKind::Handle { .. } | TypedCompKind::Mask(..)
        )
    })
}

/// Whether a handler under `comp` resumes from inside a thunk while its action
/// still has an escaping operation.
///
/// The resumption outlives the clause, so no erasure and no confined region may
/// assume it runs once.
#[must_use]
pub fn open_resume_escapes(comp: &TypedComp, latent: &Latent) -> bool {
    if let TypedCompKind::Handle { body, ops, .. } = comp.kind() {
        // Measured on the handled action's residue alone, not the clause and
        // return contributions `handle_escapes` folds in for planning.
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
    each_subcomp(comp, &mut |child| {
        found |= open_resume_escapes(child, latent);
    });
    found
}

/// Every function `comp` calls by name, descending through thunks.
pub fn collect_calls(comp: &TypedComp, out: &mut BTreeSet<Sym>) {
    out.extend(calls_in(comp));
}

fn calls_any(comp: &TypedComp, names: &BTreeSet<Sym>) -> bool {
    any_comp(
        comp,
        |node| matches!(node.kind(), TypedCompKind::Call { callee, .. } if names.contains(callee)),
    )
}

// Whether `comp` applies a value rather than calling a name, so what runs is
// decided by whatever thunk flowed to that position.
fn applies_value(comp: &TypedComp) -> bool {
    any_comp(comp, |node| {
        matches!(node.kind(), TypedCompKind::App { .. })
    })
}

fn any_comp(comp: &TypedComp, predicate: impl FnMut(&TypedComp) -> bool) -> bool {
    struct AnyComp<F> {
        predicate: F,
        found: bool,
    }

    impl<F: FnMut(&TypedComp) -> bool> Visit for AnyComp<F> {
        fn comp(&mut self, comp: &TypedComp) -> bool {
            self.found |= (self.predicate)(comp);
            !self.found
        }

        fn value(&mut self, _value: &TypedValue) -> bool {
            !self.found
        }
    }

    let mut query = AnyComp {
        predicate,
        found: false,
    };
    query.walk_comp(comp);
    query.found
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use prism_syntax::names::ENTRY_POINT;

    use crate::core::typed::{
        CompSig, CoreFnSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
        TypedValue, TypedValueKind,
    };
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::super::analysis::{plan, MonadicScope};
    use super::*;

    const ASK: &str = "Ask.ask";
    const EFFECT: &str = "Ask";
    const DEEP_QUERY_COMP_COUNT: usize = 50_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn main_name() -> Sym {
        Sym::from(ENTRY_POINT)
    }

    fn function(body: &TypedComp) -> TypedCoreFn {
        let signature = CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone());
        TypedCoreFn::new(main_name(), Vec::new(), body.clone(), signature, 0)
    }

    #[test]
    fn whole_tree_queries_handle_deep_terms_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-effect-plan-queries".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let target = Sym::new("deep.target");
                let call = TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    TypedCompKind::Call {
                        callee: target,
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                );
                let applied = applied(lambda(performed()));
                let mut body = TypedComp::new(
                    applied.sig().clone(),
                    TypedCompKind::Bind(Box::new(call), unit_binder("called"), Box::new(applied)),
                );
                for _ in 0..DEEP_QUERY_COMP_COUNT {
                    let sig = body.sig().clone();
                    let prefix = returning(TypedValue::new(
                        CoreType::Source(Type::Unit),
                        TypedValueKind::Unit,
                    ));
                    body = TypedComp::new(
                        sig,
                        TypedCompKind::Bind(
                            Box::new(prefix),
                            unit_binder("ignored"),
                            Box::new(body),
                        ),
                    );
                }

                assert!(raw_effects(&body));
                assert!(calls_any(&body, &BTreeSet::from([target])));
                assert!(applies_value(&body));
                let mut calls = BTreeSet::new();
                collect_calls(&body, &mut calls);
                assert_eq!(calls, BTreeSet::from([target]));
                mem::forget(body);
            })
            .expect("spawn deep effect-plan query test")
            .join()
            .expect("deep effect-plan query test panicked");
    }

    // `do Ask.ask`, the operation whose presence makes a thunk effectful.
    fn performed() -> TypedComp {
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton(EFFECT)),
            TypedCompKind::Do {
                operation: Sym::from(ASK),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        )
    }

    // `mask Ask { () }`: a source effect node whose evaluation performs nothing,
    // so the latent map is empty where the capture fact is not.
    fn masked() -> TypedComp {
        let inert = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                CoreType::Source(Type::Unit),
                TypedValueKind::Unit,
            )),
        );
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::Mask(vec![Sym::from(EFFECT)], Box::new(inert)),
        )
    }

    fn unit_binder(name: &str) -> TypedBinder {
        TypedBinder::new(Sym::from(name), CoreType::Source(Type::Unit))
    }

    // A thunk over a lambda: the one shape a thunk signature describes.
    fn lambda(body: TypedComp) -> TypedValue {
        let parameter = unit_binder("ignored");
        let signature =
            CoreFnSig::new(Vec::new(), vec![parameter.ty().clone()], body.sig().clone());
        let lam = TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
            TypedCompKind::Lam(vec![parameter], Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lam.sig().clone())),
            TypedValueKind::Thunk(Box::new(lam)),
        )
    }

    // The same thunk as one field of a constructor, where nothing names it until
    // a later `case` extracts it.
    fn boxed(value: TypedValue) -> TypedValue {
        TypedValue::new(
            CoreType::Source(Type::Int),
            TypedValueKind::Ctor {
                name: Sym::from("Susp"),
                tag: 0,
                instantiation: Vec::new(),
                fields: vec![value],
            },
        )
    }

    fn returning(value: TypedValue) -> TypedComp {
        TypedComp::new(
            CompSig::new(value.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(value),
        )
    }

    // The thunk handed to a value application, whose callee is decided by
    // whatever flowed to it rather than by a name.
    fn applied(argument: TypedValue) -> TypedComp {
        let signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Unit)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let function_ty = CoreType::Function(Box::new(signature));
        let callee = TypedComp::new(
            CompSig::new(function_ty.clone(), EffRow::Empty),
            TypedCompKind::Force(TypedValue::new(
                CoreType::Thunk(Box::new(CompSig::new(function_ty, EffRow::Empty))),
                TypedValueKind::Var {
                    name: Sym::from("dispatch"),
                    instantiation: Vec::new(),
                },
            )),
        );
        TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(callee),
                instantiation: Vec::new(),
                args: vec![argument],
            },
        )
    }

    // The capture fact as one undivided set, spelled out independently of the
    // split: every function whose body builds a thunk that still performs
    // something. The two halves must partition exactly this.
    fn capturers(functions: &[TypedCoreFn], effects: &EffectPlan) -> BTreeSet<Sym> {
        functions
            .iter()
            .filter(|function| {
                let mut thunks = Vec::new();
                thunks_in_comp(function.body(), &mut thunks);
                thunks
                    .iter()
                    .any(|body| calls_any(body, effects.genuine()) || raw_effects(body))
            })
            .map(TypedCoreFn::name)
            .collect()
    }

    // Every case checks the same two invariants before its own: the halves are
    // disjoint, and their union is the fact the split replaced.
    fn analyzed(functions: &[TypedCoreFn]) -> EffectPlan {
        let effects = EffectPlan::analyze(functions);
        assert!(
            effects
                .tracked_captures()
                .is_disjoint(effects.opaque_captures()),
            "a capture is tracked or opaque, never both"
        );
        let union: BTreeSet<Sym> = effects
            .tracked_captures()
            .union(effects.opaque_captures())
            .copied()
            .collect();
        assert_eq!(
            &union,
            effects.thunk_effects(),
            "the split loses no capture"
        );
        assert_eq!(
            effects.thunk_effects(),
            &capturers(functions, &effects),
            "the union is the undivided capture fact"
        );
        effects
    }

    fn scope(functions: &[TypedCoreFn], effects: &EffectPlan) -> MonadicScope {
        plan(functions, effects, false).scope
    }

    #[test]
    fn a_thunked_lambda_is_a_tracked_capture() {
        let functions = vec![function(&returning(lambda(performed())))];
        let effects = analyzed(&functions);
        assert_eq!(effects.tracked_captures(), &BTreeSet::from([main_name()]));
        assert!(effects.opaque_captures().is_empty());
        // A capture the thunk signatures describe no longer widens the region.
        // The computation the thunk holds is built by the monadic builder and
        // reached through the thunk, so the function that built it is not
        // swallowed by the region for having built it.
        assert_eq!(scope(&functions, &effects), MonadicScope::Selective);
    }

    #[test]
    fn a_thunk_buried_in_a_constructor_is_an_opaque_capture() {
        let functions = vec![function(&returning(boxed(lambda(performed()))))];
        let effects = analyzed(&functions);
        assert_eq!(effects.opaque_captures(), &BTreeSet::from([main_name()]));
        assert!(effects.tracked_captures().is_empty());
        assert_eq!(scope(&functions, &effects), MonadicScope::WholeProgram);
    }

    #[test]
    fn a_thunk_handed_to_a_value_application_is_an_opaque_capture() {
        let functions = vec![function(&applied(lambda(performed())))];
        let effects = analyzed(&functions);
        assert_eq!(effects.escaping(), &BTreeSet::from([main_name()]));
        assert_eq!(effects.opaque_captures(), &BTreeSet::from([main_name()]));
        assert!(effects.tracked_captures().is_empty());
        assert_eq!(scope(&functions, &effects), MonadicScope::WholeProgram);
    }

    // The residue the escape analysis alone cannot see: a captured thunk whose
    // own evaluation performs nothing latent is still a first-class computation,
    // and burying it still leaves the plan with nothing to name it by.
    #[test]
    fn a_buried_capture_is_opaque_even_with_an_empty_latent_set() {
        let functions = vec![function(&returning(boxed(lambda(masked()))))];
        let effects = analyzed(&functions);
        assert!(
            effects.escaping().is_empty(),
            "nothing latent escapes, so the escape analysis is silent here"
        );
        assert_eq!(effects.opaque_captures(), &BTreeSet::from([main_name()]));
        assert!(effects.tracked_captures().is_empty());
        assert_eq!(scope(&functions, &effects), MonadicScope::WholeProgram);
    }
}
