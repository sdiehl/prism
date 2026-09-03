//! The callable allocation-certificate drive.
//!
//! A parameter typed `((..) -> ..) @ noalloc` demands that every value
//! supplied for it carries a whole-call-tree allocation certificate. The
//! demand is proved at call sites, on the pre-optimizer typed core, so the
//! verdict never depends on which lowering tier or optimization level fires:
//!
//! - A named top-level function satisfies the demand when its declaration
//!   carries a zero allocation budget (`fip`, `fbip`, or the standalone
//!   `@ noalloc` row, all of which the allocation drive re-checks on the
//!   compiled term), or when its interprocedural summary proves a zero
//!   allocation bound with no callable slots of its own (a summary's bound is
//!   conditional on its callback slots, so an empty slot set closes it).
//! - A variable naming one of the enclosing function's own certified
//!   parameters passes the fact through unchanged: a generic wrapper keeps a
//!   callable's certificate without being inlined.
//! - Everything else (a literal closure, a partial application, a value the
//!   eta-wrapper identity cannot name) is conservatively rejected: forgetting
//!   the fact is free, but an unproven value never flows into a demanding
//!   slot.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::ast::{Core as CorePhase, Fip, Program, Ty};
use prism_syntax::coeffect::CoeffectFact;
use prism_syntax::kw::AT;

use super::check::{ClaimError, ClaimErrorKind, ClaimOrigin, Fips};
use crate::core::typed::specialize::{callable_identity, peel_coercions};
use crate::core::typed::summary::{summarize, AllocBound, FunctionSummary};
use crate::core::typed::traverse::Visit;
use crate::core::typed::{
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind,
};

/// The `@ noalloc` demands on function-typed parameters.
///
/// Demands are keyed by declaring function and retain the source-parameter
/// position and name. The call-site drive uses the positions; the allocation
/// drive uses the names to accept indirect calls through certified parameters.
#[derive(Debug)]
pub struct CallableRequirements {
    slots: BTreeMap<Sym, Vec<(usize, Sym)>>,
}

impl CallableRequirements {
    /// No function in the program demands a callable certificate.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// The certified parameter names of each demanding function, the form the
    /// allocation drive consumes.
    #[must_use]
    pub fn certified_params(&self) -> BTreeMap<Sym, BTreeSet<Sym>> {
        self.slots
            .iter()
            .map(|(f, slots)| (*f, slots.iter().map(|(_, name)| *name).collect()))
            .collect()
    }
}

/// Collect every function-typed parameter whose written type carries `noalloc`.
///
/// Slot positions index the source parameter list; the typed call-site drive
/// shifts them past the callee's leading dictionaries.
#[must_use]
pub fn callable_requirements(prog: &Program<CorePhase>) -> CallableRequirements {
    let slots = prog
        .fns
        .iter()
        .filter_map(|d| {
            let demands: Vec<(usize, Sym)> = d
                .params
                .iter()
                .enumerate()
                .filter(|(_, p)| {
                    matches!(&p.ty, Some(Ty::Coeffect(inner, row))
                        if matches!(**inner, Ty::Fun(..)) && row.has_noalloc())
                })
                .map(|(i, p)| (i, Sym::new(&p.name)))
                .collect();
            (!demands.is_empty()).then(|| (Sym::new(&d.name), demands))
        })
        .collect();
    CallableRequirements { slots }
}

/// Prove every value that flows into a demanding slot.
///
/// This runs over the pre-optimizer typed core so acceptance is a property of
/// the source program, and consumes interprocedural summaries rather than
/// walking the call graph itself.
///
/// # Errors
/// Returns the first callable flow whose allocation certificate cannot be
/// proved.
pub fn check_callable_flow(
    functions: &[TypedCoreFn],
    reqs: &CallableRequirements,
    fips: &Fips,
) -> Result<(), ClaimError> {
    if reqs.is_empty() {
        return Ok(());
    }
    let summaries = summarize(functions);
    let dict_arities: BTreeMap<Sym, usize> = functions
        .iter()
        .map(|f| (f.name(), f.dict_arity()))
        .collect();
    let known: BTreeSet<Sym> = functions.iter().map(TypedCoreFn::name).collect();
    for f in functions {
        let certified: BTreeSet<Sym> = reqs
            .slots
            .get(&f.name())
            .map(|slots| slots.iter().map(|(_, name)| *name).collect())
            .unwrap_or_default();
        let mut flow = Flow {
            reqs,
            fips,
            summaries: &summaries,
            dict_arities: &dict_arities,
            known: &known,
            fname: f.name(),
            certified,
            scope_depth: 0,
            shadowed: BTreeMap::new(),
            locals: BTreeMap::new(),
            pending: BTreeMap::new(),
            failure: None,
        };
        flow.walk_function(f);
        if let Some(failure) = flow.failure {
            return Err(failure);
        }
    }
    Ok(())
}

// The named function a lambda eta-wraps. The direct shape is delegated to
// `callable_identity`; a source-written wrapper additionally carries the
// rename binds elaboration inserts (`return p to t` ahead of the call), so
// this reader follows pure variable renames down to the call and checks the
// same saturation and argument-order conditions through the rename map. It
// reads renames only, never a second identity notion.
fn eta_callee(value: &TypedValue) -> Option<Sym> {
    if let Some(target) = callable_identity(value) {
        return Some(target);
    }
    let TypedValueKind::Thunk(lambda) = peel_coercions(value).kind() else {
        return None;
    };
    let TypedCompKind::Lam(params, inner) = lambda.kind() else {
        return None;
    };
    let mut renames: BTreeMap<Sym, Sym> = params.iter().map(|p| (p.name(), p.name())).collect();
    let mut body: &TypedComp = inner;
    loop {
        match body.kind() {
            TypedCompKind::Bind(first, binder, rest) => {
                let TypedCompKind::Return(v) = first.kind() else {
                    return None;
                };
                let TypedValueKind::Var {
                    name,
                    instantiation,
                } = peel_coercions(v).kind()
                else {
                    return None;
                };
                if !instantiation.is_empty() {
                    return None;
                }
                let target = *renames.get(name)?;
                renames.insert(binder.name(), target);
                body = rest;
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                if !instantiation.is_empty() || args.len() != params.len() {
                    return None;
                }
                for (argument, param) in args.iter().zip(params) {
                    let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = argument.kind()
                    else {
                        return None;
                    };
                    if !instantiation.is_empty() || renames.get(name) != Some(&param.name()) {
                        return None;
                    }
                }
                return Some(*callee);
            }
            _ => return None,
        }
    }
}

// What the drive knows about one callable value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Evidence {
    // The value is an unshadowed occurrence of one of the enclosing
    // function's own certified parameters.
    Certified,
    // The value names this top-level function (directly, through an
    // eta-wrapper, or through a local alias chain).
    Named(Sym),
    // Nothing traceable; conservatively rejected at a demanding slot.
    Opaque,
}

// One function's call-site walk. Scope depth 0 is the function's own
// parameter scope; a deeper scope rebinding a certified name suspends its
// certificate for exactly the extent of that scope, so the pass-through rule
// only ever fires on occurrences that really refer to the parameter.
//
// Elaboration ANF-binds call arguments, so a demanded slot usually receives a
// local temporary rather than the callable itself. `locals` carries the
// evidence a pure `let x = v` establishes for `x`; the resolution happens at
// the bind (where the bound value's own scope is current) but is applied only
// when the binder's scope is entered, so an occurrence of the same name
// inside the bound computation still reads the outer state. Exiting a scope
// drops its binders' entries without restoring an outer one, which can only
// lose evidence, never invent it.
struct Flow<'a> {
    reqs: &'a CallableRequirements,
    fips: &'a Fips,
    summaries: &'a BTreeMap<Sym, FunctionSummary>,
    dict_arities: &'a BTreeMap<Sym, usize>,
    known: &'a BTreeSet<Sym>,
    fname: Sym,
    certified: BTreeSet<Sym>,
    scope_depth: usize,
    shadowed: BTreeMap<Sym, usize>,
    locals: BTreeMap<Sym, Evidence>,
    pending: BTreeMap<Sym, Evidence>,
    failure: Option<ClaimError>,
}

impl Flow<'_> {
    fn fail(&mut self, kind: ClaimErrorKind) {
        if self.failure.is_none() {
            self.failure = Some(ClaimError {
                fname: self.fname,
                spelled: format!("{AT} {}", CoeffectFact::Noalloc),
                origin: ClaimOrigin::RowClaim,
                kind: Box::new(kind),
            });
        }
    }

    // Whether an unshadowed occurrence of `name` refers to one of the walked
    // function's own certified parameters.
    fn certified_here(&self, name: Sym) -> bool {
        self.certified.contains(&name) && self.shadowed.get(&name).copied().unwrap_or(0) == 0
    }

    // What one callable value is known to be, in the current scope.
    fn resolve(&self, value: &TypedValue) -> Evidence {
        if let TypedValueKind::Var { name, .. } = peel_coercions(value).kind() {
            if self.certified_here(*name) {
                return Evidence::Certified;
            }
            if self.known.contains(name) {
                return Evidence::Named(*name);
            }
            return self.locals.get(name).copied().unwrap_or(Evidence::Opaque);
        }
        eta_callee(value).map_or(Evidence::Opaque, Evidence::Named)
    }

    // Whether the named top-level function carries a whole-call-tree
    // allocation certificate. Declared zero budgets are accepted alongside
    // summary proofs because the summary is computed before reuse lowering:
    // an in-place (`fip`) body summarizes as allocating yet passes the
    // compiled-term allocation drive once reuse tokens land.
    fn certificate_ok(&self, target: Sym) -> bool {
        matches!(self.fips.get(&target), Some(Fip::Fip(0) | Fip::Fbip(0)))
            || self
                .summaries
                .get(&target)
                .is_some_and(|s| s.allocation == AllocBound::Zero && s.callbacks.is_empty())
    }

    fn check_call(&mut self, callee: Sym, args: &[TypedValue]) {
        let Some(demands) = self.reqs.slots.get(&callee) else {
            return;
        };
        let dict_arity = self.dict_arities.get(&callee).copied().unwrap_or(0);
        for (slot, slot_name) in demands.clone() {
            let Some(arg) = args.get(dict_arity + slot) else {
                // An unsaturated call defers the flow to whoever finally
                // applies it; the value it builds is opaque here.
                self.fail(ClaimErrorKind::CallableOpaque {
                    callee,
                    slot: slot_name,
                });
                continue;
            };
            match self.resolve(arg) {
                Evidence::Certified => {}
                Evidence::Named(target) if self.certificate_ok(target) => {}
                Evidence::Named(target) => self.fail(ClaimErrorKind::CallableUncertified {
                    supplied: target,
                    callee,
                    slot: slot_name,
                }),
                Evidence::Opaque => self.fail(ClaimErrorKind::CallableOpaque {
                    callee,
                    slot: slot_name,
                }),
            }
        }
    }
}

impl Visit for Flow<'_> {
    fn enter_scope(&mut self, binders: &[&TypedBinder]) {
        if self.scope_depth > 0 {
            for b in binders {
                if self.certified.contains(&b.name()) {
                    *self.shadowed.entry(b.name()).or_default() += 1;
                }
            }
        }
        for b in binders {
            match self.pending.remove(&b.name()) {
                Some(ev) => {
                    self.locals.insert(b.name(), ev);
                }
                None => {
                    // A rebinding wipes any evidence the outer scope held for
                    // the name; dropping is the conservative direction.
                    self.locals.remove(&b.name());
                }
            }
        }
        self.scope_depth += 1;
    }

    fn exit_scope(&mut self, binders: &[&TypedBinder]) {
        self.scope_depth -= 1;
        if self.scope_depth > 0 {
            for b in binders {
                if self.certified.contains(&b.name()) {
                    if let Some(count) = self.shadowed.get_mut(&b.name()) {
                        *count = count.saturating_sub(1);
                    }
                }
                self.locals.remove(&b.name());
            }
        }
    }

    fn comp(&mut self, comp: &TypedComp) -> bool {
        if self.failure.is_some() {
            return false;
        }
        match comp.kind() {
            TypedCompKind::Call { callee, args, .. } => self.check_call(*callee, args),
            // A pure `let x = v` establishes evidence for `x`; resolve now,
            // while the bound value's own scope is current, and let
            // `enter_scope` apply it when the binder comes into scope.
            TypedCompKind::Bind(first, binder, _) => {
                if let TypedCompKind::Return(value) = first.kind() {
                    let ev = self.resolve(value);
                    if ev != Evidence::Opaque {
                        self.pending.insert(binder.name(), ev);
                    }
                }
            }
            _ => {}
        }
        true
    }
}
