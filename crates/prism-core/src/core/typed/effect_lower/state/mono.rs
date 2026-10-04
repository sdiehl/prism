//! One instance per label set for a row-polymorphic carrier.
//!
//! A function that takes effect-performing thunks *inside data* is declared
//! once and instantiated wherever it is called. The arrow buried in that data
//! ends in a bare row variable at the declaration, so the declaration alone
//! cannot say whether those thunks perform an operation the caller's handler
//! answers by parameter passing: only the instantiation does. Threading an
//! accumulator through such a thunk changes its arity, so a single declaration
//! cannot serve both a call whose thunks thread and a call whose thunks do not.
//!
//! Pushing the row a call site names into the callee's own scheme settles that
//! at the declaration. Only a row the caller has closed is pushed: an open one
//! leaves the same question one level up, and the widening that follows reads a
//! closed row as the whole of what a stored thunk performs. The quantifier goes
//! with it, so a callee whose call sites name different rows becomes one
//! monomorphic instance per row, each with the type its call site already had.
//!
//! A parameter that *is* an arrow stays alone. It is an ordinary callback,
//! passed and called in place rather than stored, so nothing about it has to be
//! settled before the call. Only an arrow reached through a constructor travels
//! inside data, and only that one is treated as a carrier here.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::super::specialize_support::{substitute_witnesses, Rewrite};
use super::super::super::traverse::Visit;
use super::super::super::verify::{substitute_core_type, substitute_sig};
use super::super::super::{CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType};
use super::super::{
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind,
};

/// The instance budget. A call whose instantiation *grows* the row it passes
/// would request a fresh instance forever, so past this many the pass reports
/// no rewrite at all and the program lowers exactly as it stood.
const MAX_INSTANCES: usize = 64;

/// One closed row pushed into one row quantifier: its position in the callee's
/// scheme, the name it binds, and the row moving inward.
type Push = (usize, Sym, EffRow);

/// The instance key: a callee together with the rows its call site pushes,
/// spelled so that two call sites naming the same rows share one instance.
type Key = (Sym, Vec<(usize, Vec<String>)>);

/// Instantiate every row-polymorphic carrier against the labels its call sites
/// name. `None` when no call site names any, and when the budget runs out.
#[must_use]
pub fn instantiate_carriers(fns: &[TypedCoreFn]) -> Option<Vec<TypedCoreFn>> {
    let mut pass = Instances {
        originals: fns.iter().map(|f| (f.name(), f.clone())).collect(),
        memo: BTreeMap::new(),
        built: Vec::new(),
        sources: BTreeSet::new(),
        exhausted: false,
    };
    let rewritten: Vec<TypedCoreFn> = fns.iter().map(|f| pass.function(f, &())).collect();
    if pass.exhausted || pass.built.is_empty() {
        return None;
    }
    let sources = pass.sources;
    let mut all: Vec<TypedCoreFn> = rewritten.into_iter().chain(pass.built).collect();
    // A declaration every call site instantiated is dead now, and a dead
    // declaration still carries the polymorphic carrier the instances exist to
    // settle. Dropping it is what lets the gates below see one shape.
    let live = reachable(&all);
    all.retain(|f| !sources.contains(&f.name()) || live.contains(&f.name()));
    Some(all)
}

/// The declarations the entry point still reaches, over direct calls and
/// first-class references to top-level names. A declaration every call site
/// instantiated stays out even though its own body still calls it.
fn reachable(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    struct Names(BTreeSet<Sym>);
    impl Visit for Names {
        fn comp(&mut self, comp: &TypedComp) -> bool {
            if let TypedCompKind::Call { callee, .. } = comp.kind() {
                self.0.insert(*callee);
            }
            true
        }

        fn value(&mut self, value: &TypedValue) -> bool {
            if let TypedValueKind::Var { name, .. } = value.kind() {
                self.0.insert(*name);
            }
            true
        }
    }
    let by_name: BTreeMap<Sym, &TypedCoreFn> = fns.iter().map(|f| (f.name(), f)).collect();
    let mut visited = BTreeSet::new();
    let mut queue = vec![Sym::new(names::ENTRY_POINT)];
    while let Some(name) = queue.pop() {
        if !visited.insert(name) {
            continue;
        }
        if let Some(function) = by_name.get(&name) {
            let mut found = Names(BTreeSet::new());
            found.walk_comp(function.body());
            queue.extend(found.0.into_iter().filter(|n| by_name.contains_key(n)));
        }
    }
    visited
}

struct Instances {
    originals: BTreeMap<Sym, TypedCoreFn>,
    memo: BTreeMap<Key, Sym>,
    built: Vec<TypedCoreFn>,
    /// The declarations instances were built from, which may now be dead.
    sources: BTreeSet<Sym>,
    exhausted: bool,
}

impl Rewrite for Instances {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        let TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } = comp.kind()
        else {
            return self.descend_comp(comp, cx);
        };
        let Some((instance, rest)) = self.request(*callee, instantiation) else {
            return self.descend_comp(comp, cx);
        };
        // The call's own signature is untouched: the instance instantiated at
        // the remaining tail has the type the original had at the whole row.
        TypedComp::new(
            comp.sig().clone(),
            TypedCompKind::Call {
                callee: instance,
                instantiation: rest,
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
        )
    }
}

impl Instances {
    /// The instance this call wants, and the instantiation it passes instead.
    fn request(
        &mut self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
    ) -> Option<(Sym, Vec<CoreInstantiation>)> {
        if self.exhausted {
            return None;
        }
        let original = self.originals.get(&callee)?.clone();
        let mut pushed: Vec<Push> = Vec::new();
        for (position, name) in carrier_rows(&original) {
            let Some(CoreInstantiation::Row(row)) = instantiation.get(position) else {
                return None;
            };
            // An open row says the caller has not committed either, so pushing
            // it settles nothing. Leave that position quantified.
            if !matches!(row.tail(), EffRow::Empty) || row.labels().is_empty() {
                continue;
            }
            pushed.push((
                position,
                name,
                EffRow::canonical(row.labels().into_iter().cloned(), EffRow::Empty),
            ));
        }
        if pushed.is_empty() {
            return None;
        }
        let key = (
            callee,
            pushed
                .iter()
                .map(|(position, _, row)| {
                    (
                        *position,
                        row.labels()
                            .into_iter()
                            .map(Label::show)
                            .collect::<Vec<_>>(),
                    )
                })
                .collect(),
        );
        // The pushed rows are the instance's own now, so the call passes only
        // what is still quantified.
        let rest: Vec<CoreInstantiation> = instantiation
            .iter()
            .enumerate()
            .filter(|(position, _)| !pushed.iter().any(|(p, _, _)| p == position))
            .map(|(_, argument)| argument.clone())
            .collect();
        if let Some(instance) = self.memo.get(&key) {
            return Some((*instance, rest));
        }
        if self.built.len() >= MAX_INSTANCES {
            self.exhausted = true;
            return None;
        }
        let instance = Sym::from(&names::carrier_instance(
            callee.as_str(),
            self.memo.len() + 1,
        ));
        // Memoized before the body is rewritten, so a recursive call inside the
        // instance resolves to the instance instead of requesting another.
        self.memo.insert(key, instance);
        self.sources.insert(callee);
        self.build(&original, instance, &pushed);
        Some((instance, rest))
    }

    /// Clone `original` with its carrier rows fixed to the pushed ones.
    fn build(&mut self, original: &TypedCoreFn, instance: Sym, pushed: &[Push]) {
        let (names, arguments): (Vec<_>, Vec<_>) = pushed
            .iter()
            .map(|(_, name, row)| {
                (
                    CoreQuantifier::Row(*name),
                    CoreInstantiation::Row(row.clone()),
                )
            })
            .unzip();
        // A pushed row is no longer a parameter of the instance, so its
        // quantifier goes with it and every call passes one argument fewer.
        let quantifiers: Vec<CoreQuantifier> = original
            .sig()
            .quantifiers()
            .iter()
            .filter(|quantifier| !names.contains(quantifier))
            .cloned()
            .collect();
        let signature = CoreFnSig::new(
            quantifiers,
            original
                .sig()
                .params()
                .iter()
                .map(|ty| substitute_core_type(ty, &names, &arguments))
                .collect(),
            substitute_sig(original.sig().body(), &names, &arguments),
        );
        let params = original
            .params()
            .iter()
            .map(|binder| {
                TypedBinder::new(
                    binder.name(),
                    substitute_core_type(binder.ty(), &names, &arguments),
                )
            })
            .collect();
        let body = substitute_witnesses(original.body(), &names, &arguments);
        let body = self.comp(&body, &());
        self.built.push(TypedCoreFn::new(
            instance,
            params,
            body,
            signature,
            original.dict_arity(),
        ));
    }
}

/// The scheme positions whose row quantifier ends an arrow buried inside a
/// parameter's own type, paired with the name that quantifier binds.
fn carrier_rows(function: &TypedCoreFn) -> Vec<(usize, Sym)> {
    let signature = function.sig();
    signature
        .quantifiers()
        .iter()
        .enumerate()
        .filter_map(|(position, quantifier)| {
            let CoreQuantifier::Row(name) = quantifier else {
                return None;
            };
            signature
                .params()
                .iter()
                .any(|ty| buries_row(ty, *name))
                .then_some((position, *name))
        })
        .collect()
}

/// Whether `name` ends the row of an arrow strictly inside this parameter's
/// type, which is what makes the parameter a carrier rather than a callback.
fn buries_row(ty: &CoreType, name: Sym) -> bool {
    let CoreType::Source(source) = ty else {
        return false;
    };
    let mut found = false;
    source.each_child(&mut |child| ends_an_arrow(child, name, &mut found));
    found
}

fn ends_an_arrow(ty: &Type, name: Sym, found: &mut bool) {
    if *found {
        return;
    }
    if let Type::Fun(_, row, _) = ty {
        if matches!(row.tail(), EffRow::Var(tail) if *tail == name) {
            *found = true;
            return;
        }
    }
    ty.each_child(&mut |child| ends_an_arrow(child, name, found));
}
