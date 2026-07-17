//! Typed erasure of escape-checked local `var` state to mutable cells.
//!
//! Recognizes the closed var/State handler shape the desugar emits
//! (`Bind(handle BODY with {get@x@n, set@x@n}, run@n, run@n(init))`, a
//! triple-match on the unforgeable op/runner names), and rewrite it to a
//! mutable cell: `get` becomes `RefGet`, `set` becomes `RefSet`, and the block
//! is wrapped in `RefNew(init)` under a fresh `{n}@cell` binder. A function is
//! erased only when no genuinely multishot op is reachable from it
//! (transitively over calls and thunks), with an op's declared grade capping
//! the classification.
//!
//! The typed-specific step is effect-row discharge: the handler this pass
//! removes was the proof that the private `Var@x@n` effect never escaped, so
//! every sig in the rewritten region has that one label subtracted from its
//! row (rows are unions of leaf rows, so uniform label removal is exactly the
//! recomputation), and the rewritten `RefGet`/`RefSet` leaves carry the empty
//! row their verified construction rules demand. Multishot facts come from the
//! canonical [`crate::core::cbpv::CheckedHandler`] classification, recomputed
//! on an erased clone of each typed handler.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::OpGrades;
use crate::fixpoint::least_fixpoint;
use crate::fresh::Fresh;
use crate::names;
use crate::sym::Sym;
use crate::syntax::ast::Grade;
use crate::types::ty::EffRow;

use super::super::inline::calls_in;
use super::super::specialize_support::Rewrite;
use super::super::verify::VerifyEnv;
use super::super::{
    CompSig, CoreInstantiation, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
    TypedHandleOp, TypedValue,
};
use super::subtract::SubtractEffect;
use super::walk::{collect_ops, each_subterm};
use super::{as_var, binder_var, union_effects, unit_value};

/// Rewrite closed local `var`/State handlers to mutable-cell ops, per
/// function, leaving any function from which a genuinely multishot op is
/// reachable untouched (the cell would share state across resumptions that
/// pure State keeps independent).
pub(super) fn erase_local_vars(
    fns: &[TypedCoreFn],
    grades: &OpGrades,
    env: &VerifyEnv,
) -> Vec<TypedCoreFn> {
    let multishot = multishot_ops(fns, grades);
    // No genuinely multishot handler anywhere: every var is safe to erase.
    // This common path computes no reachability.
    let unsafe_fns: BTreeSet<Sym> = if multishot.is_empty() {
        BTreeSet::new()
    } else {
        let reach = reach_map(fns);
        fns.iter()
            .filter(|f| reach[&f.name()].intersection(&multishot).next().is_some())
            .map(TypedCoreFn::name)
            .collect()
    };
    let mut eraser = Eraser {
        fresh: Fresh::new(),
        env,
        discharged: BTreeSet::new(),
    };
    let mut rewritten: Vec<TypedCoreFn> = fns
        .iter()
        .map(|f| {
            if unsafe_fns.contains(&f.name()) {
                f.clone()
            } else {
                TypedCoreFn::new(
                    f.name(),
                    f.params().to_vec(),
                    eraser.comp(f.body(), &()),
                    f.sig().clone(),
                    f.dict_arity(),
                )
            }
        })
        .collect();
    for label in eraser.discharged {
        let mut rows = SubtractEffect { label };
        rewritten = rewritten
            .iter()
            .map(|function| rows.function(function, &()))
            .collect();
    }
    rewritten
}

// Ops with a genuinely multishot handler somewhere in the program. The
// classification is the canonical stored fact `CheckedHandler::new` computes
// from the clause bodies; erasing a clone of the typed handler recomputes it
// through that one constructor. An op graded at most `One` can never resume
// more than once, so it is excluded, and the two facts must agree.
fn multishot_ops(fns: &[TypedCoreFn], grades: &OpGrades) -> BTreeSet<Sym> {
    let mut out = BTreeSet::new();
    for f in fns {
        collect_multishot(f.body(), grades, &mut out);
    }
    out
}

fn collect_multishot(c: &TypedComp, grades: &OpGrades, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Handle { ops, .. } = c.kind() {
        let checked = ops.clone().erase();
        for (op, ru) in checked.iter_with_use() {
            match grades.get(&op.name) {
                Some(g) if *g <= Grade::Once => debug_assert!(
                    !ru.multishot,
                    "op `{}` declared grade {:?} but its clause classifies as multishot; \
                     the desugar grade check should have rejected it",
                    op.name, g
                ),
                _ if ru.multishot => {
                    out.insert(op.name);
                }
                _ => {}
            }
        }
    }
    each_subterm(c, &mut |sc| collect_multishot(sc, grades, out));
}

// Every op each function can perform or handle, transitively over calls and
// thunks: the least fixpoint of `own_ops(f) union reach(callee)` over the call
// graph. `collect_ops` and `calls_in` both descend thunks.
fn reach_map(fns: &[TypedCoreFn]) -> BTreeMap<Sym, BTreeSet<Sym>> {
    let own: BTreeMap<Sym, BTreeSet<Sym>> = fns
        .iter()
        .map(|f| {
            let mut ops = BTreeSet::new();
            collect_ops(f.body(), &mut ops);
            (f.name(), ops)
        })
        .collect();
    let calls: BTreeMap<Sym, BTreeSet<Sym>> = fns
        .iter()
        .map(|f| (f.name(), calls_in(f.body()).into_iter().collect()))
        .collect();
    let seed: BTreeMap<Sym, BTreeSet<Sym>> =
        fns.iter().map(|f| (f.name(), BTreeSet::new())).collect();
    least_fixpoint(seed, |name, cur| {
        let mut s = own[name].clone();
        for callee in &calls[name] {
            if let Some(r) = cur.get(callee) {
                s.extend(r.iter().copied());
            }
        }
        s
    })
}

struct Eraser<'a> {
    fresh: Fresh,
    env: &'a VerifyEnv,
    discharged: BTreeSet<Sym>,
}

impl Rewrite for Eraser<'_> {
    type Ctx = ();

    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        if let Some(block) = match_var_block(c) {
            // The private effect the removed handler discharged, from the op's
            // declared signature. A verified program always carries it; if it
            // is somehow absent the handler is left for the general lowering
            // (always sound) rather than guessed at.
            if let Some(label) = self.env.operation(block.get).map(|sig| sig.effect().name) {
                self.discharged.insert(label);
                let cell = Sym::from(names::lowered("cell", self.fresh.bump()));
                let init = self.comp(&block.init, &());
                // Erase nested vars in the body first, then this var's own ops.
                let body = self.comp(&block.body, &());
                let init_ty = init.sig().result().clone();
                let cell_binder = TypedBinder::new(cell, CoreType::Ref(Box::new(init_ty)));
                let body = SubtractVar {
                    get: block.get,
                    set: block.set,
                    cell: cell_binder.clone(),
                    rows: SubtractEffect { label },
                }
                .comp(&body, &());
                // run@n(init) threaded the State and discarded it, so the
                // block's value is the body's value; the cell holds the state.
                let refnew = TypedComp::new(
                    CompSig::new(cell_binder.ty().clone(), EffRow::Empty),
                    TypedCompKind::RefNew(binder_var(&block.init_binder)),
                );
                let inner = TypedComp::new(
                    body.sig().clone(),
                    TypedCompKind::Bind(Box::new(refnew), cell_binder, Box::new(body)),
                );
                let outer_sig = CompSig::new(
                    inner.sig().result().clone(),
                    union_effects(init.sig().effects(), inner.sig().effects()),
                );
                return TypedComp::new(
                    outer_sig,
                    TypedCompKind::Bind(Box::new(init), block.init_binder, Box::new(inner)),
                );
            }
        }
        self.descend_comp(c, &())
    }
}

struct VarBlock {
    body: TypedComp,
    get: Sym,
    set: Sym,
    init: TypedComp,
    init_binder: TypedBinder,
}

// Recognize `Bind(handle BODY with {var get/set/return}, run@n, run@n(init))`,
// the fixed shape the var desugar emits. The op names `get@x@n`/`set@x@n` and
// the runner `run@n` must all share the var id `n` (and the get/set the var
// name `x`), a triple-match no construct but the var desugar produces.
fn match_var_block(c: &TypedComp) -> Option<VarBlock> {
    let TypedCompKind::Bind(handle, run_binder, kont) = c.kind() else {
        return None;
    };
    if !names::is_var_runner(run_binder.name().as_str()) {
        return None;
    }
    let TypedCompKind::Handle { body, ops, .. } = handle.kind() else {
        return None;
    };
    let [a, b] = ops.arms() else {
        return None;
    };
    let (get_op, set_op) = order_get_set(a, b)?;
    let (gx, gn) = names::parse_var_get(get_op.name().as_str())?;
    let (sx, sn) = names::parse_var_set(set_op.name().as_str())?;
    let rn = names::parse_var_runner(run_binder.name().as_str())?;
    if gx != sx || gn != sn || gn != rn {
        return None;
    }
    let (init, init_binder) = match_runner_apply(kont, run_binder.name())?;
    Some(VarBlock {
        body: body.as_ref().clone(),
        get: get_op.name(),
        set: set_op.name(),
        init,
        init_binder,
    })
}

fn order_get_set<'a>(
    a: &'a TypedHandleOp,
    b: &'a TypedHandleOp,
) -> Option<(&'a TypedHandleOp, &'a TypedHandleOp)> {
    if names::is_var_get(a.name().as_str()) && names::is_var_set(b.name().as_str()) {
        Some((a, b))
    } else if names::is_var_get(b.name().as_str()) && names::is_var_set(a.name().as_str()) {
        Some((b, a))
    } else {
        None
    }
}

// Peel `Bind(<init>, it, Bind(Return(run_sym), ra, (force ra)(it)))`, returning
// the init computation and its binder.
fn match_runner_apply(kont: &TypedComp, run_sym: Sym) -> Option<(TypedComp, TypedBinder)> {
    let TypedCompKind::Bind(init, it, rest) = kont.kind() else {
        return None;
    };
    let TypedCompKind::Bind(run_bind, ra, app) = rest.kind() else {
        return None;
    };
    // `ra` aliases the runner.
    match run_bind.kind() {
        TypedCompKind::Return(v) if as_var(v) == Some(run_sym) => {}
        _ => return None,
    }
    // `(force ra)(it)`.
    let TypedCompKind::App {
        callee,
        instantiation: _,
        args,
    } = app.kind()
    else {
        return None;
    };
    let TypedCompKind::Force(fa) = callee.kind() else {
        return None;
    };
    if as_var(fa) != Some(ra.name()) {
        return None;
    }
    match args.as_slice() {
        [v] if as_var(v) == Some(it.name()) => Some((init.as_ref().clone(), it.clone())),
        _ => None,
    }
}

// Replace this var's `do get`/`do set` with cell reads/writes throughout the
// region (every subterm and thunk), and discharge the var's private effect
// label from every sig and every row nested in a witness type. Other ops, and
// other vars' ops, are left untouched.
struct SubtractVar {
    get: Sym,
    set: Sym,
    cell: TypedBinder,
    rows: SubtractEffect,
}

impl Rewrite for SubtractVar {
    type Ctx = ();

    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        match c.kind() {
            TypedCompKind::Do { operation, .. } if *operation == self.get => TypedComp::new(
                CompSig::new(self.core_type(c.sig().result(), &()), EffRow::Empty),
                TypedCompKind::RefGet(binder_var(&self.cell)),
            ),
            TypedCompKind::Do {
                operation, args, ..
            } if *operation == self.set => {
                // set takes one argument: the new value.
                let v = args.first().map_or_else(unit_value, |v| self.value(v, &()));
                TypedComp::new(
                    CompSig::new(self.core_type(c.sig().result(), &()), EffRow::Empty),
                    TypedCompKind::RefSet(binder_var(&self.cell), v),
                )
            }
            _ => self.descend_comp(c, &()),
        }
    }

    fn comp_sig(&mut self, sig: &CompSig, (): &()) -> CompSig {
        self.rows.sig(sig)
    }

    fn core_type(&mut self, ty: &CoreType, (): &()) -> CoreType {
        self.rows.ty(ty)
    }

    fn instantiation(&mut self, instantiation: &CoreInstantiation, (): &()) -> CoreInstantiation {
        Rewrite::instantiation(&mut self.rows, instantiation, &())
    }
}

// Suppress an unused-import lint until the erasure integrates with the
// builder: `TypedValue` participates only through helper signatures.
#[allow(unused_imports)]
use TypedValue as _TypedValueUsed;
