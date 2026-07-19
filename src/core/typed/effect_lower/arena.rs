//! Typed scope-directed arena lowering: the `Elaborated -> ArenaPrepared`
//! transition.
//!
//! A constructor built under a `with_arena` scope becomes a performed
//! allocation plus an in-place initialization:
//!
//! ```text
//!   let cell = alloc(|fields|) in init_at(cell, Ctor(C, fields))
//! ```
//!
//! Reachability decides which code is "under an arena" as
//! `arena_only = arena_reachable \ otherwise_reachable` over the direct call
//! graph.
//!
//! ## What the witnesses add
//!
//! The rewrite *introduces* an effect: a function that only built a constructor
//! now performs `alloc`, so its row is no longer the one elaboration proved.
//! Re-establishing the invalidated witnesses is the whole reason this is its own
//! phase rather than a licence to admit `InitAt` in elaborated Core.
//!
//! Two propagations, and the distinction between them is the crux:
//!
//!   - **Terms** are rewritten only in `arena_only` functions, and never inside a
//!     thunk because a closure's layout is not `init_at`-shaped.
//!   - **Rows** widen wherever the new operation became reachable, which includes
//!     functions that were never rewritten. `main` never allocates, yet the thunk
//!     it hands to `with_arena` now suspends a computation that does, so that
//!     thunk's *witness* gains the label while `main`'s own row does not.
//!
//! The widening is additive and local: [`Widen`] adds the one label exactly where
//! a node's checking rule now derives it, and preserves every other row as
//! elaboration wrote it. `Return` is the invariant keeping this honest: it is
//! pure by rule, so it never gains the label however effectful the computation it
//! suspends, and a uniform "add the label everywhere" pass would be rejected for
//! precisely that reason.
//!
//! The frontier is the thunk passed to `with_arena`, whose declared type already
//! reads `() -> a ! {Alloc}`; widening reaches it and stops, which is why the
//! label never escapes into `main`. A program where it would escape is one whose
//! `alloc` the reachability placed outside every handler that discharges it; it
//! is rejected here rather than lowered.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::builtins::Builtin;
use crate::error::TypedCoreEffectLoweringFailure;
use crate::names::{self, ALLOC_OP, ENTRY_POINT};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label};
use crate::types::Type;
use crate::util::fresh::Fresh;

use super::super::specialize_support::Rewrite;
use super::super::verify::{verify, VerifyEnv};
use super::super::{
    ArenaPrepared, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder,
    TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedValue, TypedValueKind,
};
use super::peel;
use super::walk::{each_subcomp, each_value};

/// The binder hint for a cell an allocator handed out.
const ARENA_CELL: &str = "arena_cell";

/// The binder hint for the region token `arena_enter` returns.
const ARENA_TOK: &str = "arena_tok";

/// The binder hint for a handler activation's result, promoted by `arena_exit`.
const ARENA_OUT: &str = "arena_out";

/// The type quantifier of the `arena_exit` verifier signature.
const ARENA_EXIT_QUANTIFIER: &str = "arena_a@";

/// Seed the verifier signatures of the region hook builtins this pass emits:
/// `arena_enter : () -> Int` (the activation-depth token) and
/// `arena_exit : forall a. (Int, a) -> a` (token and result threaded through,
/// so the bracket is data-dependent and no flow-respecting simplification can
/// separate or drop it). Neither is surface-callable, so overrides are their
/// only signature source.
pub(super) fn insert_builtin_sigs(env: &mut VerifyEnv) {
    let int = CoreType::Source(Type::Int);
    env.insert_builtin_override(
        Builtin::ArenaEnter,
        CoreFnSig::new(
            Vec::new(),
            Vec::new(),
            CompSig::new(int.clone(), EffRow::Empty),
        ),
    );
    let a = Sym::from(ARENA_EXIT_QUANTIFIER);
    let var = CoreType::Source(Type::Var(a));
    env.insert_builtin_override(
        Builtin::ArenaExit,
        CoreFnSig::new(
            vec![CoreQuantifier::Type(a)],
            vec![int, var.clone()],
            CompSig::new(var, EffRow::Empty),
        ),
    );
}

/// Rewrite constructors built under a `with_arena` scope into `alloc` +
/// `init_at`, re-establishing every witness the new operation invalidates.
///
/// A no-op on a program that installs no `Alloc` handler (the common case): the
/// tree is unchanged and only the phase marker moves. That path is verified too,
/// so the marker is never a claim about an unchecked tree.
///
/// # Errors
/// [`TypedCoreEffectLoweringFailure::Verification`] if the prepared tree does not
/// verify.
pub(super) fn prepare(
    fns: Vec<TypedCoreFn>,
    env: &VerifyEnv,
) -> Result<TypedCore<ArenaPrepared>, TypedCoreEffectLoweringFailure> {
    let installers = installers(&fns);
    if installers.is_empty() {
        return finish(fns, env);
    }
    // The cell type and the row label are read from the checked declaration of
    // the operation being performed, never named here: `init_at` is the proof
    // that this allocator's cell now holds this constructor, so the node and the
    // declaration must agree by construction rather than by coincidence.
    let Some(alloc) = env.operation(Sym::new(ALLOC_OP)) else {
        return finish(fns, env);
    };
    let alloc = Alloc {
        cell: alloc.result().clone(),
        label: alloc.effect().clone(),
    };
    let roots = arena_roots(&fns, &installers);
    if roots.is_empty() {
        return finish(fns, env);
    }
    let graph = direct_graph(&fns);
    let arena_reachable = closure(&roots, &graph);
    let otherwise = closure(
        &std::iter::once(Sym::new(ENTRY_POINT)).collect(),
        &otherwise_graph(&fns, &installers),
    );
    let arena_only: BTreeSet<Sym> = arena_reachable.difference(&otherwise).copied().collect();
    if arena_only.is_empty() {
        return finish(fns, env);
    }

    let gains = gains(&fns, &arena_only, &graph);
    let mut widen = Widen {
        alloc: &alloc,
        gains: &gains,
        fresh: Fresh::new(),
    };
    let fns = fns
        .iter()
        .map(|f| {
            let cx = Cx {
                rewriting: arena_only.contains(&f.name()),
                installer: installers.contains(&f.name()),
            };
            let body = widen.comp(f.body(), &cx);
            let sig = fn_sig_for(f.sig(), gains.contains(&f.name()), &alloc);
            TypedCoreFn::new(f.name(), f.params().to_vec(), body, sig, f.dict_arity())
        })
        .collect();
    finish(fns, env)
}

/// The checked declaration of the operation this pass performs.
struct Alloc {
    /// What the allocator hands out (currently `Arena.Cell`).
    cell: CoreType,
    /// The row label the operation carries (currently `Alloc`).
    label: Label,
}

// Verify, then stamp. The marker is never forged around an unverified tree.
fn finish(
    fns: Vec<TypedCoreFn>,
    env: &VerifyEnv,
) -> Result<TypedCore<ArenaPrepared>, TypedCoreEffectLoweringFailure> {
    let out = TypedCore::<ArenaPrepared>::new(fns);
    match verify(&out, env) {
        Ok(()) => Ok(out),
        Err(violations) => Err(TypedCoreEffectLoweringFailure::Verification {
            first: violations
                .first()
                .map_or_else(String::new, ToString::to_string),
            count: violations.len(),
        }),
    }
}

/// Functions whose body installs an `Alloc` handler. Recognized structurally, so
/// no handler name is hardcoded.
fn installers(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| handles_alloc(f.body()))
        .map(TypedCoreFn::name)
        .collect()
}

/// Whether `c` (or a sub-computation) is a `Handle` whose clauses include
/// `alloc`.
fn handles_alloc(c: &TypedComp) -> bool {
    if nested_alloc_handler(c) {
        return true;
    }
    let mut found = false;
    each_subcomp(c, &mut |sc| found |= handles_alloc(sc));
    found
}

/// The arena roots: the entry functions of the thunks passed to an installer at
/// each of its call sites. ANF binds the thunk to a variable and passes the
/// variable, so each function first maps its `var -> thunk` bindings, then
/// resolves each installer argument against that map. A thunk that does not
/// monomorphically name a function contributes nothing, leaving that site
/// un-reified.
fn arena_roots(fns: &[TypedCoreFn], installers: &BTreeSet<Sym>) -> BTreeSet<Sym> {
    let mut roots = BTreeSet::new();
    for f in fns {
        let mut thunks: BTreeMap<Sym, &TypedComp> = BTreeMap::new();
        thunk_bindings(f.body(), &mut thunks);
        collect_roots(f.body(), installers, &thunks, &mut roots);
    }
    roots
}

/// Map every var bound to a thunk literal to that thunk's body, so an installer
/// call passing the variable can be resolved. Descends into thunk values too: a
/// binding inside a loop body or closure (elaborated as a suspended
/// computation) is as resolvable as one at the top of the function, and
/// post-elaboration binder names are fresh, so one flat map per function cannot
/// collide across scopes.
fn thunk_bindings<'a>(c: &'a TypedComp, out: &mut BTreeMap<Sym, &'a TypedComp>) {
    if let TypedCompKind::Bind(m, x, _) = c.kind() {
        if let TypedCompKind::Return(v) = m.kind() {
            if let TypedValueKind::Thunk(body) = &peel(v).kind {
                out.insert(x.name(), body);
            }
        }
    }
    each_value(c, &mut |v| thunk_bindings_value(v, out));
    each_subcomp(c, &mut |sc| thunk_bindings(sc, out));
}

fn thunk_bindings_value<'a>(v: &'a TypedValue, out: &mut BTreeMap<Sym, &'a TypedComp>) {
    match &v.kind {
        TypedValueKind::Thunk(c) => thunk_bindings(c, out),
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            thunk_bindings_value(inner, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                thunk_bindings_value(f, out);
            }
        }
        _ => {}
    }
}

/// Find installer calls anywhere in `c`, descending into thunk values: a
/// `with_arena` call inside a loop body or closure installs its handler exactly
/// as one written at the top of the function does.
fn collect_roots<'a>(
    c: &'a TypedComp,
    installers: &BTreeSet<Sym>,
    thunks: &BTreeMap<Sym, &'a TypedComp>,
    out: &mut BTreeSet<Sym>,
) {
    if let TypedCompKind::Call { callee, args, .. } = c.kind() {
        if installers.contains(callee) {
            for a in args {
                match &peel(a).kind {
                    TypedValueKind::Thunk(body) => calls_deep(body, out),
                    TypedValueKind::Var { name, .. } => {
                        if let Some(body) = thunks.get(name) {
                            calls_deep(body, out);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    each_value(c, &mut |v| collect_roots_value(v, installers, thunks, out));
    each_subcomp(c, &mut |sc| collect_roots(sc, installers, thunks, out));
}

fn collect_roots_value<'a>(
    v: &'a TypedValue,
    installers: &BTreeSet<Sym>,
    thunks: &BTreeMap<Sym, &'a TypedComp>,
    out: &mut BTreeSet<Sym>,
) {
    match &v.kind {
        TypedValueKind::Thunk(c) => collect_roots(c, installers, thunks, out),
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            collect_roots_value(inner, installers, thunks, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                collect_roots_value(f, installers, thunks, out);
            }
        }
        _ => {}
    }
}

/// Every direct call head anywhere in `c`, descending through thunks (unlike
/// [`all_calls`]), so a root nested in a lambda inside the thunk is still found.
fn calls_deep(c: &TypedComp, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = c.kind() {
        out.insert(*callee);
    }
    each_value(c, &mut |v| calls_deep_value(v, out));
    each_subcomp(c, &mut |sc| calls_deep(sc, out));
}

fn calls_deep_value(v: &TypedValue, out: &mut BTreeSet<Sym>) {
    match &v.kind {
        TypedValueKind::Thunk(c) => calls_deep(c, out),
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            calls_deep_value(inner, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                calls_deep_value(f, out);
            }
        }
        _ => {}
    }
}

/// Every direct call head in `c`'s own body, not descending into thunk values (a
/// thunk is a deferred computation, not a call the enclosing function makes).
fn all_calls(c: &TypedComp, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = c.kind() {
        out.insert(*callee);
    }
    each_subcomp(c, &mut |sc| all_calls(sc, out));
}

/// The direct call graph.
fn direct_graph(fns: &[TypedCoreFn]) -> BTreeMap<Sym, BTreeSet<Sym>> {
    fns.iter()
        .map(|f| {
            let mut callees = BTreeSet::new();
            all_calls(f.body(), &mut callees);
            (f.name(), callees)
        })
        .collect()
}

/// The non-arena call graph, for the `otherwise_reachable` side of the
/// subtraction: every named call head in a function's body, descending into
/// thunk values (a loop body or closure runs in its creator's own context),
/// EXCEPT the entry thunks passed to installers, which run under the installed
/// handler and are precisely the arena side. Without the carve-out every arena
/// entry would also count as otherwise-reachable and nothing could be reified;
/// without the thunk descent a function called from an ordinary loop body would
/// be invisible here and could be misclassified arena-only.
fn otherwise_graph(
    fns: &[TypedCoreFn],
    installers: &BTreeSet<Sym>,
) -> BTreeMap<Sym, BTreeSet<Sym>> {
    fns.iter()
        .map(|f| {
            let mut thunks = BTreeMap::new();
            thunk_bindings(f.body(), &mut thunks);
            let mut skip = BTreeSet::new();
            installer_entry_bodies(f.body(), installers, &thunks, &mut skip);
            let mut callees = BTreeSet::new();
            calls_outside_arenas(f.body(), &skip, &mut callees);
            (f.name(), callees)
        })
        .collect()
}

/// The identity of one thunk body, for the installer-entry carve-out. The
/// var-bound case resolves to the literal at its binding site, so the address
/// identifies the same body either way it is reached.
fn body_id(body: &TypedComp) -> usize {
    std::ptr::from_ref::<TypedComp>(body) as usize
}

/// The body identities of every thunk passed to an installer call in `c`.
fn installer_entry_bodies<'a>(
    c: &'a TypedComp,
    installers: &BTreeSet<Sym>,
    thunks: &BTreeMap<Sym, &'a TypedComp>,
    out: &mut BTreeSet<usize>,
) {
    if let TypedCompKind::Call { callee, args, .. } = c.kind() {
        if installers.contains(callee) {
            for a in args {
                match &peel(a).kind {
                    TypedValueKind::Thunk(body) => {
                        out.insert(body_id(body));
                    }
                    TypedValueKind::Var { name, .. } => {
                        if let Some(body) = thunks.get(name) {
                            out.insert(body_id(body));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    each_value(c, &mut |v| {
        installer_entry_value(v, installers, thunks, out);
    });
    each_subcomp(c, &mut |sc| {
        installer_entry_bodies(sc, installers, thunks, out);
    });
}

fn installer_entry_value<'a>(
    v: &'a TypedValue,
    installers: &BTreeSet<Sym>,
    thunks: &BTreeMap<Sym, &'a TypedComp>,
    out: &mut BTreeSet<usize>,
) {
    match &v.kind {
        TypedValueKind::Thunk(c) => installer_entry_bodies(c, installers, thunks, out),
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            installer_entry_value(inner, installers, thunks, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                installer_entry_value(f, installers, thunks, out);
            }
        }
        _ => {}
    }
}

/// Every named call head in `c`, descending into thunk values except the
/// carved-out installer entries.
fn calls_outside_arenas(c: &TypedComp, skip: &BTreeSet<usize>, out: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = c.kind() {
        out.insert(*callee);
    }
    each_value(c, &mut |v| calls_outside_value(v, skip, out));
    each_subcomp(c, &mut |sc| calls_outside_arenas(sc, skip, out));
}

fn calls_outside_value(v: &TypedValue, skip: &BTreeSet<usize>, out: &mut BTreeSet<Sym>) {
    match &v.kind {
        TypedValueKind::Thunk(c) => {
            if !skip.contains(&body_id(c)) {
                calls_outside_arenas(c, skip, out);
            }
        }
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            calls_outside_value(inner, skip, out);
        }
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
            for f in fields {
                calls_outside_value(f, skip, out);
            }
        }
        _ => {}
    }
}

/// Transitive closure of `roots` over `graph`.
fn closure(roots: &BTreeSet<Sym>, graph: &BTreeMap<Sym, BTreeSet<Sym>>) -> BTreeSet<Sym> {
    let mut visited: BTreeSet<Sym> = BTreeSet::new();
    let mut stack: Vec<Sym> = roots.iter().copied().collect();
    while let Some(n) = stack.pop() {
        if !visited.insert(n) {
            continue;
        }
        if let Some(succ) = graph.get(&n) {
            stack.extend(succ.iter().copied());
        }
    }
    visited
}

/// The functions whose row gains the label: those the rewrite makes perform the
/// operation directly, plus their transitive direct callers. A least fixpoint
/// over the direct call graph, which is the propagation rows themselves follow: a
/// call in computation position carries its callee's row, while a call suspended
/// under a thunk carries it only into that thunk's witness.
fn gains(
    fns: &[TypedCoreFn],
    arena_only: &BTreeSet<Sym>,
    graph: &BTreeMap<Sym, BTreeSet<Sym>>,
) -> BTreeSet<Sym> {
    let op = Sym::new(ALLOC_OP);
    let seed: BTreeMap<Sym, BTreeSet<Sym>> = fns
        .iter()
        .map(|f| {
            let mut own = BTreeSet::new();
            if arena_only.contains(&f.name()) && rewrites(f.body()) {
                own.insert(op);
            }
            (f.name(), own)
        })
        .collect();
    crate::util::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut s = BTreeSet::new();
        for callee in graph.get(name).into_iter().flatten() {
            if cur.get(callee).is_some_and(|c| !c.is_empty()) {
                s.insert(op);
            }
        }
        s
    })
    .into_iter()
    .filter(|(_, ops)| !ops.is_empty())
    .map(|(name, _)| name)
    .collect()
}

/// Whether [`Widen`] has a rewrite site in this body: the same recursion it
/// performs, so the two never disagree about who allocates.
fn rewrites(c: &TypedComp) -> bool {
    if is_rewrite_site(c) {
        return true;
    }
    if nested_alloc_handler(c) {
        return false;
    }
    let mut found = false;
    each_subcomp(c, &mut |sc| found |= rewrites(sc));
    found
}

/// `Return` of a boxed constructor or boxed tuple: the shape an allocator can
/// hand out a cell for.
fn is_rewrite_site(c: &TypedComp) -> bool {
    match c.kind() {
        TypedCompKind::Return(v) => matches!(
            peel(v).kind,
            TypedValueKind::Ctor { .. } | TypedValueKind::Tuple(_)
        ),
        _ => false,
    }
}

/// A nested `alloc` handler re-services allocation, so its subtree belongs to
/// that handler rather than being reified twice.
fn nested_alloc_handler(c: &TypedComp) -> bool {
    matches!(c.kind(), TypedCompKind::Handle { ops, .. }
        if ops.arms().iter().any(|op| op.name().as_str() == ALLOC_OP))
}

/// A function's declared signature after the rewrite. The body's row must be a
/// subrow of the declared one, so a body that gained the label forces the
/// declaration to carry it. Everything else is left exactly as elaboration wrote
/// it: the parameters, because the rewrite never changes what a function is
/// handed, and the result, because the body is checked against it by subtyping
/// and a rewrite would discard the generality elaboration proved.
fn fn_sig_for(sig: &CoreFnSig, gained: bool, alloc: &Alloc) -> CoreFnSig {
    if !gained {
        return sig.clone();
    }
    CoreFnSig::new(
        sig.quantifiers().to_vec(),
        sig.params().to_vec(),
        CompSig::new(
            sig.body().result().clone(),
            alloc.widen(sig.body().effects()),
        ),
    )
}

impl Alloc {
    fn present(&self, row: &EffRow) -> bool {
        row.labels().iter().any(|l| l.name == self.label.name)
    }

    /// Add the one label the rewrite introduced, leaving every other row exactly
    /// as elaboration wrote it. Rows are unions of leaf rows, so a union with the
    /// singleton is precisely the widened row.
    fn widen(&self, row: &EffRow) -> EffRow {
        if self.present(row) {
            return row.clone();
        }
        EffRow::canonical(
            row.labels()
                .into_iter()
                .cloned()
                .chain(std::iter::once(self.label.clone())),
            row.tail().clone(),
        )
    }

    /// Whether forcing a thunk with this witness now performs the operation.
    ///
    /// Only the thunk's own row counts. A thunk whose result is a closure that
    /// allocates performs nothing when forced: forcing hands back the closure,
    /// and the operation is the caller's at the application that runs it.
    fn in_thunk(&self, ty: &CoreType) -> bool {
        match ty {
            CoreType::Thunk(sig) => self.present(sig.effects()),
            _ => false,
        }
    }

    /// Whether a closure witness now abstracts the operation.
    fn in_function(&self, ty: &CoreType) -> bool {
        match ty {
            CoreType::Function(sig) => self.present(sig.body().effects()),
            _ => false,
        }
    }
}

/// Whether this function's terms are rewritten. Rows widen everywhere; terms
/// only inside `arena_only`; region brackets only around the alloc-handling
/// `Handle` nodes of installer functions.
struct Cx {
    rewriting: bool,
    installer: bool,
}

struct Widen<'a> {
    alloc: &'a Alloc,
    gains: &'a BTreeSet<Sym>,
    fresh: Fresh,
}

impl Rewrite for Widen<'_> {
    type Ctx = Cx;

    /// A thunk's witness is its body's signature exactly, so a thunk whose body
    /// widened must be re-witnessed here. This is the step that carries the label
    /// out of a rewritten function and into the closure a caller passes around,
    /// which is how it reaches `with_arena`'s parameter without ever entering the
    /// row of the function that builds the thunk.
    fn value(&mut self, value: &TypedValue, cx: &Cx) -> TypedValue {
        let out = self.descend_value(value, cx);
        match &out.kind {
            TypedValueKind::Thunk(body) => {
                TypedValue::new(CoreType::Thunk(Box::new(body.sig().clone())), out.kind)
            }
            _ => out,
        }
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Cx) -> TypedComp {
        if cx.rewriting && is_rewrite_site(comp) {
            let TypedCompKind::Return(ctor) = comp.kind() else {
                unreachable!("a rewrite site is a Return by construction")
            };
            return self.split_alloc(ctor);
        }
        // A nested `alloc` handler owns its subtree's allocations. Rows inside it
        // still widen: a call it makes to a rewritten function performs that
        // function's operation, which this scope does not service.
        let inner = Cx {
            rewriting: cx.rewriting && !nested_alloc_handler(comp),
            installer: cx.installer,
        };
        let out = self.descend_comp(comp, &inner);
        let out = self.retype(out);
        // Each alloc-handling `Handle` in an installer is one region activation:
        // bracket it with the runtime enter/exit hooks.
        if cx.installer && nested_alloc_handler(&out) {
            return self.bracket_region(out);
        }
        out
    }
}

impl Widen<'_> {
    /// Bracket one alloc-handling `Handle` with the runtime region hooks:
    ///
    /// ```text
    ///   let tok = arena_enter() in
    ///   let out = handle ... in
    ///   arena_exit(tok, out)
    /// ```
    ///
    /// One region per handler activation. The token makes the bracket
    /// data-dependent (enter feeds exit, exit produces the activation's
    /// result), so no flow-respecting simplification can drop or reorder it,
    /// and the runtime traps on any unbalanced pairing. `arena_exit` promotes
    /// whatever escapes the activation before the region is reclaimed, so it
    /// must see the final result, which is why the bracket wraps the whole
    /// `Handle` (return clause included) rather than editing its clauses.
    ///
    /// An exotic handler whose result is not a source type cannot carry the
    /// exit instantiation; it is left unbracketed, which is sound because
    /// `bump` without an open region delegates to the ordinary allocator.
    fn bracket_region(&mut self, handle: TypedComp) -> TypedComp {
        let CoreType::Source(result_src) = handle.sig().result() else {
            return handle;
        };
        let result_src = result_src.clone();
        let result = handle.sig().result().clone();
        let effects = handle.sig().effects().clone();
        let int = CoreType::Source(Type::Int);
        let tok = TypedBinder::new(
            Sym::from(names::lowered(ARENA_TOK, self.fresh.bump())),
            int.clone(),
        );
        let out = TypedBinder::new(
            Sym::from(names::lowered(ARENA_OUT, self.fresh.bump())),
            result.clone(),
        );
        let enter = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArenaEnter,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let exit = TypedComp::new(
            CompSig::new(result.clone(), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArenaExit,
                instantiation: vec![CoreInstantiation::Type(result_src)],
                args: vec![
                    TypedValue::new(
                        int,
                        TypedValueKind::Var {
                            name: tok.name(),
                            instantiation: Vec::new(),
                        },
                    ),
                    TypedValue::new(
                        result.clone(),
                        TypedValueKind::Var {
                            name: out.name(),
                            instantiation: Vec::new(),
                        },
                    ),
                ],
            },
        );
        let after = TypedComp::new(
            CompSig::new(result.clone(), effects.clone()),
            TypedCompKind::Bind(Box::new(handle), out, Box::new(exit)),
        );
        TypedComp::new(
            CompSig::new(result, effects),
            TypedCompKind::Bind(Box::new(enter), tok, Box::new(after)),
        )
    }

    /// `return ctor` becomes `let cell = alloc(arity) in init_at(cell, ctor)`.
    /// The replacement's row is exactly the operation's: `alloc` performs it and
    /// the in-place write is pure.
    fn split_alloc(&mut self, ctor: &TypedValue) -> TypedComp {
        let arity = match &peel(ctor).kind {
            TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => fields.len(),
            _ => unreachable!("split_alloc called on a non-constructor value"),
        };
        let row = EffRow::canonical([self.alloc.label.clone()], EffRow::Empty);
        let cell = TypedBinder::new(
            Sym::from(names::lowered(ARENA_CELL, self.fresh.bump())),
            self.alloc.cell.clone(),
        );
        let size = TypedValue::new(
            CoreType::Source(Type::Int),
            TypedValueKind::Int(i64::try_from(arity).unwrap_or(i64::MAX)),
        );
        let perform = TypedComp::new(
            CompSig::new(self.alloc.cell.clone(), row.clone()),
            TypedCompKind::Do {
                operation: Sym::new(ALLOC_OP),
                instantiation: Vec::new(),
                args: vec![size],
            },
        );
        let init = TypedComp::new(
            CompSig::new(ctor.ty().clone(), EffRow::Empty),
            TypedCompKind::InitAt(
                TypedValue::new(
                    self.alloc.cell.clone(),
                    TypedValueKind::Var {
                        name: cell.name(),
                        instantiation: Vec::new(),
                    },
                ),
                ctor.clone(),
            ),
        );
        TypedComp::new(
            CompSig::new(ctor.ty().clone(), row),
            TypedCompKind::Bind(Box::new(perform), cell, Box::new(init)),
        )
    }

    /// Re-establish one node's signature from its rewritten children.
    ///
    /// Only the introduced label moves. A node gains it exactly when its own
    /// checking rule now derives it from a child, which is why `Return` is
    /// absent: it is pure by rule, and the thunk it suspends carries the label in
    /// its witness instead.
    fn retype(&self, comp: TypedComp) -> TypedComp {
        let TypedComp { sig, kind } = comp;
        let widened = match &kind {
            // A direct call's row is exactly its callee's declared row.
            TypedCompKind::Call { callee, .. } => self.gains.contains(callee),
            // A composite carries the union of the rows its children run.
            TypedCompKind::Bind(m, _, n) => {
                self.alloc.present(m.sig().effects()) || self.alloc.present(n.sig().effects())
            }
            TypedCompKind::If(_, t, e) => {
                self.alloc.present(t.sig().effects()) || self.alloc.present(e.sig().effects())
            }
            TypedCompKind::Case(_, arms) => arms
                .iter()
                .any(|(_, b)| self.alloc.present(b.sig().effects())),
            TypedCompKind::Mask(labels, b) => {
                self.alloc.present(b.sig().effects()) && !labels.contains(&self.alloc.label.name)
            }
            // Forcing a thunk runs what it suspends.
            TypedCompKind::Force(v) => self.alloc.in_thunk(v.ty()),
            // Applying a computed closure runs that closure's body.
            TypedCompKind::App { callee, .. } => {
                self.alloc.present(callee.sig().effects())
                    || self.alloc.in_function(callee.sig().result())
            }
            // `Handle` discharges its own operations, so an `alloc` its body
            // performs is this scope's to service and does not escape it.
            _ => false,
        };
        let effects = if widened {
            self.alloc.widen(sig.effects())
        } else {
            sig.effects().clone()
        };
        let result = self.result_for(&sig, &kind);
        let kind = Self::rebind(kind);
        TypedComp::new(CompSig::new(result, effects), kind)
    }

    /// A node's result type after its children were rewritten.
    ///
    /// Rebuilt only where the checking rule is an equality and a child is the
    /// authority for it. Everywhere else the stored type is kept: those rules
    /// check the child against the stored type by *subtyping*, so a stored type
    /// that was already general stays general, and re-deriving it from a child
    /// would silently discard the row variable elaboration proved.
    fn result_for(&self, sig: &CompSig, kind: &TypedCompKind) -> CoreType {
        match kind {
            // A return's witness is its value's, exactly.
            TypedCompKind::Return(v) => v.ty().clone(),
            // A lambda's declared body row may legitimately be wider than the
            // body's own, so widen it rather than replace it.
            TypedCompKind::Lam(_, body) if self.alloc.present(body.sig().effects()) => {
                match sig.result() {
                    CoreType::Function(f) => CoreType::Function(Box::new(CoreFnSig::new(
                        f.quantifiers().to_vec(),
                        f.params().to_vec(),
                        CompSig::new(
                            f.body().result().clone(),
                            self.alloc.widen(f.body().effects()),
                        ),
                    ))),
                    other => other.clone(),
                }
            }
            _ => sig.result().clone(),
        }
    }

    /// A bind's binder holds exactly what the bound computation returns, so a
    /// binder whose computation was rewritten must follow it.
    fn rebind(kind: TypedCompKind) -> TypedCompKind {
        match kind {
            TypedCompKind::Bind(m, x, n) => {
                let x = TypedBinder::new(x.name(), m.sig().result().clone());
                TypedCompKind::Bind(m, x, n)
            }
            other => other,
        }
    }
}
