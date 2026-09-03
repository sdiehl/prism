use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use crate::error::{suggest, ErrKind, TypeError};
pub use crate::error::{HoleBinding, HoleCandidate, HoleReport};
use crate::hir::NodeFacts;
use crate::names;
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl, Expr, Program, S};
use crate::types::deps;
use crate::types::ty::{EffRow, Effects, Label, Type};

mod classes;
mod context;
use context::Renames;

mod coverage;
mod env;
pub use env::Env;
pub(crate) use env::{builtin_sigs, is_builtin_effect};
mod infer;
mod pat;
mod product;
pub use product::{
    Canon, Checked, CheckedView, ClassConstraint, ClassInfo, ConstrainedScheme, ConstrainedSchemes,
    DataInfo, DeclFacts, Dict, DictTable, DispatchFacts, FieldRef, HeadKey, InstInfo, InstKeys,
    InterfaceFacts, MethodRef, NominalRepr, PathRes, Reports, TypeParameter, Warning,
};
pub(crate) use product::{CtorInfo, DeclInfo, EffOpInfo, WarningOrigin};
mod seed;
mod session;
pub(crate) use seed::{SeedClassMethod, TypecheckSeedBuilder};
pub use seed::{TypecheckSeed, TypecheckSeedError};
use session::{
    BodyWitness, EffectOperationUses, Entry, HandlerFrame, HoleSite, IndexOp, OperationUses,
    RowScope, SelfRef, Tc, TcErr, Wanted,
};
mod subsume;
#[cfg(test)]
mod tests;

// The concrete effects a declaration performs, with multiplicities: the label
// counts of its inferred function row (peeling quantifiers). Rows are
// multisets (`mask` raises a label's count above one), so the count is part of
// the contract an annotation must cover. A polymorphic row tail contributes
// none; a non-function value performs nothing observable in its type.
fn concrete_effect_counts(ty: &Type) -> BTreeMap<Sym, usize> {
    let mut t = ty;
    while let Type::Forall(_, b) | Type::RowForall(_, b) = t {
        t = b;
    }
    match t {
        Type::Fun(_, row, _) => row.label_counts(),
        _ => BTreeMap::new(),
    }
}

// The function's parameter types and inferred effect row, peeling quantifiers.
// `None` for a non-function type (a plain value binds no row). Shares the
// quantifier peel with `concrete_effect_counts` but returns the whole
// signature, so the open-tail case can be distinguished from a closed empty
// one.
fn fn_sig(ty: &Type) -> Option<(&[Type], &EffRow, &Type)> {
    let mut t = ty;
    while let Type::Forall(_, b) | Type::RowForall(_, b) = t {
        t = b;
    }
    match t {
        Type::Fun(doms, row, ret) => Some((doms, row, ret)),
        _ => None,
    }
}

// A top-level constant must be effect-free: its initializer runs once at load
// with no handler in scope. The effects are the body's principal inferred row
// (its `konst` body is checked under a fresh ambient row whose labels are read
// off here), so the check is exact rather than a syntactic over-approximation.
pub(super) fn require_pure_konst(d: &Decl<Core>, effs: &Effects) -> Result<(), TypeError> {
    if !effs.is_empty() {
        let list: Vec<String> = effs.iter().map(Sym::to_string).collect();
        return Err(ErrKind::KonstNotPure {
            name: d.name.clone(),
            effects: list.join(", "),
        }
        .at(d.body.span));
    }
    Ok(())
}

// The post-inference checks for a function: enforce `borrow`-implies-pure and
// check the declared effect annotation against the inferred (principal) row.
// Returns the `DeclInfo` to record. Shared by the singleton and mutually
// recursive driver paths.
fn finalize_fn(
    d: &Decl<Core>,
    ty: Type,
    witness: &BodyWitness,
    warnings: &mut Vec<Warning>,
) -> Result<DeclInfo, TypeError> {
    // The labels of the inferred row, with multiplicities. Effect-row inference
    // is principal: it discovers every effect on its own (direct performs,
    // applied effect-carrying callees, builtin rows, `mask`), so the row alone
    // determines inferred effects. Real under-coverage is caught downstream by
    // `reconcile_effects` (lowered ops vs the row) and the parity oracle.
    let inferred_counts = concrete_effect_counts(&ty);
    let inferred: Effects = inferred_counts.keys().copied().collect();
    if d.params.iter().any(|p| p.borrow) {
        // The RC calling convention retains ownership of a borrowed argument
        // across the call, so a `borrow`-taking function must be provably pure.
        // Concrete labels are the obvious failure; a body whose ambient row
        // solved to one flowing through the interface (it forwards a
        // higher-order argument's effects, or returns a computation carrying
        // them, either of which can suspend) is the subtle one. Both facts are
        // read off the recorded principal-body-effect witness inference
        // captured before generalization, not re-derived from the scheme.
        if !witness.effects.is_empty() {
            let list: Vec<String> = witness.effects.iter().map(Sym::to_string).collect();
            return Err(ErrKind::BorrowNotPure {
                name: d.name.clone(),
                effects: list.join(", "),
            }
            .at(d.span));
        }
        if !witness.closed {
            let row = fn_sig(&ty).map_or_else(String::new, |(_, row, _)| row.show());
            return Err(ErrKind::BorrowRowNotClosed {
                name: d.name.clone(),
                row,
            }
            .at(d.span));
        }
    }
    if let Some(declared) = &d.eff {
        // The annotation is a multiset too: writing a label twice covers the
        // extra occurrence a `mask` adds, so the check compares counts, not
        // membership. An inferred count above the declared one means the body
        // demands a handler the annotation does not promise.
        let mut declared_counts: BTreeMap<Sym, usize> = BTreeMap::new();
        for l in declared {
            *declared_counts.entry(Sym::from(&l.name)).or_default() += 1;
        }
        for (eff, demanded) in &inferred_counts {
            if *demanded > declared_counts.get(eff).copied().unwrap_or_default() {
                return Err(ErrKind::UndeclaredEffect {
                    name: d.name.clone(),
                    eff: eff.to_string(),
                }
                .at(d.body.span));
            }
        }
        // The reverse direction is sound (a pure body satisfies an effectful
        // annotation by subsumption) but the annotation then disagrees with the
        // inferred row, so warn rather than reject: a declared effect, or an
        // extra declared occurrence, the body never performs is dead weight.
        for (eff, declared_count) in &declared_counts {
            let performed = inferred_counts.get(eff).copied().unwrap_or_default();
            if performed == 0 {
                warnings.push(Warning {
                    span: d.span,
                    msg: format!(
                        "in `{}`: effect `{eff}` declared in the annotation but never performed",
                        d.name
                    ),
                    origin: WarningOrigin::Decl(Sym::from(&d.name)),
                });
            } else if performed < *declared_count {
                warnings.push(Warning {
                    span: d.span,
                    msg: format!(
                        "in `{}`: effect `{eff}` declared {declared_count} times but the body demands only {performed}",
                        d.name
                    ),
                    origin: WarningOrigin::Decl(Sym::from(&d.name)),
                });
            }
        }
    }
    Ok(DeclInfo {
        name: d.name.clone(),
        params: d.params.iter().map(|p| p.name.clone()).collect(),
        ty,
        effects: inferred,
        pure: witness.effects.is_empty() && witness.closed,
    })
}

/// # Errors
/// Fails when the program does not type check.
pub fn check(prog: &Program<Core>) -> Result<Checked, TypeError> {
    check_seeded(prog, &TypecheckSeed::default())
}

/// Typecheck a program and retain typed-hole reports instead of rejecting them.
/// This is deliberately separate from [`check`]: only the interpreter's explicit
/// deferred-hole mode should call it.
///
/// # Errors
/// Fails for ordinary type errors; typed holes are returned in [`Reports::holes`].
pub fn check_allow_holes(prog: &Program<Core>) -> Result<Checked, TypeError> {
    check_seeded_mode(prog, &TypecheckSeed::default(), false)
}

/// Typecheck while collecting each expression node's canonical inferred type
/// and evaluation-effect row. This is deliberately crate-private: it is the
/// analysis path for `dump typespans` and documentation tooltips, never an
/// alternate compilation policy.
pub(crate) fn check_tooltips(prog: &Program<Core>) -> Result<Checked, TypeError> {
    // Tooltips are an observation surface, not a judgment: a typed hole is
    // retained (its report carries the inferred type the hover shows) rather
    // than promoted to the error `check` raises.
    check_seeded_mode(prog, &TypecheckSeed::default(), true)
}

/// Typecheck one program against already checked dependency facts.
///
/// # Errors
/// Fails when the local program or its use of an imported fact does not typecheck.
pub fn check_seeded(prog: &Program<Core>, seed: &TypecheckSeed) -> Result<Checked, TypeError> {
    let checked = check_seeded_allow_holes(prog, seed)?;
    if checked.reports.holes.is_empty() {
        Ok(checked)
    } else {
        Err(hole_error(&checked.reports.holes))
    }
}

/// Seeded form of [`check_allow_holes`].
///
/// # Errors
/// Fails for ordinary type errors; typed holes themselves are returned in
/// [`Reports::holes`].
pub fn check_seeded_allow_holes(
    prog: &Program<Core>,
    seed: &TypecheckSeed,
) -> Result<Checked, TypeError> {
    check_seeded_mode(prog, seed, false)
}

/// The signatures a program's own constructor and operation declarations put in
/// `env`, captured before the seed merges over it so they can be restored after.
fn declared_member_signatures(prog: &Program<Core>, env: &Env) -> Vec<(Sym, Type)> {
    let ctors = prog
        .types
        .iter()
        .flat_map(|d| d.ctors.iter().map(|c| &c.name));
    let ops = prog
        .effects
        .iter()
        .flat_map(|e| e.ops.iter().map(|o| &o.name));
    ctors
        .chain(ops)
        .map(|name| Sym::new(name))
        .filter_map(|name| env.get(&name).map(|ty| (name, ty.clone())))
        .collect()
}

fn check_seeded_mode(
    prog: &Program<Core>,
    seed: &TypecheckSeed,
    track_tooltips: bool,
) -> Result<Checked, TypeError> {
    let (mut data, mut ctors, mut eff_ops, mut env) = env::build_data(prog)?;
    // The seed is the ambient foundation: the prelude, the embedded standard
    // library, and every imported interface. A name the program declares itself
    // is the program's, so seeding must not overwrite it. That is what the
    // whole-program checker does, where a user declaration of a prelude name
    // displaces the prelude's (the resolver relocates the prelude's to a
    // module-private name), and the modular check has to agree with it: a
    // program that runs must also build. Plain `extend` has the opposite
    // precedence, so insert only the keys the program left free.
    for (name, info) in seed.data_types() {
        data.entry(name.clone()).or_insert_with(|| info.clone());
    }
    for (name, info) in seed.constructors() {
        ctors.entry(name.clone()).or_insert_with(|| info.clone());
    }
    for (name, info) in seed.effect_operations() {
        eff_ops.entry(name.clone()).or_insert_with(|| info.clone());
    }
    // `env` also holds the builtin base bindings, which the seed is entitled to
    // refine, so it keeps seed precedence and only the program's own member
    // signatures are restored over it.
    let local_members = declared_member_signatures(prog, &env);
    env.extend(
        seed.environment()
            .iter()
            .map(|(name, ty)| (*name, ty.clone())),
    );
    for (name, ty) in local_members {
        env.insert(name, ty);
    }
    // Constructor field annotations are converted while the datatype
    // environment is built, before its imported half is merged. Validate them
    // now against the complete local-plus-imported datatype table. In
    // particular, an unopened imported type must be rejected here as an unknown
    // type instead of surviving as a nominal `Type::Con` and later making the
    // structural printer generate an empty match.
    for data_decl in &prog.types {
        let span = if crate::names::module_of(&data_decl.name).is_empty() {
            data_decl.span
        } else {
            Span::default()
        };
        for ctor in &data_decl.ctors {
            for field_ty in &ctor.args {
                env::check_known_types(field_ty, &data, span)?;
            }
        }
    }
    let seeds = env::seed_var_states(&eff_ops);
    let classes::ClassBuild {
        classes,
        instances,
        inst_keys,
        canonical,
        methods,
        mut constrained,
        mut warnings,
    } = classes::build_classes(prog, &mut data, &mut ctors, &mut env, seed)?;
    let mut infos = Vec::new();
    // Validate where-clauses and record each constrained function's scheme up
    // front; this is order-independent and must precede inference. Functions are
    // *not* seeded into `env` here: a referenced top-level binding is seeded into
    // `env` by its own strongly-connected component just before that component is
    // inferred (callee components first), so by the time it is referenced it
    // already holds either a real generalized scheme (an earlier component) or
    // the monomorphic self-type of a mutually recursive sibling (the same
    // component). A constrained function is fully annotated, so its stored scheme
    // is its annotation scheme, which is exactly what its component seeds.
    for d in &prog.fns {
        if d.constraints.is_empty() {
            continue;
        }
        if d.params.iter().any(|p| p.ty.is_none()) || d.ret.is_none() {
            return Err(ErrKind::WhereClauseNeedsAnnotations {
                name: d.name.clone(),
            }
            .at(d.span));
        }
        let mut cs = Vec::new();
        for c in &d.constraints {
            if !classes.contains_key(&Sym::from(&c.class)) {
                return Err(ErrKind::UnknownClass {
                    class: c.class.clone(),
                }
                .at(c.span)
                .maybe_help(suggest::suggestion(
                    &c.class,
                    classes.keys().map(|k| names::bare_name(k.as_str())),
                )));
            }
            cs.push(ClassConstraint {
                class: Sym::from(&c.class),
                head: env::convert_data(&c.ty),
            });
        }
        constrained.insert(
            Sym::from(&d.name),
            ConstrainedScheme {
                scheme: env::fn_stub(d, &data),
                constraints: cs,
            },
        );
    }
    let field_res;
    let unboxed_field;
    let path_res;
    let fixed;
    let span_types;
    let tooltip_rows;
    let method_effects;
    let handler_nodes;
    let handler_residuals;
    let generalized_lets;
    let dicts;
    let constrained_final;
    let mut holes;
    {
        let mut tc = Tc {
            ctx: (0..seeds).map(Entry::Ex).collect(),
            next: seeds,
            seeds,
            ctors: &ctors,
            data: &data,
            eff_ops: &eff_ops,
            field_res: BTreeMap::new(),
            unboxed_field: BTreeMap::new(),
            path_res: PathRes::new(),
            fixed: BTreeMap::new(),
            span_types: BTreeMap::new(),
            track_tooltips,
            pending_tooltip_rows: Vec::new(),
            tooltip_rows: BTreeMap::new(),
            method_effects: BTreeMap::new(),
            touched_tooltip_rows: BTreeSet::new(),
            tooltip_row_scaffolds: BTreeSet::new(),
            body_witness: BTreeMap::new(),
            pending: Vec::new(),
            decl_renames: None,
            deferred_spans: std::collections::VecDeque::new(),
            hole_sites: Vec::new(),
            holes: Vec::new(),
            or_null_sites: Vec::new(),
            classes: &classes,
            instances: &instances,
            inst_keys: &inst_keys,
            canonical: &canonical,
            constrained,
            cur_self: None,
            wanted: Vec::new(),
            num_default: Vec::new(),
            neg_default: Vec::new(),
            index_ops: Vec::new(),
            dicts: BTreeMap::new(),
            row_ctx: Vec::new(),
            cur_row: None,
            handler_stack: Vec::new(),
            operation_uses: OperationUses::default(),
            precise_calls: BTreeMap::new(),
            handler_nodes: BTreeSet::new(),
            handler_residuals: BTreeMap::new(),
            generalized_lets: BTreeSet::new(),
        };
        // Check each strongly-connected component after its callee components, so
        // a forward reference (notably one into a stdlib module merged after the
        // prelude) sees a generalized type, not a structure-free stub. A singleton
        // (the common case, including a self-recursive function) is inferred on its
        // own; a mutually recursive group is inferred together against shared
        // monomorphic variables. `infos` is rebuilt in declaration order afterward
        // so downstream output is unaffected by the visiting order.
        for component in deps::dep_sccs(prog) {
            if component.len() == 1 {
                let d = &prog.fns[component[0]];
                if d.konst {
                    let (ty, effs) = tc.infer_const(&env, d).map_err(|e| e.in_fn(&d.name))?;
                    require_pure_konst(d, &effs)?;
                    env.insert(Sym::from(&d.name), ty.clone());
                    infos.push(DeclInfo {
                        name: d.name.clone(),
                        params: Vec::new(),
                        ty,
                        effects: Effects::new(),
                        pure: true,
                    });
                    continue;
                }
                // Effect-row inference is principal: `infer_decl` discovers the
                // row on its own; the purity checks (konst here, instance methods
                // in `check_instance`) read the same principal inferred row.
                let ty = tc.infer_decl(&env, d).map_err(|e| e.in_fn(&d.name))?;
                env.insert(Sym::from(&d.name), ty.clone());
                let witness =
                    tc.body_witness
                        .get(&d.name)
                        .ok_or_else(|| TypeError::InternalInvariant {
                            msg: format!("no body-effect witness recorded for `{}`", d.name),
                        })?;
                infos.push(finalize_fn(d, ty, witness, &mut warnings)?);
                continue;
            }
            // A mutually recursive group; the whole group is inferred together,
            // and `infer_scc` holds any constant member to its inferred purity.
            let members: Vec<&_> = component.iter().map(|&di| &prog.fns[di]).collect();
            let tys = tc.infer_scc(&mut env, &members)?;
            for (&di, ty) in component.iter().zip(tys) {
                let d = &prog.fns[di];
                if d.konst {
                    infos.push(DeclInfo {
                        name: d.name.clone(),
                        params: Vec::new(),
                        ty,
                        effects: Effects::new(),
                        pure: true,
                    });
                } else {
                    let witness = tc.body_witness.get(&d.name).ok_or_else(|| {
                        TypeError::InternalInvariant {
                            msg: format!("no body-effect witness recorded for `{}`", d.name),
                        }
                    })?;
                    infos.push(finalize_fn(d, ty, witness, &mut warnings)?);
                }
            }
        }
        for inst in &prog.instances {
            // `check_instance` checks each method against its class signature and,
            // for a method whose signature is not effect-polymorphic, holds it to
            // its principal inferred purity (an effect-polymorphic method like
            // `fmap` may perform the effects flowing through its row variable).
            tc.check_instance(
                &env,
                inst,
                &instances[&Sym::from(&inst.name)],
                &classes[&Sym::from(&inst.class)],
            )?;
        }
        // Every `This(e)` element is now zonked; hold each to the non-null rule.
        tc.check_or_null_sites()?;
        field_res = tc.field_res;
        unboxed_field = tc.unboxed_field;
        path_res = tc.path_res;
        fixed = tc.fixed;
        span_types = tc.span_types;
        tooltip_rows = tc.tooltip_rows;
        method_effects = std::mem::take(&mut tc.method_effects);
        handler_nodes = tc.handler_nodes;
        handler_residuals = tc.handler_residuals;
        generalized_lets = tc.generalized_lets;
        dicts = tc.dicts;
        constrained_final = tc.constrained;
        holes = tc.holes;
    }
    holes.sort_by_key(|h| (h.start, h.end, h.name.clone()));
    // Restore declaration order: `infos` was filled in dependency order, but
    // consumers (signatures listing, snapshots) expect source order.
    {
        let pos: BTreeMap<&str, usize> = prog
            .fns
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.as_str(), i))
            .collect();
        infos.sort_by_key(|info| pos.get(info.name.as_str()).copied().unwrap_or(usize::MAX));
    }
    Ok(Checked::new(CheckedView {
        interface: InterfaceFacts { env, seeds },
        defs: DeclFacts {
            data,
            ctors,
            decls: infos,
            eff_ops,
        },
        facts: NodeFacts::from_tables(
            field_res,
            unboxed_field,
            path_res,
            fixed,
            span_types,
            dicts,
            tooltip_rows,
            handler_nodes,
            handler_residuals,
            generalized_lets,
        ),
        dispatch: DispatchFacts {
            classes,
            instances,
            inst_keys,
            canonical,
            methods,
            method_effects,
            constrained: constrained_final,
        },
        reports: Reports { warnings, holes },
    }))
}

/// Render the dedicated diagnostic corresponding to one or more hole reports.
#[must_use]
pub fn hole_error(holes: &[HoleReport]) -> TypeError {
    let Some(first) = holes.first() else {
        return TypeError::InternalInvariant {
            msg: "typed-hole diagnostic requested without a hole".into(),
        };
    };
    let mut error = ErrKind::TypedHole {
        report: first.clone(),
    }
    .at(first.span());
    for hole in &holes[1..] {
        error = error.note(format!(
            "also `?{}` at {}..{}: expected {} with effects {}",
            hole.name, hole.start, hole.end, hole.expected, hole.effects
        ));
    }
    error
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr(checked: &Checked, e: &S<Expr<Core>>) -> Result<(Type, Effects), TypeError> {
    infer_expr_env(checked, &Env::new(), e)
}

/// A standalone expression plus every node fact established by its inference.
/// The REPL hands this artifact to elaboration as one unit so its fresh numeric
/// node identities can never read facts from the resident program.
pub(crate) struct CheckedExpr {
    pub(crate) ty: Type,
    pub(crate) effects: Effects,
    #[cfg(feature = "native")]
    pub(crate) facts: NodeFacts,
    pub(crate) holes: Vec<HoleReport>,
    dicts: DictTable,
}

/// Infer the complete artifact elaboration needs for a standalone expression.
///
/// # Errors
/// Fails for ordinary type errors, and for typed holes unless `allow_holes` is
/// true.
#[cfg(feature = "native")]
pub(crate) fn infer_checked_expr(
    checked: &Checked,
    e: &S<Expr<Core>>,
    allow_holes: bool,
) -> Result<CheckedExpr, TypeError> {
    let inferred = infer_expr_full(checked, &Env::new(), e)?;
    if allow_holes || inferred.holes.is_empty() {
        Ok(inferred)
    } else {
        Err(hole_error(&inferred.holes))
    }
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_env(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects), TypeError> {
    let inferred = infer_expr_full(checked, extra, e)?;
    if inferred.holes.is_empty() {
        Ok((inferred.ty, inferred.effects))
    } else {
        Err(hole_error(&inferred.holes))
    }
}

/// Infer an expression while returning, rather than rejecting, typed holes.
///
/// # Errors
/// Fails for ordinary type errors.
pub fn infer_expr_allow_holes(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, Vec<HoleReport>), TypeError> {
    let inferred = infer_expr_full(checked, extra, e)?;
    Ok((inferred.ty, inferred.effects, inferred.holes))
}

// Parse the canonical signature carried by a checked module interface.
pub(crate) use crate::types::sig::parse_checked_signature;

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_dicts(
    checked: &Checked,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable), TypeError> {
    let inferred = infer_expr_full(checked, &Env::new(), e)?;
    if inferred.holes.is_empty() {
        Ok((inferred.ty, inferred.effects, inferred.dicts))
    } else {
        Err(hole_error(&inferred.holes))
    }
}

/// Dictionary-producing expression inference for deferred interpreter holes.
///
/// # Errors
/// Fails for ordinary type errors.
pub fn infer_expr_dicts_allow_holes(
    checked: &Checked,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable, Vec<HoleReport>), TypeError> {
    let inferred = infer_expr_full(checked, &Env::new(), e)?;
    Ok((
        inferred.ty,
        inferred.effects,
        inferred.dicts,
        inferred.holes,
    ))
}

fn infer_expr_full(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<CheckedExpr, TypeError> {
    let mut env = checked.interface.env.clone();
    env.extend(extra.iter().map(|(k, v)| (*k, v.clone())));
    // Re-inference shares `eff_ops`, whose var-state markers lowered to the
    // pinned existentials below `seeds`. The fresh context must seed the same
    // floor, else subsume references existentials that do not exist.
    let mut tc = Tc {
        ctx: (0..checked.interface.seeds).map(Entry::Ex).collect(),
        next: checked.interface.seeds,
        seeds: checked.interface.seeds,
        ctors: &checked.defs.ctors,
        data: &checked.defs.data,
        eff_ops: &checked.defs.eff_ops,
        field_res: BTreeMap::new(),
        unboxed_field: BTreeMap::new(),
        path_res: PathRes::new(),
        fixed: BTreeMap::new(),
        span_types: BTreeMap::new(),
        track_tooltips: false,
        pending_tooltip_rows: Vec::new(),
        tooltip_rows: BTreeMap::new(),
        method_effects: BTreeMap::new(),
        touched_tooltip_rows: BTreeSet::new(),
        tooltip_row_scaffolds: BTreeSet::new(),
        body_witness: BTreeMap::new(),
        pending: Vec::new(),
        decl_renames: None,
        deferred_spans: std::collections::VecDeque::new(),
        hole_sites: Vec::new(),
        holes: Vec::new(),
        or_null_sites: Vec::new(),
        classes: &checked.dispatch.classes,
        instances: &checked.dispatch.instances,
        inst_keys: &checked.dispatch.inst_keys,
        canonical: &checked.dispatch.canonical,
        constrained: checked.dispatch.constrained.clone(),
        cur_self: None,
        wanted: Vec::new(),
        num_default: Vec::new(),
        neg_default: Vec::new(),
        index_ops: Vec::new(),
        dicts: BTreeMap::new(),
        row_ctx: Vec::new(),
        cur_row: None,
        handler_stack: Vec::new(),
        operation_uses: OperationUses::default(),
        precise_calls: BTreeMap::new(),
        handler_nodes: BTreeSet::new(),
        handler_residuals: BTreeMap::new(),
        generalized_lets: BTreeSet::new(),
    };
    let (t, effs) = tc.scoped_effects(|tc| {
        let t = tc.synth(&env, e)?;
        tc.resolve_all()?;
        Ok(t)
    })?;
    tc.check_or_null_sites()?;
    tc.flush_holes();
    let t = tc.apply(&t);
    let g = tc.generalize(&env, &t);
    tc.holes.sort_by_key(|h| (h.start, h.end, h.name.clone()));
    let dicts = tc.dicts;
    #[cfg(feature = "native")]
    let facts = NodeFacts::from_tables(
        tc.field_res,
        tc.unboxed_field,
        tc.path_res,
        tc.fixed,
        tc.span_types,
        dicts.clone(),
        tc.tooltip_rows,
        tc.handler_nodes,
        tc.handler_residuals,
        tc.generalized_lets,
    );
    Ok(CheckedExpr {
        ty: g,
        effects: effs,
        #[cfg(feature = "native")]
        facts,
        holes: tc.holes,
        dicts,
    })
}

// A checker context for read-only type queries. Search and synthesis use the
// same higher-rank and row-aware relation as ordinary checking, but infer no
// declarations and therefore need only an empty seed plus solver state.
// Native-only with its two callers below: the CLI drives every type query.
#[cfg(feature = "native")]
fn query_tc(seed: &TypecheckSeed) -> Tc<'_> {
    Tc {
        ctx: Vec::new(),
        next: 0,
        seeds: 0,
        ctors: seed.constructors(),
        data: seed.data_types(),
        eff_ops: seed.effect_operations(),
        field_res: BTreeMap::new(),
        unboxed_field: BTreeMap::new(),
        path_res: PathRes::new(),
        fixed: BTreeMap::new(),
        span_types: BTreeMap::new(),
        track_tooltips: false,
        pending_tooltip_rows: Vec::new(),
        tooltip_rows: BTreeMap::new(),
        method_effects: BTreeMap::new(),
        touched_tooltip_rows: BTreeSet::new(),
        tooltip_row_scaffolds: BTreeSet::new(),
        body_witness: BTreeMap::new(),
        pending: Vec::new(),
        decl_renames: None,
        deferred_spans: std::collections::VecDeque::new(),
        hole_sites: Vec::new(),
        holes: Vec::new(),
        or_null_sites: Vec::new(),
        classes: seed.classes(),
        instances: seed.instances(),
        inst_keys: seed.instance_keys(),
        canonical: seed.canonical_instances(),
        constrained: seed.constrained().clone(),
        cur_self: None,
        wanted: Vec::new(),
        num_default: Vec::new(),
        neg_default: Vec::new(),
        index_ops: Vec::new(),
        dicts: BTreeMap::new(),
        row_ctx: Vec::new(),
        cur_row: None,
        handler_stack: Vec::new(),
        operation_uses: OperationUses::default(),
        precise_calls: BTreeMap::new(),
        handler_nodes: BTreeSet::new(),
        handler_residuals: BTreeMap::new(),
        generalized_lets: BTreeSet::new(),
    }
}

/// Whether `actual` can be used where `expected` is required.
///
/// This is the typechecker's real subsumption relation, including forall
/// instantiation, skolemization, function variance, and effect-row matching.
#[cfg(feature = "native")]
#[must_use]
pub(crate) fn type_subsumes(actual: &Type, expected: &Type) -> bool {
    if actual == expected {
        return true;
    }
    let seed = TypecheckSeed::default();
    query_tc(&seed).subtype(actual, expected).is_ok()
}

/// Parameter types for applying `function` to produce `expected`.
///
/// Leading type and row quantifiers are instantiated before the result is
/// matched. Returned domains carry the substitutions learned by that match.
#[cfg(feature = "native")]
#[must_use]
pub(crate) fn application_params(function: &Type, expected: &Type) -> Option<Vec<Type>> {
    let seed = TypecheckSeed::default();
    let mut tc = query_tc(&seed);
    let mut current = function.clone();
    let opened = loop {
        current = match current {
            Type::Forall(name, body) => {
                let fresh = tc.push_ex();
                body.subst_var(name, &Type::Exist(fresh))
            }
            Type::RowForall(name, body) => {
                let fresh = tc.push_ex_row();
                body.subst_row_var(name, &EffRow::Exist(fresh))
            }
            other => break other,
        };
    };
    let Type::Fun(params, _effects, result) = opened else {
        return None;
    };
    tc.subtype(&result, expected).ok()?;
    let applied = Type::Tuple(params.iter().map(|param| tc.apply(param)).collect());
    let generalized = tc.generalize(&Env::new(), &applied);
    let mut body = &generalized;
    while let Type::Forall(_, next) | Type::RowForall(_, next) = body {
        body = next;
    }
    match body {
        Type::Tuple(params) => Some(params.clone()),
        _ => None,
    }
}
