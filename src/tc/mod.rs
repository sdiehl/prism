use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use crate::error::TypeError;
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl, Expr, NodeId, Program, S};
use crate::types::effects;
use crate::types::ty::{EffRow, Effects, Type};

mod classes;
mod context;
mod coverage;
mod env;
mod infer;
mod pat;
mod subsume;

pub type Env = BTreeMap<Sym, Type>;

#[derive(Clone, Debug)]
pub struct DataInfo {
    pub params: Vec<String>,
    pub ctors: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct CtorInfo {
    pub type_name: Sym,
    pub params: Vec<Sym>,
    pub args: Vec<Type>,
    pub tag: usize,
    pub fields: Vec<Sym>,
}

#[derive(Clone, Debug)]
pub struct DeclInfo {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Type,
    pub effects: Effects,
}

#[derive(Clone, Debug)]
pub struct EffOpInfo {
    pub effect_name: Sym,
    pub eff_params: Vec<Sym>,
    pub params: Vec<Type>,
    pub ret: Type,
}

// Instance dispatch key: the head constructor of an instance head type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HeadKey {
    Int,
    I64,
    U64,
    Bool,
    Float,
    Char,
    Str,
    Unit,
    Con(Sym),
}

pub type InstKeys = BTreeMap<(Sym, HeadKey), Vec<Sym>>;

// The canonical-instance designation: for a `(class, head)` that several
// instances share, the one implicit resolution selects. Built from `canonical`
// decls beside `inst_keys`, keying each `(class, head)` to the chosen instance
// name so resolution is deterministic instead of ambiguous.
pub type Canon = BTreeMap<(Sym, HeadKey), Sym>;

// How a constraint is discharged at a use site: a top-level instance dictionary
// (applied to its context dictionaries) or the i-th hidden dictionary parameter
// of the enclosing constrained function.
#[derive(Clone, Debug, PartialEq)]
pub enum Dict {
    Global(String, Vec<Self>),
    Param(usize),
    // Project a superclass dictionary from a subclass dictionary: the `idx`-th
    // leading (superclass) field of the dict cell for class `subclass`. Used to
    // discharge `Eq(a)` from a `given Ord(a)` when `Ord` declares `Eq` a super.
    Super(Box<Self>, String, usize),
}

// `NodeId` is the identity of a dispatch site, assigned once by `assign_ids`
// after desugar so it is unique per node and stable between typecheck and
// elaboration; resolve_all ICEs on conflicting records at one id.
pub type DictTable = BTreeMap<NodeId, Vec<Dict>>;

#[derive(Clone, Debug)]
pub struct ClassInfo {
    pub param: Sym,
    // Superclass class names; each instance carries one resolved superclass
    // dictionary per entry, stored as a leading field of its dict cell.
    pub supers: Vec<Sym>,
    pub methods: Vec<(Sym, Type)>,
}

#[derive(Clone, Debug)]
pub struct InstInfo {
    pub class: Sym,
    pub head: Type,
    // The module that defines this instance (empty for root), for the orphan and
    // overlap rules and for naming provenance in ambiguity diagnostics.
    pub module: String,
    pub context: Vec<(Sym, Type)>,
    // Resolved superclass obligations `(super_class, head)`, one per the class's
    // declared supers, discharged at each use site and embedded in the dict cell.
    pub supers: Vec<(Sym, Type)>,
}

// Per update path, the rebuild chain: one (ctor name, field index, arity)
// step per path segment, resolved at the update expression's node.
pub type PathRes = BTreeMap<NodeId, Vec<Vec<(String, usize, usize)>>>;

/// A non-fatal diagnostic raised during checking (an orphan or overlapping
/// instance). Carries a span so it can be rendered like an error but does not
/// stop compilation.
#[derive(Clone, Debug)]
pub struct Warning {
    pub span: Span,
    pub msg: String,
}

#[derive(Clone, Debug)]
pub struct Checked {
    pub env: Env,
    pub data: BTreeMap<String, DataInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub decls: Vec<DeclInfo>,
    pub eff_ops: BTreeMap<String, EffOpInfo>,
    pub field_res: BTreeMap<NodeId, (String, usize, usize)>,
    pub path_res: PathRes,
    pub fixed: BTreeMap<NodeId, Type>,
    pub span_types: BTreeMap<NodeId, Type>,
    pub classes: BTreeMap<Sym, ClassInfo>,
    pub instances: BTreeMap<Sym, InstInfo>,
    pub inst_keys: InstKeys,
    pub canonical: Canon,
    pub methods: BTreeMap<Sym, (Sym, usize)>,
    pub constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
    pub dicts: DictTable,
    pub seeds: u32,
    pub warnings: Vec<Warning>,
}

// A subsumption failure. `Fail` is a plain mismatch the caller renders with its
// own span and message. `Ice` is a broken internal invariant that must surface
// as a diagnostic instead of a raw backtrace.
enum TcErr {
    Fail(String),
    Ice(String),
}

impl TcErr {
    // Attach a span: mismatches become located errors, ICEs pass through.
    fn at(self, span: Span) -> TypeError {
        match self {
            Self::Fail(msg) => TypeError::Other { span, msg },
            Self::Ice(msg) => TypeError::Ice { msg },
        }
    }

    // Replace a mismatch message, ICEs pass through.
    fn or_fail(self, msg: String) -> Self {
        match self {
            Self::Fail(_) => Self::Fail(msg),
            ice @ Self::Ice(_) => ice,
        }
    }

    // Replace a mismatch with the caller's diagnostic, ICEs pass through.
    fn or(self, fallback: TypeError) -> TypeError {
        match self {
            Self::Fail(_) => fallback,
            Self::Ice(msg) => TypeError::Ice { msg },
        }
    }
}

#[derive(Clone, Debug)]
enum Entry {
    Uni(Sym),
    RowUni(Sym),
    Ex(u32),
    Solved(u32, Type),
    Marker(u32),
    ExRow(u32),
    SolvedRow(u32, EffRow),
}

// One dispatch site: the constraints instantiated at `span`, resolved together
// into the site's dict vector at the end of the declaration.
struct Wanted {
    // Identity of the dispatch site, the key its resolved dicts land under.
    id: NodeId,
    // Source span, kept for the ambiguity/no-instance diagnostic's caret.
    span: Span,
    items: Vec<(String, Type, Option<String>)>,
}

// A deferred indexed read/write, resolved by head-type dispatch at the end of
// the declaration. `recv`/`key` are the synthed operand types (applied at
// resolution); `result` is the element existential to solve (and the read's
// result type); `val` is `Some(value type)` for a write (checked against the
// element type), `None` for a read (which also performs `Fail`).
struct IndexOp {
    span: Span,
    recv_span: Span,
    recv: Type,
    key: Type,
    result: u32,
    val: Option<Type>,
}

struct Tc<'a> {
    ctx: Vec<Entry>,
    next: u32,
    seeds: u32,
    ctors: &'a BTreeMap<String, CtorInfo>,
    data: &'a BTreeMap<String, DataInfo>,
    eff_ops: &'a BTreeMap<String, EffOpInfo>,
    field_res: BTreeMap<NodeId, (String, usize, usize)>,
    path_res: PathRes,
    fixed: BTreeMap<NodeId, Type>,
    span_types: BTreeMap<NodeId, Type>,
    pending: Vec<(NodeId, Type)>,
    classes: &'a BTreeMap<Sym, ClassInfo>,
    instances: &'a BTreeMap<Sym, InstInfo>,
    inst_keys: &'a InstKeys,
    canonical: &'a Canon,
    constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
    // The named function whose body is currently being checked, with its self
    // type and the class constraints in force. `None` when no self scope is
    // active: the Option makes the "not checking a named body" state explicit
    // and the non-nesting invariant enforceable by save/restore.
    cur_self: Option<SelfRef>,
    wanted: Vec<Wanted>,
    // Numeric operands left ambiguous at an arithmetic/comparison operator: each
    // (node id, span, operand type) is resolved in one pass at the end of the
    // declaration (`resolve_all`), so a later use can fix the type to a
    // fixed-width lane before the otherwise-`Int` default applies. The id keys
    // the `fixed` record; the span blames a non-numeric operand. Symmetric in
    // the two operands.
    num_default: Vec<(NodeId, Span, Type)>,
    // Indexed reads/writes (`a[i]`, `a[i] := v`) whose receiver type was not yet
    // resolved at synth (a `var`'s state existential is solved only once its
    // initializer is checked). Each is dispatched on the receiver's head type in
    // one pass at the end of the declaration (`resolve_all`, before `num_default`
    // so an index's element type is known to numeric defaulting).
    index_ops: Vec<IndexOp>,
    dicts: BTreeMap<NodeId, Vec<Dict>>,
    // Innermost-last instantiation scopes for parametric effects: each entry
    // ties an effect name to the type args in force (handler or latent row).
    row_ctx: Vec<(Sym, Vec<Type>)>,
    // The ambient effect obligation: an open row existential (`tail`) that every
    // effectful action in the code under check unifies into, plus the concrete
    // labels already in its fixed prefix. A handler scopes a fresh one for its
    // body and discharges the labels it names. Set per declaration / per handler
    // body; `None` when no scope is active. Tail and prefix move in lockstep so
    // they cannot desync.
    cur_row: Option<RowScope>,
    // Innermost-last stack of active handler bodies. A `mask<E>` marks the
    // nearest frame that handles `E` as not discharging it, so the masked
    // operation tunnels past that one handler and stays in the residual row
    // (the handler it skips is the innermost enclosing one, by construction).
    handler_stack: Vec<HandlerFrame>,
}

// One active handler while its body is checked: the effects its arms handle,
// and those a `mask` inside the body has tunnelled past it.
struct HandlerFrame {
    handled: BTreeSet<Sym>,
    masked: BTreeSet<Sym>,
}

// Ambient self-reference state for the body of a named declaration.
struct SelfRef {
    name: String,
    self_ty: Type,
    constraints: Vec<(String, Type)>,
}

// Open row existential tail plus the concrete labels in its fixed prefix.
// Absorbing a callee row skips the prefix labels so a direct named call does
// not duplicate a label.
struct RowScope {
    tail: u32,
    prefix: BTreeSet<Sym>,
}

// The concrete effects a declaration performs: the labels of its inferred
// function row (peeling quantifiers). A polymorphic row tail contributes none;
// a non-function value performs nothing observable in its type.
fn concrete_effects(ty: &Type) -> Effects {
    let mut t = ty;
    while let Type::Forall(_, b) | Type::RowForall(_, b) = t {
        t = b;
    }
    match t {
        Type::Fun(_, row, _) => row.labels().iter().map(|l| l.name).collect(),
        _ => Effects::new(),
    }
}

// A top-level constant must be effect-free: its initializer runs once at load
// with no handler in scope. The effects are the body's principal inferred row
// (its `konst` body is checked under a fresh ambient row whose labels are read
// off here), so the check is exact rather than a syntactic over-approximation.
pub(super) fn require_pure_konst(d: &Decl<Core>, effs: &Effects) -> Result<(), TypeError> {
    if !effs.is_empty() {
        let list: Vec<String> = effs.iter().map(Sym::to_string).collect();
        return Err(TypeError::Other {
            span: d.body.span,
            msg: format!(
                "top-level constant `{}` must be effect-free; it performs {}",
                d.name,
                list.join(", ")
            ),
        });
    }
    Ok(())
}

// The post-inference checks for a function: reconcile the call-graph set pass
// against the inferred row, enforce `borrow`-implies-pure, and check the declared
// effect annotation. Returns the `DeclInfo` to record. Shared by the singleton
// and mutually recursive driver paths.
fn finalize_fn(
    d: &Decl<Core>,
    ty: Type,
    warnings: &mut Vec<Warning>,
) -> Result<DeclInfo, TypeError> {
    // The labels of the inferred row. Effect-row inference is now principal: it
    // discovers every effect on its own (direct performs, applied effect-carrying
    // callees, builtin rows, `mask`), so the row is the single source of truth.
    // The old `set-pass ⊆ inferred` reconciliation is gone with the seed it
    // guarded: the set pass over-approximates effect-polymorphic and
    // higher-order-laundered effects as concrete labels, so it can only disagree
    // by over-reporting now. Real under-coverage is caught downstream by
    // `reconcile_effects` (lowered ops vs the row) and the parity oracle.
    let inferred = concrete_effects(&ty);
    if d.params.iter().any(|p| p.borrow) && !inferred.is_empty() {
        let list: Vec<String> = inferred.iter().map(Sym::to_string).collect();
        return Err(TypeError::Other {
            span: d.span,
            msg: format!(
                "`{}` has a `borrow` parameter but is not pure; it performs {}",
                d.name,
                list.join(", ")
            ),
        });
    }
    if let Some(declared) = &d.eff {
        let declared_set: BTreeSet<Sym> = declared.iter().map(|l| Sym::from(&l.name)).collect();
        for eff in &inferred {
            if !declared_set.contains(eff) {
                return Err(TypeError::Other {
                    span: d.body.span,
                    msg: format!("in `{}`: effect `{eff}` not declared in annotation", d.name),
                });
            }
        }
        // The reverse direction is sound (a pure body satisfies an effectful
        // annotation by subsumption) but the annotation then disagrees with the
        // inferred row, so warn rather than reject: a declared effect the body
        // never performs is dead weight.
        for eff in &declared_set {
            if !inferred.contains(eff) {
                warnings.push(Warning {
                    span: d.span,
                    msg: format!(
                        "in `{}`: effect `{eff}` declared in the annotation but never performed",
                        d.name
                    ),
                });
            }
        }
    }
    Ok(DeclInfo {
        name: d.name.clone(),
        params: d.params.iter().map(|p| p.name.clone()).collect(),
        ty,
        effects: inferred,
    })
}

/// # Errors
/// Fails when the program does not type check.
pub fn check(prog: &Program<Core>) -> Result<Checked, TypeError> {
    let (mut data, mut ctors, eff_ops, mut env) = env::build_data(prog)?;
    let seeds = env::seed_var_states(&eff_ops);
    let (classes, instances, inst_keys, canonical, methods, mut constrained, mut warnings) =
        classes::build_classes(prog, &mut data, &mut ctors, &mut env)?;
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
            return Err(TypeError::Other {
                span: d.span,
                msg: format!(
                    "`{}` has a where clause and needs full parameter and return type annotations",
                    d.name
                ),
            });
        }
        let mut cs = Vec::new();
        for c in &d.constraints {
            if !classes.contains_key(&Sym::from(&c.class)) {
                return Err(TypeError::Other {
                    span: c.span,
                    msg: format!("unknown class {}", c.class),
                });
            }
            cs.push((Sym::from(&c.class), env::convert_data(&c.ty)));
        }
        constrained.insert(Sym::from(&d.name), (env::fn_stub(d), cs));
    }
    let field_res;
    let path_res;
    let fixed;
    let span_types;
    let dicts;
    let constrained_final;
    {
        let mut tc = Tc {
            ctx: (0..seeds).map(Entry::Ex).collect(),
            next: seeds,
            seeds,
            ctors: &ctors,
            data: &data,
            eff_ops: &eff_ops,
            field_res: BTreeMap::new(),
            path_res: PathRes::new(),
            fixed: BTreeMap::new(),
            span_types: BTreeMap::new(),
            pending: Vec::new(),
            classes: &classes,
            instances: &instances,
            inst_keys: &inst_keys,
            canonical: &canonical,
            constrained,
            cur_self: None,
            wanted: Vec::new(),
            num_default: Vec::new(),
            index_ops: Vec::new(),
            dicts: BTreeMap::new(),
            row_ctx: Vec::new(),
            cur_row: None,
            handler_stack: Vec::new(),
        };
        // Check each strongly-connected component after its callee components, so
        // a forward reference (notably one into a stdlib module merged after the
        // prelude) sees a generalized type, not a structure-free stub. A singleton
        // (the common case, including a self-recursive function) is inferred on its
        // own; a mutually recursive group is inferred together against shared
        // monomorphic variables. `infos` is rebuilt in declaration order afterward
        // so downstream output is unaffected by the visiting order.
        for component in effects::dep_sccs(prog) {
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
                    });
                    continue;
                }
                // Effect-row inference is principal: `infer_decl` discovers the
                // row on its own. There is no separate set pass: the purity
                // checks (konst here, instance methods in `check_instance`) read
                // the same principal inferred row.
                let ty = tc.infer_decl(&env, d).map_err(|e| e.in_fn(&d.name))?;
                env.insert(Sym::from(&d.name), ty.clone());
                infos.push(finalize_fn(d, ty, &mut warnings)?);
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
                    });
                } else {
                    infos.push(finalize_fn(d, ty, &mut warnings)?);
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
        field_res = tc.field_res;
        path_res = tc.path_res;
        fixed = tc.fixed;
        span_types = tc.span_types;
        dicts = tc.dicts;
        constrained_final = tc.constrained;
    }
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
    Ok(Checked {
        env,
        data,
        ctors,
        field_res,
        path_res,
        fixed,
        span_types,
        decls: infos,
        eff_ops,
        classes,
        instances,
        inst_keys,
        canonical,
        methods,
        constrained: constrained_final,
        dicts,
        seeds,
        warnings,
    })
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr(checked: &Checked, e: &S<Expr<Core>>) -> Result<(Type, Effects), TypeError> {
    infer_expr_env(checked, &Env::new(), e)
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_env(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects), TypeError> {
    let (t, eff, _) = infer_expr_full(checked, extra, e)?;
    Ok((t, eff))
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_dicts(
    checked: &Checked,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable), TypeError> {
    infer_expr_full(checked, &Env::new(), e)
}

fn infer_expr_full(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable), TypeError> {
    let mut env = checked.env.clone();
    env.extend(extra.iter().map(|(k, v)| (*k, v.clone())));
    // Re-inference shares `eff_ops`, whose var-state markers lowered to the
    // pinned existentials below `seeds`. The fresh context must seed the same
    // floor, else subsume references existentials that do not exist.
    let mut tc = Tc {
        ctx: (0..checked.seeds).map(Entry::Ex).collect(),
        next: checked.seeds,
        seeds: checked.seeds,
        ctors: &checked.ctors,
        data: &checked.data,
        eff_ops: &checked.eff_ops,
        field_res: BTreeMap::new(),
        path_res: PathRes::new(),
        fixed: BTreeMap::new(),
        span_types: BTreeMap::new(),
        pending: Vec::new(),
        classes: &checked.classes,
        instances: &checked.instances,
        inst_keys: &checked.inst_keys,
        canonical: &checked.canonical,
        constrained: checked.constrained.clone(),
        cur_self: None,
        wanted: Vec::new(),
        num_default: Vec::new(),
        index_ops: Vec::new(),
        dicts: BTreeMap::new(),
        row_ctx: Vec::new(),
        cur_row: None,
        handler_stack: Vec::new(),
    };
    let (t, effs) = tc.scoped_effects(|tc| {
        let t = tc.synth(&env, e)?;
        tc.resolve_all()?;
        Ok(t)
    })?;
    let t = tc.apply(&t);
    let g = tc.generalize(&env, &t);
    Ok((g, effs, tc.dicts))
}
