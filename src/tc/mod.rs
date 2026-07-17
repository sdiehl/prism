use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

use im::OrdMap;
use marginalia::Span;
use serde::{Deserialize, Serialize};

use crate::error::{ErrKind, TypeError};
pub use crate::error::{HoleBinding, HoleCandidate, HoleReport};
use crate::hir::{HandlerResidual, NodeFacts};
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl, Expr, Grade, NodeId, Program, S};
use crate::types::effects;
use crate::types::ty::{EffRow, Effects, Kind, Label, Type};

mod classes;
mod context;
mod coverage;
mod env;
pub(crate) use env::is_builtin_effect;
mod infer;
mod pat;
mod subsume;

const EMPTY_SUMMARY_COUNT: usize = 0;
const SUMMARY_COUNT_INCREMENT: usize = 1;

/// Persistent type environment with free-variable side indexes.
///
/// Cloning shares the ordered map, while the indexes let generalization inspect
/// only bindings that can constrain quantification instead of re-walking every
/// closed prelude scheme.
#[derive(Clone, Debug, Default)]
pub struct Env {
    types: OrdMap<Sym, Type>,
    free_exists: BTreeMap<u32, usize>,
    free_row_exists: BTreeMap<u32, usize>,
    free_type_vars: BTreeMap<Sym, usize>,
}

impl Env {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: Sym, ty: Type) -> Option<Type> {
        let summary = type_summary(&ty);
        let old = self.types.insert(name, ty);
        if let Some(previous) = &old {
            self.adjust_summary(&type_summary(previous), false);
        }
        self.adjust_summary(&summary, true);
        old
    }

    pub(crate) fn remove(&mut self, name: &Sym) -> Option<Type> {
        let old = self.types.remove(name);
        if let Some(previous) = &old {
            self.adjust_summary(&type_summary(previous), false);
        }
        old
    }

    fn adjust_summary(&mut self, summary: &TypeSummary, add: bool) {
        adjust_counts(&mut self.free_exists, summary.exists.iter().copied(), add);
        adjust_counts(
            &mut self.free_row_exists,
            summary.row_exists.iter().copied(),
            add,
        );
        adjust_counts(
            &mut self.free_type_vars,
            summary.type_vars.iter().copied(),
            add,
        );
    }

    fn free_exists(&self) -> impl Iterator<Item = u32> + '_ {
        self.free_exists.keys().copied()
    }

    fn free_row_exists(&self) -> impl Iterator<Item = u32> + '_ {
        self.free_row_exists.keys().copied()
    }

    fn free_type_vars(&self) -> impl Iterator<Item = Sym> + '_ {
        self.free_type_vars.keys().copied()
    }
}

impl Deref for Env {
    type Target = OrdMap<Sym, Type>;

    fn deref(&self) -> &Self::Target {
        &self.types
    }
}

impl Extend<(Sym, Type)> for Env {
    fn extend<T: IntoIterator<Item = (Sym, Type)>>(&mut self, iter: T) {
        for (name, ty) in iter {
            self.insert(name, ty);
        }
    }
}

impl FromIterator<(Sym, Type)> for Env {
    fn from_iter<T: IntoIterator<Item = (Sym, Type)>>(iter: T) -> Self {
        let mut env = Self::new();
        env.extend(iter);
        env
    }
}

struct TypeSummary {
    exists: BTreeSet<u32>,
    row_exists: BTreeSet<u32>,
    type_vars: BTreeSet<Sym>,
}

fn type_summary(ty: &Type) -> TypeSummary {
    let mut exists = BTreeSet::new();
    ty.free_exist(&mut exists);
    let mut row_exists = BTreeSet::new();
    ty.free_exist_row(&mut row_exists);
    let mut type_vars = BTreeSet::new();
    env::collect_type_vars(ty, &mut type_vars);
    TypeSummary {
        exists,
        row_exists,
        type_vars,
    }
}

fn adjust_counts<K: Ord>(
    counts: &mut BTreeMap<K, usize>,
    keys: impl IntoIterator<Item = K>,
    add: bool,
) {
    for key in keys {
        if add {
            *counts.entry(key).or_default() += SUMMARY_COUNT_INCREMENT;
        } else if let Some(count) = counts.get_mut(&key) {
            *count -= SUMMARY_COUNT_INCREMENT;
            if *count == EMPTY_SUMMARY_COUNT {
                counts.remove(&key);
            }
        }
    }
}

#[cfg(test)]
mod env_summary_tests {
    use super::{Env, Type};
    use crate::sym::Sym;

    const EXISTENTIAL: u32 = 17;

    #[test]
    fn replacing_shadowed_bindings_updates_free_variable_counts() {
        let mut env = Env::new();
        let first = Sym::from("first");
        let second = Sym::from("second");
        env.insert(first, Type::Exist(EXISTENTIAL));
        env.insert(second, Type::Exist(EXISTENTIAL));
        assert_eq!(env.free_exists().collect::<Vec<_>>(), [EXISTENTIAL]);

        env.insert(first, Type::Int);
        assert_eq!(env.free_exists().collect::<Vec<_>>(), [EXISTENTIAL]);
        env.insert(second, Type::Int);
        assert!(env.free_exists().next().is_none());
    }
}

#[cfg(test)]
mod typed_hole_tests {
    use super::{check, check_allow_holes};
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::desugar::desugar;

    fn core(src: &str) -> crate::syntax::ast::Program<crate::syntax::ast::Core> {
        let surface = parse(src).expect("parse typed-hole fixture").program;
        let resolved = resolve(surface).expect("resolve typed-hole fixture");
        desugar(resolved).expect("desugar typed-hole fixture")
    }

    #[test]
    fn report_is_structured_ranked_and_effect_aware() {
        let program = core("fn choose(x : Int, y : Bool) : Int ! {} = ?answer");
        let checked = check_allow_holes(&program).expect("holes are retained in allow mode");
        let [hole] = checked.holes.as_slice() else {
            panic!("expected one hole report, got {:?}", checked.holes);
        };
        assert_eq!(hole.name, "answer");
        assert_eq!(hole.expected, "Int");
        assert_eq!(hole.effects, "{}");
        assert!(hole.bindings.iter().any(|b| b.name == "x" && b.ty == "Int"));
        assert_eq!(hole.candidates.first().map(|c| c.name.as_str()), Some("x"));
        assert!(hole.candidates[0].exact);
        let json = serde_json::to_value(hole).expect("hole payload serializes");
        assert_eq!(json["expected"], "Int");
        assert_eq!(json["effects"], "{}");
    }

    #[test]
    fn ordinary_check_rejects_holes_with_the_dedicated_code() {
        let program = core("fn main() : Int = ?todo");
        let error = check(&program).expect_err("ordinary checking must reject holes");
        assert_eq!(error.code(), Some(crate::error::TYPED_HOLE.as_str()));
    }

    #[test]
    fn inferred_context_reports_an_open_effect_row() {
        let program = core("fn main() : Int = ?todo");
        let checked = check_allow_holes(&program).expect("allow mode");
        assert_eq!(checked.holes[0].effects, "{| e0}");
    }

    #[test]
    fn annotated_lambda_reports_its_open_effect_permission() {
        let program = core(
            "fn main() : (() -> Int ! {Exn | e}) = \
             ((\\() -> ?todo) : () -> Int ! {Exn | e})",
        );
        let checked = check_allow_holes(&program).expect("allow mode");
        assert_eq!(checked.holes[0].expected, "Int");
        assert_eq!(checked.holes[0].effects, "{Exn | e0}");
    }

    #[test]
    fn polymorphic_candidates_are_ranked_by_real_subsumption() {
        let program = core(
            "fn identity(x) = x\n\
             fn main() : ((Int) -> Int) ! {} = ?answer",
        );
        let checked = check_allow_holes(&program).expect("allow mode");
        let identity = checked.holes[0]
            .candidates
            .iter()
            .find(|candidate| candidate.name == "identity")
            .expect("polymorphic identity subsumes Int -> Int");
        assert!(
            !identity.exact,
            "instantiation is compatible, not identical"
        );
    }
}

#[cfg(test)]
mod residual_operation_tests {
    use super::{check, Checked};
    use crate::hir::{build, HandlerResidual};
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::ast::{Core, Expr, NodeId, Program};
    use crate::syntax::desugar::desugar;

    fn core(src: &str) -> Program<Core> {
        let surface = parse(src).expect("parse residual fixture").program;
        let resolved = resolve(surface).expect("resolve residual fixture");
        desugar(resolved).expect("desugar residual fixture")
    }

    fn checked(src: &str) -> (Program<Core>, Checked) {
        let program = core(src);
        let checked = check(&program).expect("check residual fixture");
        (program, checked)
    }

    fn function_body(program: &Program<Core>, name: &str) -> NodeId {
        program
            .fns
            .iter()
            .find(|function| function.name == name)
            .expect("fixture function")
            .body
            .id
    }

    fn residual<'a>(
        program: &Program<Core>,
        checked: &'a Checked,
        function: &str,
    ) -> &'a HandlerResidual {
        build(checked)
            .handler_residual(function_body(program, function))
            .expect("handler residual fact")
    }

    fn names(symbols: &[crate::sym::Sym]) -> Vec<&'static str> {
        symbols.iter().map(|symbol| symbol.as_str()).collect()
    }

    const ADJACENT: &str = "
effect E
  one() : Int
  two() : Int

fn run() : Int ! {} =
  handle (handle one() + two() with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    two() resume k => k(2),
    return r => r
  }
";

    #[test]
    fn adjacent_inline_partials_cancel_known_operation_subsets() {
        let (program, checked) = checked(ADJACENT);
        assert!(checked.decls[0].effects.is_empty());
        let outer = residual(&program, &checked, "run");
        assert!(outer.forwarded_operations().is_empty());
        assert!(outer.residual_operations().is_empty());
        assert!(outer.forwarded_effects().is_empty());
        assert!(!outer.has_open_row());

        let run = program
            .fns
            .iter()
            .find(|function| function.name == "run")
            .expect("run");
        let Expr::Handle(inner, ..) = &run.body.node else {
            panic!("run body must be the outer handler");
        };
        let inner = build(&checked)
            .handler_residual(inner.id)
            .expect("inner residual");
        assert_eq!(names(inner.forwarded_operations()), ["two"]);
        assert_eq!(names(inner.residual_operations()), ["two"]);
    }

    #[test]
    fn signature_rows_remain_opaque_across_adjacent_partials() {
        let source = ADJACENT.replace(
            "fn run() : Int ! {} =\n  handle (handle one() + two()",
            "fn work() : Int ! {E} = one() + two()\n\nfn run() : Int ! {E} =\n  handle (handle work()",
        );
        let (program, checked) = checked(&source);
        let run = checked
            .decls
            .iter()
            .find(|decl| decl.name == "run")
            .expect("run declaration");
        assert!(run.effects.iter().any(|effect| effect.as_str() == "E"));
        let outer = residual(&program, &checked, "run");
        assert_eq!(names(outer.forwarded_effects()), ["E"]);
        assert_eq!(names(outer.residual_effects()), ["E"]);

        let pure = source.replace("fn run() : Int ! {E}", "fn run() : Int ! {}");
        let program = core(&pure);
        check(&program).expect_err("an opaque signature row must not become locally pure");
    }

    #[test]
    fn handler_arm_uses_are_unioned_into_the_residual() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle one() with partial {
    one() resume k => two(),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert!(fact.forwarded_operations().is_empty());
        assert_eq!(names(fact.residual_operations()), ["two"]);
    }

    #[test]
    fn mask_forces_the_skipped_effect_to_remain_opaque() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle mask<E>(one()) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.forwarded_operations()), ["one"]);
        assert_eq!(names(fact.residual_operations()), ["one"]);
    }

    #[test]
    fn outer_partial_cancels_the_known_operation_masked_past_inner() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {} =
  handle (handle mask<E>(one()) with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
    }

    #[test]
    fn pure_mask_does_not_borrow_prior_same_effect_precision() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle (handle one() + mask<E>(5) with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.forwarded_effects()), ["E"]);
        assert_eq!(names(fact.residual_effects()), ["E"]);
    }

    #[test]
    fn parametric_direct_operation_keeps_singleton_precision() {
        let (_, checked) = checked(
            r"effect Choice(a)
  first(a) : a
  second(a) : a

fn run() : Int ! {} =
  handle first(1) with partial {
    first(x) resume k => k(x),
    return r => r
  }",
        );
        assert!(checked.decls[0].effects.is_empty());
    }

    #[test]
    fn thunk_operation_retains_its_latent_effect_row() {
        let (program, checked) = checked(
            r"effect Out
  out() : Int

effect Wrap
  wrap(() -> Int ! {Wrap | e}) : Int

fn run() : Int ! {Out, Wrap} =
  handle wrap(\() -> out()) with partial {
    wrap(th) resume k => k(0),
    return r => r
  }",
        );
        let run = checked
            .decls
            .iter()
            .find(|decl| decl.name == "run")
            .expect("run declaration");
        assert!(run.effects.iter().any(|effect| effect.as_str() == "Out"));
        assert!(run.effects.iter().any(|effect| effect.as_str() == "Wrap"));
        let fact = residual(&program, &checked, "run");
        assert!(fact.residual_operations().is_empty());
        assert_eq!(names(fact.forwarded_effects()), ["Wrap"]);
        assert_eq!(names(fact.residual_effects()), ["Out", "Wrap"]);
        assert!(fact.has_open_row());
    }

    #[test]
    fn synthesized_lambda_keeps_latent_operations_out_of_handler_residual() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn make() : (() -> Int ! {E}) =
  handle (\() -> two()) with partial {
    one() resume k => k(1),
    return f => f
  }",
        );
        let make = checked
            .decls
            .iter()
            .find(|decl| decl.name == "make")
            .expect("make declaration");
        assert!(make.effects.is_empty());
        let fact = residual(&program, &checked, "make");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
    }

    #[test]
    fn builtin_opaque_residual_is_valid_checked_hir() {
        let (program, checked) = checked(
            r"effect E
  one() : Int

fn run() : Unit ! {IO} =
  handle one() with partial {
    one() resume k => let _ = k(1) in mask<IO>(()),
    return r => ()
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.residual_effects()), ["IO"]);
    }

    #[test]
    fn operation_precision_does_not_cross_declaration_boundaries() {
        let (program, checked) = checked(
            r"effect Out
  out() : Int

effect Wrap
  wrap(() -> Int ! {Wrap | e}) : Int

effect E
  one() : Int
  two() : Int

fn leaves_open() : Int ! {Out, Wrap} = wrap(\() -> out())

fn clean() : Int ! {} =
  handle one() with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "clean");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
        assert!(!fact.has_open_row());
    }
}

#[derive(Clone, Debug)]
pub struct DataInfo {
    pub params: Vec<String>,
    // Kind of each parameter, positional and same length as `params`. Almost
    // always all `Kind::Type`; a `Kind::Row` entry marks a row-kinded parameter
    // (`type Cmd(a, e : Row)`), carried in `Con` spines as `Type::Row`, and a
    // `Kind::Nat` entry a dimension parameter (`type Vec(a, n : Nat)`), carried
    // as `Type::Nat`. These parameter kinds form the constructor's arrow, checked
    // against its arguments at each annotation (see `env::check_annot_rows`).
    pub param_kinds: Vec<Kind>,
    pub ctors: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorInfo {
    pub type_name: Sym,
    pub params: Vec<Sym>,
    // Kind of each parameter, parallel to `params`. Lets pattern matching open a
    // `Row`-kinded parameter with a fresh row existential (substituted into the
    // field types with `subst_row_var`) rather than a type existential.
    pub param_kinds: Vec<Kind>,
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
    // Declared resumption multiplicity of the op (see `ast::Grade`). Consumed by
    // effect lowering to decide which handlers may disable var-erasure; a
    // handler clause more general than this grade is rejected at desugar.
    pub grade: Grade,
}

impl EffOpInfo {
    // True when the op signature carries a free effect-row variable (a thunk
    // parameter whose row has an open tail, e.g. `() -> a ! {Eff | e}`). Such an
    // op must tie that variable to the ambient row at each perform site so the
    // thunk's extra effects flow out; see `Tc::bind_op_rows_to_ambient`.
    #[must_use]
    pub fn has_free_row_vars(&self) -> bool {
        let mut rows = BTreeSet::new();
        for p in &self.params {
            env::collect_row_vars(p, &mut rows);
        }
        env::collect_row_vars(&self.ret, &mut rows);
        !rows.is_empty()
    }

    // Instantiate the op's param/return types with the effect's type arguments,
    // substituting each declared effect parameter for the supplied argument.
    #[must_use]
    pub fn instantiate(&self, args: &[Type]) -> (Vec<Type>, Type) {
        let mut params = self.params.clone();
        let mut ret = self.ret.clone();
        for (p, t) in self.eff_params.iter().zip(args) {
            for q in &mut params {
                *q = q.subst_var(*p, t);
            }
            ret = ret.subst_var(*p, t);
        }
        (params, ret)
    }
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
    // A tuple has no nominal constructor, so it keys on its arity: `(a, b)` and
    // `(a, b, c)` are distinct heads a structural instance (`Serialize`) hangs on.
    Tuple(usize),
}

pub type InstKeys = BTreeMap<(Sym, HeadKey), Vec<Sym>>;

// The canonical-instance designation: for a `(class, head)` that several
// instances share, the one implicit resolution selects. Built from `canonical`
// decls beside `inst_keys`, keying each `(class, head)` to the chosen instance
// name so resolution is deterministic instead of ambiguous.
pub type Canon = BTreeMap<(Sym, HeadKey), Sym>;

/// Checked dependency facts used to typecheck one module without dependency
/// implementation bodies.
#[derive(Clone, Debug, Default)]
pub struct TypecheckSeed {
    pub env: Env,
    pub data: BTreeMap<String, DataInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub eff_ops: BTreeMap<String, EffOpInfo>,
    pub classes: BTreeMap<Sym, ClassInfo>,
    pub instances: BTreeMap<Sym, InstInfo>,
    pub inst_keys: InstKeys,
    pub canonical: Canon,
    pub methods: BTreeMap<Sym, (Sym, usize)>,
    pub constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
}

impl TypecheckSeed {
    /// Clone all checker facts from an already checked dependency closure.
    #[must_use]
    pub fn from_checked(checked: &Checked) -> Self {
        Self {
            env: checked.env.clone(),
            data: checked.data.clone(),
            ctors: checked.ctors.clone(),
            eff_ops: checked.eff_ops.clone(),
            classes: checked.classes.clone(),
            instances: checked.instances.clone(),
            inst_keys: checked.inst_keys.clone(),
            canonical: checked.canonical.clone(),
            methods: checked.methods.clone(),
            constrained: checked.constrained.clone(),
        }
    }

    /// Merge one dependency interface into this seed.
    pub fn extend(&mut self, other: Self) {
        self.env
            .extend(other.env.iter().map(|(name, ty)| (*name, ty.clone())));
        self.data.extend(other.data);
        self.ctors.extend(other.ctors);
        self.eff_ops.extend(other.eff_ops);
        self.classes.extend(other.classes);
        self.instances.extend(other.instances);
        for (key, names) in other.inst_keys {
            let entries = self.inst_keys.entry(key).or_default();
            entries.extend(names);
            entries.sort_by_key(|name| name.as_str());
            entries.dedup();
        }
        self.canonical.extend(other.canonical);
        self.methods.extend(other.methods);
        self.constrained.extend(other.constrained);
    }
}

// How a constraint is discharged at a use site: a top-level instance dictionary
// (applied to its context dictionaries) or the i-th hidden dictionary parameter
// of the enclosing constrained function.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Dict {
    Global(String, Vec<Self>),
    Param(usize),
    // Project a superclass dictionary from a subclass dictionary: the `idx`-th
    // leading (superclass) field of the dict cell for class `subclass`. Used to
    // discharge `Eq(a)` from a `given Ord(a)` when `Ord` declares `Eq` a super.
    Super(Box<Self>, String, usize),
    // A compiler-synthesized `Show` dictionary for a tuple type, carrying one
    // component `Show` dictionary per element. Tuples have no nominal head to
    // hang an instance on, so the elaborator materializes their dict cell from
    // these components (a structural `(a, b, ...)` printer).
    Tuple(Vec<Self>),
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
    pub(crate) origin: WarningOrigin,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum WarningOrigin {
    Surface,
    Decl(Sym),
    RootInstance(Sym),
    Imported,
}

#[derive(Clone, Debug)]
pub struct Checked {
    pub env: Env,
    pub data: BTreeMap<String, DataInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub decls: Vec<DeclInfo>,
    pub eff_ops: BTreeMap<String, EffOpInfo>,
    // Every per-node semantic fact checking established (resolution, evidence,
    // lanes, zonked node types), dense by NodeId. The former six NodeId side
    // tables, consolidated; elaboration reads it only through a `CheckedHir`.
    pub facts: NodeFacts,
    pub classes: BTreeMap<Sym, ClassInfo>,
    pub instances: BTreeMap<Sym, InstInfo>,
    pub inst_keys: InstKeys,
    pub canonical: Canon,
    pub methods: BTreeMap<Sym, (Sym, usize)>,
    pub constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
    pub seeds: u32,
    pub warnings: Vec<Warning>,
    /// Source-ordered typed-hole reports. Ordinary checking rejects a non-empty
    /// list; interpreter-only deferred checking returns it to the caller.
    pub holes: Vec<HoleReport>,
}

impl Checked {
    /// Each effect op keyed by its symbol to its declared resumption grade, the
    /// side table effect lowering consumes to decide which handlers may disable
    /// var-erasure. Ops absent here (a synthetic private effect) default to the
    /// most general grade at the consumer.
    #[must_use]
    pub fn op_grades(&self) -> BTreeMap<Sym, Grade> {
        self.eff_ops
            .iter()
            .map(|(name, info)| (Sym::from(name), info.grade))
            .collect()
    }
}

// A subsumption failure. `Fail` is a plain mismatch the caller renders with its
// own span and message. `Keep` is a mismatch that already carries its final,
// more precise message (a dimension clash naming both lengths): it survives a
// caller's structural override, taking only the caller's span. `Ice` is a broken
// internal invariant that must surface as a diagnostic instead of a raw backtrace.
enum TcErr {
    Fail(String),
    Keep(String),
    Ice(String),
}

impl TcErr {
    // Attach a span: mismatches become located errors, ICEs pass through.
    fn at(self, span: Span) -> TypeError {
        match self {
            Self::Fail(msg) | Self::Keep(msg) => TypeError::TypeFailure { span, msg },
            Self::Ice(msg) => TypeError::InternalInvariant { msg },
        }
    }

    // Replace a coarse mismatch message; a `Keep` message and ICEs pass through.
    fn or_fail(self, msg: String) -> Self {
        match self {
            Self::Fail(_) => Self::Fail(msg),
            kept @ (Self::Keep(_) | Self::Ice(_)) => kept,
        }
    }

    // Replace a coarse mismatch with the caller's diagnostic. A `Keep` message is
    // preserved but adopts the fallback's span; ICEs pass through.
    fn or(self, fallback: TypeError) -> TypeError {
        match self {
            Self::Fail(_) => fallback,
            Self::Keep(msg) => match fallback.span() {
                Some(&span) => TypeError::TypeFailure { span, msg },
                None => TypeError::TypeFailure {
                    span: Span::default(),
                    msg,
                },
            },
            Self::Ice(msg) => TypeError::InternalInvariant { msg },
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

// Inference-time form of a hole report. Types and the environment remain live
// until `resolve_all` has solved the surrounding constraints, then `flush_holes`
// zonks and serializes them before the checker context is reset.
struct HoleSite {
    name: String,
    span: Span,
    expected: Type,
    effects: EffRow,
    env: Env,
}

struct Tc<'a> {
    ctx: Vec<Entry>,
    next: u32,
    seeds: u32,
    ctors: &'a BTreeMap<String, CtorInfo>,
    data: &'a BTreeMap<String, DataInfo>,
    eff_ops: &'a BTreeMap<String, EffOpInfo>,
    field_res: BTreeMap<NodeId, (String, usize, usize)>,
    unboxed_field: BTreeMap<NodeId, (usize, usize)>,
    path_res: PathRes,
    fixed: BTreeMap<NodeId, Type>,
    span_types: BTreeMap<NodeId, Type>,
    // Canonical `type ! row` strings for the opt-in `dump typespans` analysis.
    // Ordinary checking leaves these tables empty, so tooltip collection cannot
    // perturb the established inference path or checked-HIR fixture.
    track_tooltips: bool,
    pending_tooltip_rows: Vec<(NodeId, EffRow)>,
    tooltip_rows: BTreeMap<NodeId, String>,
    touched_tooltip_rows: BTreeSet<u32>,
    tooltip_row_scaffolds: BTreeSet<u32>,
    // Per-declaration principal-body-effect witnesses ([`BodyWitness`]),
    // recorded by `infer_body` and consumed by `finalize_fn`'s borrow rule.
    body_witness: BTreeMap<String, BodyWitness>,
    pending: Vec<(NodeId, Type)>,
    hole_sites: Vec<HoleSite>,
    holes: Vec<HoleReport>,
    // Each `This(e)` site, with the span of the whole expression and the element
    // type synthesized for `e`. After inference solves every existential, the
    // element is zonked and checked to have a non-null, single-word representation
    // (`is_or_null_element`), so `OrNull` formed by inference is held to the same
    // soundness rule as a written `OrNull(a)` annotation. `Null` needs no entry:
    // it is the null word for any element.
    or_null_sites: Vec<(Span, Type)>,
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
    // Numeric/comparison operands left ambiguous: each (node id, span, operand
    // type, class) is resolved in one pass at the end of the declaration
    // (`resolve_all`), so a later use can fix the type before the default or
    // class obligation applies. `class` is `None` for arithmetic, or `Eq`/`Ord`
    // for comparisons whose resolved ADTs must raise a dictionary obligation.
    num_default: Vec<(NodeId, Span, Type, Option<&'static str>)>,
    // Unary-minus operands left ambiguous at synth: resolved in the same
    // `resolve_all` pass as `num_default`, but the signed lanes differ. Negation
    // spans `Int`/`I64`/`Float` (a leftover existential defaults to `Int`), while
    // `U64` is rejected because it is unsigned. Kept separate from `num_default`,
    // whose integer operators reject a `Float` operand.
    neg_default: Vec<(NodeId, Span, Type)>,
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
    // Operation-local effect uses for the expression currently being checked.
    // Public rows remain effect-granular; this private summary lets adjacent
    // partial handlers cancel complementary, syntactically known operations.
    operation_uses: OperationUses,
    // Exact summaries for handler continuation binders. Calling `resume` runs
    // the already-recorded residual body, so its deliberately open function row
    // must not turn a known local summary into an opaque one.
    precise_calls: BTreeMap<Sym, OperationUses>,
    // Every handler expression must produce exactly one checked-HIR residual
    // fact. The marker set lets the HIR lint detect a missing or stale fact.
    handler_nodes: BTreeSet<NodeId>,
    handler_residuals: BTreeMap<NodeId, HandlerResidual>,
}

// A private operation-level refinement of an effect row. Each effect maps to
// the operations this expression may perform. A call through a public function
// row contributes every declared operation of each named effect; direct op
// syntax contributes only that op. `open_row` preserves an unenumerable row
// tail and prevents a partial handler from claiming complete discharge.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct OperationUses {
    by_effect: BTreeMap<Sym, EffectOperationUses>,
    open_row: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EffectOperationUses {
    Known(BTreeSet<Sym>),
    All,
}

impl OperationUses {
    fn insert(&mut self, effect: Sym, operation: Sym) {
        match self
            .by_effect
            .entry(effect)
            .or_insert_with(|| EffectOperationUses::Known(BTreeSet::new()))
        {
            EffectOperationUses::Known(operations) => {
                operations.insert(operation);
            }
            EffectOperationUses::All => {}
        }
    }

    fn insert_all(&mut self, effect: Sym) {
        self.by_effect.insert(effect, EffectOperationUses::All);
    }

    fn merge(&mut self, other: Self) {
        self.open_row |= other.open_row;
        for (effect, operations) in other.by_effect {
            match (
                self.by_effect
                    .entry(effect)
                    .or_insert_with(|| EffectOperationUses::Known(BTreeSet::new())),
                operations,
            ) {
                (slot, EffectOperationUses::All) => *slot = EffectOperationUses::All,
                (EffectOperationUses::Known(into), EffectOperationUses::Known(from)) => {
                    into.extend(from);
                }
                (EffectOperationUses::All, EffectOperationUses::Known(_)) => {}
            }
        }
    }

    fn subtract(
        mut self,
        handled: &BTreeMap<Sym, BTreeSet<Sym>>,
        exhaustive: &BTreeSet<Sym>,
        masked: &BTreeSet<Sym>,
    ) -> Self {
        for (effect, operations) in handled {
            if masked.contains(effect) {
                continue;
            }
            let remove_effect = self
                .by_effect
                .get_mut(effect)
                .is_some_and(|uses| match uses {
                    EffectOperationUses::Known(uses) => {
                        for operation in operations {
                            uses.remove(operation);
                        }
                        uses.is_empty()
                    }
                    EffectOperationUses::All => exhaustive.contains(effect),
                });
            if remove_effect {
                self.by_effect.remove(effect);
            }
        }
        self
    }

    fn operations(&self) -> Vec<Sym> {
        self.by_effect
            .values()
            .filter_map(|uses| match uses {
                EffectOperationUses::Known(operations) => Some(operations),
                EffectOperationUses::All => None,
            })
            .flatten()
            .copied()
            .collect()
    }

    fn opaque_effects(&self) -> Vec<Sym> {
        self.by_effect
            .iter()
            .filter_map(|(effect, uses)| {
                matches!(uses, EffectOperationUses::All).then_some(*effect)
            })
            .collect()
    }
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
// not duplicate a label. The prefix keeps whole labels, not bare names: the
// skip must equate a parametric label's arguments against the prefix's
// instantiation, or a lambda body performing `Tag(String)` under an arrow
// annotated `! {Tag(Int) | e}` would drop the label unchecked.
struct RowScope {
    tail: u32,
    prefix: Vec<Label>,
    // The contextual permission reported at a hole. This is separate from the
    // mutable accumulator above: an explicitly pure context stays `{}` even
    // while the accumulator is represented by a fresh row existential.
    expected: EffRow,
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
        Type::Fun(_, row, _) => row.label_names(),
        _ => Effects::new(),
    }
}

// The function's parameter types and inferred effect row, peeling quantifiers.
// `None` for a non-function type (a plain value binds no row). Shares the
// quantifier peel with `concrete_effects` but returns the whole signature, so
// the open-tail case can be distinguished from a closed empty one.
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

/// The recorded principal-body-effect witness of one function declaration: the
/// body's ambient effect row as inference solved it, read before
/// `default_open_rows` re-opens a pure row for context fit (which destroys the
/// closedness fact). `effects` are the concrete labels the body accumulated;
/// `closed` records that the row's tail stayed the declaration's own fresh
/// ambient (or emptied) rather than solving to a row that also flows through
/// the interface, so nothing the caller supplies can make the body perform or
/// suspend. The borrow rule consumes this witness directly instead of
/// reverse-engineering closedness from the generalized scheme.
pub(super) struct BodyWitness {
    pub(super) effects: Effects,
    pub(super) closed: bool,
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
    // The labels of the inferred row. Effect-row inference is principal: it
    // discovers every effect on its own (direct performs, applied effect-carrying
    // callees, builtin rows, `mask`), so the row is the single source of truth.
    // Real under-coverage is caught downstream by `reconcile_effects` (lowered
    // ops vs the row) and the parity oracle.
    let inferred = concrete_effects(&ty);
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
        let declared_set: BTreeSet<Sym> = declared.iter().map(|l| Sym::from(&l.name)).collect();
        for eff in &inferred {
            if !declared_set.contains(eff) {
                return Err(ErrKind::UndeclaredEffect {
                    name: d.name.clone(),
                    eff: eff.to_string(),
                }
                .at(d.body.span));
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
/// Fails for ordinary type errors; typed holes are returned in [`Checked::holes`].
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
    if checked.holes.is_empty() {
        Ok(checked)
    } else {
        Err(hole_error(&checked.holes))
    }
}

/// Seeded form of [`check_allow_holes`].
///
/// # Errors
/// Fails for ordinary type errors; typed holes themselves are returned in
/// [`Checked::holes`].
pub fn check_seeded_allow_holes(
    prog: &Program<Core>,
    seed: &TypecheckSeed,
) -> Result<Checked, TypeError> {
    check_seeded_mode(prog, seed, false)
}

fn check_seeded_mode(
    prog: &Program<Core>,
    seed: &TypecheckSeed,
    track_tooltips: bool,
) -> Result<Checked, TypeError> {
    let (mut data, mut ctors, mut eff_ops, mut env) = env::build_data(prog)?;
    data.extend(seed.data.clone());
    ctors.extend(seed.ctors.clone());
    eff_ops.extend(seed.eff_ops.clone());
    env.extend(seed.env.iter().map(|(name, ty)| (*name, ty.clone())));
    let seeds = env::seed_var_states(&eff_ops);
    let (classes, instances, inst_keys, canonical, methods, mut constrained, mut warnings) =
        classes::build_classes(prog, &mut data, &mut ctors, &mut env, seed)?;
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
                .at(c.span));
            }
            cs.push((Sym::from(&c.class), env::convert_data(&c.ty)));
        }
        constrained.insert(Sym::from(&d.name), (env::fn_stub(d, &data), cs));
    }
    let field_res;
    let unboxed_field;
    let path_res;
    let fixed;
    let span_types;
    let tooltip_rows;
    let handler_nodes;
    let handler_residuals;
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
            touched_tooltip_rows: BTreeSet::new(),
            tooltip_row_scaffolds: BTreeSet::new(),
            body_witness: BTreeMap::new(),
            pending: Vec::new(),
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
        handler_nodes = tc.handler_nodes;
        handler_residuals = tc.handler_residuals;
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
    Ok(Checked {
        env,
        data,
        ctors,
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
        ),
        decls: infos,
        eff_ops,
        classes,
        instances,
        inst_keys,
        canonical,
        methods,
        constrained: constrained_final,
        seeds,
        warnings,
        holes,
    })
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

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_env(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects), TypeError> {
    let (t, eff, _, holes) = infer_expr_full(checked, extra, e)?;
    if holes.is_empty() {
        Ok((t, eff))
    } else {
        Err(hole_error(&holes))
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
    let (ty, effects, _, holes) = infer_expr_full(checked, extra, e)?;
    Ok((ty, effects, holes))
}

// Parse the canonical signature carried by a checked module interface.
pub(crate) fn parse_checked_signature(name: &str, signature: &str) -> Result<Type, TypeError> {
    env::parse_sig(name, signature).map(|(ty, _)| ty)
}

pub(crate) const fn instance_head_key(ty: &Type) -> Option<HeadKey> {
    classes::head_name(ty)
}

/// # Errors
/// Fails when the expression does not type check.
pub fn infer_expr_dicts(
    checked: &Checked,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable), TypeError> {
    let (ty, effects, dicts, holes) = infer_expr_full(checked, &Env::new(), e)?;
    if holes.is_empty() {
        Ok((ty, effects, dicts))
    } else {
        Err(hole_error(&holes))
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
    infer_expr_full(checked, &Env::new(), e)
}

fn infer_expr_full(
    checked: &Checked,
    extra: &Env,
    e: &S<Expr<Core>>,
) -> Result<(Type, Effects, DictTable, Vec<HoleReport>), TypeError> {
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
        unboxed_field: BTreeMap::new(),
        path_res: PathRes::new(),
        fixed: BTreeMap::new(),
        span_types: BTreeMap::new(),
        track_tooltips: false,
        pending_tooltip_rows: Vec::new(),
        tooltip_rows: BTreeMap::new(),
        touched_tooltip_rows: BTreeSet::new(),
        tooltip_row_scaffolds: BTreeSet::new(),
        body_witness: BTreeMap::new(),
        pending: Vec::new(),
        hole_sites: Vec::new(),
        holes: Vec::new(),
        or_null_sites: Vec::new(),
        classes: &checked.classes,
        instances: &checked.instances,
        inst_keys: &checked.inst_keys,
        canonical: &checked.canonical,
        constrained: checked.constrained.clone(),
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
    };
    let (t, effs) = tc.scoped_effects(|tc| {
        let t = tc.synth(&env, e)?;
        tc.resolve_all()?;
        Ok(t)
    })?;
    tc.flush_holes();
    let t = tc.apply(&t);
    let g = tc.generalize(&env, &t);
    tc.holes.sort_by_key(|h| (h.start, h.end, h.name.clone()));
    Ok((g, effs, tc.dicts, tc.holes))
}
