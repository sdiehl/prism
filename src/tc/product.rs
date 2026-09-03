//! The checker's product types: the read-only [`Checked`] artifact, its
//! [`CheckedView`] contents, and the declaration/instance/dispatch records
//! those contents are made of. Assembly stays in `tc`; this module owns the
//! shapes consumers read.

use std::collections::BTreeMap;
use std::ops::Deref;

use marginalia::Span;
use serde::{Deserialize, Serialize};

use crate::error::HoleReport;
use crate::hir::NodeFacts;
use crate::sym::Sym;
use crate::syntax::ast::{Grade, NodeId};
use crate::types::ty::{Effects, Kind, Type};

use super::Env;

/// Declaration-level runtime representation of a nominal type.
///
/// Constructor shape is not enough: an ordinary one-field datatype allocates
/// a cell, while a source `newtype` with the same shape is erased. Vector
/// builtins are multiword values and belong to neither class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NominalRepr {
    /// An allocated, non-zero runtime cell.
    BoxedCell,
    /// A source `newtype` whose wrapper is removed by mandatory lowering.
    Transparent,
    /// A two-word vector value.
    Vec128,
}

/// One declared type parameter: its source name and its kind.
///
/// Almost always `Kind::Type`; a `Kind::Row` entry marks a row-kinded
/// parameter (`type Cmd(a, e : Row)`), carried in `Con` spines as `Type::Row`,
/// and a `Kind::Nat` entry a dimension parameter (`type Vec(a, n : Nat)`),
/// carried as `Type::Nat`. The parameter kinds form the constructor's arrow,
/// checked against its arguments at each annotation (see
/// `env::check_annot_rows`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeParameter {
    pub name: String,
    pub kind: Kind,
}

#[derive(Clone, Debug)]
pub struct DataInfo {
    pub params: Vec<TypeParameter>,
    pub ctors: Vec<String>,
    /// Checked declaration evidence used by representation-sensitive queries.
    pub repr: NominalRepr,
}

impl DataInfo {
    /// The declared parameter names, in declaration order.
    #[must_use]
    pub fn param_names(&self) -> Vec<String> {
        self.params.iter().map(|param| param.name.clone()).collect()
    }

    /// The declared parameter kinds, in declaration order.
    #[must_use]
    pub fn param_kinds(&self) -> Vec<Kind> {
        self.params.iter().map(|param| param.kind.clone()).collect()
    }
}

pub(crate) use crate::types::CtorInfo;

pub(crate) use crate::types::DeclInfo;

pub(crate) use crate::types::EffOpInfo;

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

/// One record-field resolution step.
///
/// Names the constructor, the field's index, and the constructor arity.
/// Serialized as the `(ctor, index, arity)` triple so the checked-HIR wire and
/// every fixture keep their bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(into = "(String, usize, usize)", from = "(String, usize, usize)")]
pub struct FieldRef {
    pub ctor: String,
    pub index: usize,
    pub arity: usize,
}

impl From<FieldRef> for (String, usize, usize) {
    fn from(field: FieldRef) -> Self {
        (field.ctor, field.index, field.arity)
    }
}

impl From<(String, usize, usize)> for FieldRef {
    fn from((ctor, index, arity): (String, usize, usize)) -> Self {
        Self { ctor, index, arity }
    }
}

// Per update path, the rebuild chain: one [`FieldRef`] step per path segment,
// resolved at the update expression's node.
pub type PathRes = BTreeMap<NodeId, Vec<Vec<FieldRef>>>;

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

/// The typing surface later compilations build on: the final environment and
/// the seed count interface serialization stamps beside it.
#[derive(Clone, Debug)]
pub struct InterfaceFacts {
    pub env: Env,
    pub seeds: u32,
}

/// Per-declaration facts: nominal types, their constructors, top-level
/// declaration schemes, and effect operations.
#[derive(Clone, Debug)]
pub struct DeclFacts {
    pub data: BTreeMap<String, DataInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub decls: Vec<DeclInfo>,
    pub eff_ops: BTreeMap<String, EffOpInfo>,
}

/// A class method's identity: the owning class and the method's slot among the
/// class's declared methods (its field index in the dict cell follows the
/// class's superclass fields).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MethodRef {
    pub class: Sym,
    pub index: usize,
}

/// One class-constraint obligation `Class(head)` a scheme carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassConstraint {
    pub class: Sym,
    pub head: Type,
}

/// A generalized scheme together with the `given` constraints the checker
/// discharges at each of its call sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstrainedScheme {
    pub scheme: Type,
    pub constraints: Vec<ClassConstraint>,
}

/// Every constrained scheme, keyed by the declaration it types.
pub type ConstrainedSchemes = BTreeMap<Sym, ConstrainedScheme>;

/// Everything class-and-instance: declarations, dispatch keys, canonical
/// designations, method identities, and the constrained schemes whose evidence
/// elaboration threads.
#[derive(Clone, Debug)]
pub struct DispatchFacts {
    pub classes: BTreeMap<Sym, ClassInfo>,
    pub instances: BTreeMap<Sym, InstInfo>,
    pub inst_keys: InstKeys,
    pub canonical: Canon,
    pub methods: BTreeMap<Sym, MethodRef>,
    /// The inferred effect row of each instance method, keyed by the name
    /// elaboration will lift it to (`i@showInt@show`).
    ///
    /// An instance method is not in `decls`: it is checked from inside its
    /// instance rather than as a top-level function, so its row was computed,
    /// held to the class signature's declared labels, and dropped. Instances have
    /// no `DeclInfo`, and Core carries no rows, so consumers read this table.
    pub method_effects: BTreeMap<Sym, Effects>,
    pub constrained: ConstrainedSchemes,
}

/// Non-fatal checker output: warnings and typed-hole reports.
#[derive(Clone, Debug)]
pub struct Reports {
    pub warnings: Vec<Warning>,
    /// Source-ordered typed-hole reports. Ordinary checking rejects a non-empty
    /// list; interpreter-only deferred checking returns it to the caller.
    pub holes: Vec<HoleReport>,
}

/// Read-only contents of a successfully checked program, grouped by consumer:
/// each downstream pass reads one or two groups, never the whole bag.
///
/// [`Checked`] owns this view and exposes it through shared dereferencing. The
/// separate type preserves field-based reads for existing consumers without
/// letting them mutate or assemble a checked artifact.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct CheckedView {
    pub interface: InterfaceFacts,
    pub defs: DeclFacts,
    // Every per-node semantic fact checking established (resolution, evidence,
    // lanes, zonked node types), dense by NodeId. The former six NodeId side
    // tables, consolidated; elaboration reads it only through a `CheckedHir`.
    pub facts: NodeFacts,
    pub dispatch: DispatchFacts,
    pub reports: Reports,
}

/// A successfully checked program whose aggregate invariants are sealed.
///
/// Consumers may read the fields in [`CheckedView`] through shared
/// dereferencing. Construction and mutation remain inside the checker and the
/// narrow compiler transitions that own presentation-only facts.
///
/// ```compile_fail
/// fn corrupt(checked: &mut prism::types::Checked) {
///     checked.decls.clear();
/// }
/// ```
///
/// ```compile_fail
/// use prism::types::{Checked, CheckedView};
///
/// fn forge(view: CheckedView) -> Checked {
///     Checked { view }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Checked {
    view: CheckedView,
}

impl Deref for Checked {
    type Target = CheckedView;

    fn deref(&self) -> &Self::Target {
        &self.view
    }
}

impl Checked {
    // Construction is sealed to the checker: `tc` and its children assemble a
    // view, everyone else reads one.
    pub(super) const fn new(view: CheckedView) -> Self {
        Self { view }
    }

    /// Borrow the complete read-only checker result.
    #[must_use]
    pub const fn view(&self) -> &CheckedView {
        &self.view
    }

    pub(crate) fn extend_warnings(&mut self, warnings: impl IntoIterator<Item = Warning>) {
        self.view.reports.warnings.extend(warnings);
    }

    pub(crate) fn push_warning(&mut self, warning: Warning) {
        self.view.reports.warnings.push(warning);
    }

    pub(crate) fn refresh_surface_warnings(
        &mut self,
        surface_warnings: impl IntoIterator<Item = Warning>,
        mut refresh_span: impl FnMut(WarningOrigin) -> Option<Span>,
    ) {
        self.view
            .reports
            .warnings
            .retain(|warning| !matches!(warning.origin, WarningOrigin::Surface));
        for warning in &mut self.view.reports.warnings {
            if let Some(span) = refresh_span(warning.origin) {
                warning.span = span;
            }
        }
        self.view.reports.warnings.extend(surface_warnings);
    }

    pub(crate) fn adopt_tooltips_from(&mut self, tooltips: Self) {
        self.view.facts.adopt_tooltips(tooltips.view.facts);
    }

    #[cfg(test)]
    pub(crate) fn replace_node_facts_for_test(&mut self, facts: NodeFacts) {
        self.view.facts = facts;
    }

    /// Each effect op keyed by its symbol to its declared resumption grade, the
    /// side table effect lowering consumes to decide which handlers may disable
    /// var-erasure. Ops absent here (a synthetic private effect) default to the
    /// most general grade at the consumer.
    #[must_use]
    pub fn op_grades(&self) -> BTreeMap<Sym, Grade> {
        self.defs
            .eff_ops
            .iter()
            .map(|(name, info)| (Sym::from(name), info.grade))
            .collect()
    }

    /// One declaration's full rendered signature: the generalized scheme, then
    /// the `given` constraints the checker discharges at each call site.
    /// `finish_decl` renames the constraint types through the same substitution
    /// that names the scheme's quantifiers, so `given Foldable(a)` names the
    /// same `a` the `forall` binds. `Type` itself has no constraint component
    /// (constraints erase to dictionary evidence), so the plain `ty.show()`
    /// silently drops them; every reader-facing surface (`dump types`, the doc
    /// generator) must render through here instead. The content hash
    /// (`hash_meta`) deliberately does not: its rendering is pinned.
    #[must_use]
    pub fn show_sig(&self, d: &DeclInfo) -> String {
        let base = d.ty.show();
        match self.dispatch.constrained.get(&Sym::from(&d.name)) {
            Some(constrained) if !constrained.constraints.is_empty() => {
                let given: Vec<String> = constrained
                    .constraints
                    .iter()
                    .map(|c| format!("{}({})", c.class, c.head.show()))
                    .collect();
                format!("{base} given {}", given.join(", "))
            }
            _ => base,
        }
    }
}
