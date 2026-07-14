use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub use marginalia::Span;
pub use num_bigint::BigInt;

use crate::coeffect::CoeffectFact;
pub use crate::coeffect::CoeffectRow;
use crate::kw;
pub use crate::types::ty::Kind;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Suffix {
    None,
    I64,
    U64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntLit {
    pub value: BigInt,
    pub suffix: Suffix,
}

impl fmt::Display for IntLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self.suffix {
            Suffix::None => "",
            Suffix::I64 => "i64",
            Suffix::U64 => "u64",
        };
        write!(f, "{}{}", self.value, s)
    }
}

// A stable, unique identity for an expression node, the key under which the
// typechecker records a node's resolution (dictionaries, field/path rebuilds,
// numeric width) for the elaborator to read back. Assigned by `assign_ids`
// after desugar, so identity is decoupled from `Span`: a synthesized node may
// carry any real source span (even a duplicated one) for diagnostics without
// ever aliasing another node's resolution. `DUMMY` is the unassigned id, worn
// by patterns/types (which are never dispatch sites) and by elaborator-local
// nodes that do no table lookup.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct NodeId(pub u32);

impl NodeId {
    pub const DUMMY: Self = Self(0);
}

#[derive(Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
    // Node identity for the typechecker's per-node side tables; see `NodeId`.
    // Inert until `assign_ids` stamps it; never printed (identity, not content).
    pub id: NodeId,
    // Set by parse-time sugar so the formatter can restore the surface form
    // (dot calls, `with`, pattern lets, `?`, handler blocks) rather than print
    // the desugared tree. Inert for every pass except the formatter.
    pub synth: bool,
}

pub type S<T> = Spanned<T>;

impl<T> Spanned<T> {
    #[must_use]
    pub const fn new(node: T, span: Span) -> Self {
        Self {
            node,
            span,
            id: NodeId::DUMMY,
            synth: false,
        }
    }
    #[must_use]
    pub const fn sugar(node: T, span: Span) -> Self {
        Self {
            node,
            span,
            id: NodeId::DUMMY,
            synth: true,
        }
    }
}

// Show `synth` only when set, so a sugar node stands out and non-sugar nodes
// render identically to the derived form. `id` is identity, not content, so it
// is never shown: an AST dump stays byte-identical across id assignment.
#[expect(
    clippy::missing_fields_in_debug,
    reason = "`id` is node identity, deliberately omitted so AST dumps are stable"
)]
impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Spanned");
        d.field("node", &self.node).field("span", &self.span);
        if self.synth {
            d.field("synth", &self.synth);
        }
        d.finish()
    }
}

#[derive(Clone)]
pub struct Program<P: Phase = Surface> {
    pub types: Vec<DataDecl>,
    pub effects: Vec<EffectDecl>,
    pub errors: Vec<ErrorDecl>,
    pub aliases: Vec<AliasDecl>,
    pub synonyms: Vec<SynonymDecl>,
    pub classes: Vec<ClassDecl>,
    pub instances: Vec<InstanceDecl<P>>,
    // `stable` blocks, desugared into `types`/`fns`/`instances`/`synonyms` before
    // typecheck. Surface-only, so it is empty in a `Program<Core>`.
    pub stable: Vec<StableDecl>,
    // Canonical-instance designations: which instance implicit resolution picks
    // when several share a `(class, type-head)`. Phase-independent (no exprs).
    pub canonicals: Vec<CanonicalDecl>,
    pub patterns: Vec<PatternDecl<P>>,
    pub fns: Vec<Decl<P>>,
    // Module imports, resolved away by the name-resolution pass.
    pub imports: Vec<ImportDecl>,
    // Top-level names marked `pub`. Visibility lives here, off the decls, so an
    // AST dump of a `pub`-free program is byte-identical to one without modules.
    pub exports: BTreeSet<String>,
    // Type names marked `opaque`: exported by name but with their constructors
    // hidden outside the defining module. A subset of `exports`.
    pub opaques: BTreeSet<String>,
    // Definitions carrying a `deprecated "suggestion"` annotation, keyed by the
    // surface name, mapping to the author's replacement suggestion. Off the decls
    // (like `exports`), so an AST dump of an annotation-free program is unchanged.
    // A use of one of these names warns at compile time (see `resolve::lints`).
    pub deprecated: BTreeMap<String, String>,
}

// The visibility of a top-level item: private (default), `pub` (exported
// transparently), or `opaque` (exported by name, constructors hidden).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vis {
    Priv,
    Pub,
    Opaque,
}

// The FP^2 in-place discipline a `fn` is annotated with. `Fbip` proves the body
// allocates nothing fresh (every constructor reuses a dropped cell); `Fip` adds
// linearity (no dup, no borrowed params). Checked over the reuse-lowered core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fip {
    No,
    Fbip,
    Fip,
}

impl Fip {
    /// The canonical certificate keyword (`fip`/`fbip`), or `None` when the
    /// definition carries no discipline. The one home for the spelling: the
    /// content hash (`hash_meta`), the `dump usage` discipline column, and the
    /// module interface's usage summary all render through this, so the three
    /// can never drift. Callers choose how to render `None` (an empty cell, a
    /// `-`, or an omitted field).
    #[must_use]
    pub const fn keyword(self) -> Option<&'static str> {
        match self {
            Self::No => None,
            Self::Fbip => Some("fbip"),
            Self::Fip => Some("fip"),
        }
    }
}

// `patterns`, `imports`, and `exports` are omitted from the debug dump when
// empty, matching the derived output for import-free, pattern-free programs.
impl<P: Phase + fmt::Debug> fmt::Debug for Program<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Program");
        if !self.imports.is_empty() {
            d.field("imports", &self.imports);
        }
        d.field("types", &self.types)
            .field("effects", &self.effects)
            .field("errors", &self.errors)
            .field("aliases", &self.aliases);
        if !self.synonyms.is_empty() {
            d.field("synonyms", &self.synonyms);
        }
        d.field("classes", &self.classes)
            .field("instances", &self.instances);
        if !self.stable.is_empty() {
            d.field("stable", &self.stable);
        }
        if !self.canonicals.is_empty() {
            d.field("canonicals", &self.canonicals);
        }
        if !self.patterns.is_empty() {
            d.field("patterns", &self.patterns);
        }
        d.field("fns", &self.fns);
        if !self.exports.is_empty() {
            d.field("exports", &self.exports);
        }
        if !self.opaques.is_empty() {
            d.field("opaques", &self.opaques);
        }
        if !self.deprecated.is_empty() {
            d.field("deprecated", &self.deprecated);
        }
        d.finish()
    }
}

// `import Data.Map`, `import List (map, filter)`, `import Json as J`,
// `import Data.List (..)`. The path is the dotted module path. `names` present
// means a selective unqualified import; absent means a qualified import bound
// under `alias` or the last path component. `glob` is the `(..)` form: every
// exported name enters unqualified scope, the mechanism the layered prelude uses
// to re-open its stdlib modules.
#[derive(Clone, Debug)]
pub struct ImportDecl {
    pub path: Vec<String>,
    pub alias: Option<String>,
    pub names: Option<Vec<String>>,
    pub glob: bool,
    // A `pub import` re-exports the imported names from this module, so a
    // downstream importer can reach them through this module too.
    pub reexport: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Item {
    Import(ImportDecl),
    Data(DataDecl),
    Effect(EffectDecl),
    Error(ErrorDecl),
    Alias(AliasDecl),
    Synonym(SynonymDecl),
    Class(ClassDecl),
    Instance(InstanceDecl),
    Canonical(CanonicalDecl),
    Pattern(PatternDecl),
    Fn(Decl),
    Stable(StableDecl),
    // A `deprecated "suggestion"` annotation line. It is a standalone item (a
    // layout statement of its own) that the parse-time demultiplexer attaches to
    // the declaration that follows it, recording the suggestion in
    // `Program::deprecated`; it never survives into a built `Program`.
    Deprecated(Span, String),
}

// The parser only builds `Surface` items, so `Item` stays non-generic.

// `pattern Polar(r, t) for Complex = view \(c) -> ... make \(r, t) -> ...`:
// a Scala-style extractor. `view` deconstructs in match position, `make`
// (optional) constructs in expression position.
#[derive(Clone, Debug)]
pub struct PatternDecl<P: Phase = Surface> {
    pub name: String,
    pub params: Vec<String>,
    pub for_ty: String,
    pub view: S<Expr<P>>,
    pub make: Option<S<Expr<P>>>,
    pub span: Span,
}

// `error NotFound(String)`: sugar for a one-op effect whose op never resumes.
#[derive(Clone, Debug)]
pub struct ErrorDecl {
    pub name: String,
    pub params: Vec<Ty>,
    pub span: Span,
}

// A row label: an effect name with optional type arguments, `Emit(Int)`.
#[derive(Clone, Debug, PartialEq)]
pub struct EffLabel {
    pub name: String,
    pub args: Vec<Ty>,
}

impl EffLabel {
    #[must_use]
    pub fn bare(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            args: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AliasDecl {
    pub name: String,
    pub labels: Vec<EffLabel>,
    pub span: Span,
}

// `alias Name(a, b) = Ty`: a type synonym, distinguished from an effect alias
// by its RHS (a type, not a `{ .. }` row). Expanded with parameter substitution
// before typecheck, so the checker never sees synonyms.
#[derive(Clone, Debug)]
pub struct SynonymDecl {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Ty,
    pub span: Span,
}

// Parser helper: the right side of an `alias`, before deciding whether it is an
// effect alias (a `{ .. }` row) or a type synonym (a type).
#[derive(Debug)]
pub enum AliasRhs {
    Eff(Vec<EffLabel>),
    Ty(Ty),
}

#[derive(Clone, Debug)]
pub struct ClassDecl {
    pub name: String,
    pub param: String,
    // Superclass class names, each a constraint over `param` (`class Ord(a)
    // given Eq(a)` records `["Eq"]`). Every instance of this class then carries
    // a resolved superclass dictionary, projectable from a `given` constraint.
    pub supers: Vec<String>,
    pub methods: Vec<(String, Ty)>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct InstanceDecl<P: Phase = Surface> {
    pub name: String,
    pub class: String,
    pub head: Ty,
    pub context: Vec<Constraint>,
    pub methods: Vec<Decl<P>>,
    // The module that defines this instance, for the orphan/overlap rules and
    // provenance diagnostics. Empty for a root-program instance. A user instance
    // is tagged by the renamer; a derived one by its data type's canonical name.
    pub module: String,
    pub span: Span,
}

// `canonical Class(Head) = name`: designates the canonical instance for a
// `(class, type-head)` so implicit resolution is deterministic when several
// instances share the head. `name` references a global instance (stays bare,
// like every instance reference); `class`/`head` are canonicalized by the
// renamer to match the keys the instance store is built under.
#[derive(Clone, Debug)]
pub struct CanonicalDecl {
    pub class: String,
    pub head: Ty,
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Constraint {
    pub class: String,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct DataDecl {
    pub name: String,
    pub params: Vec<String>,
    // Kind of each type parameter, positional. Either empty (every parameter has
    // kind `Type`, the common case) or the same length as `params`. A parameter
    // of kind `Row` ranges over effect rows, so a field may reference it in a
    // `! {..}` position (`type Cmd(a, e : Row)`).
    pub param_kinds: Vec<Kind>,
    pub ctors: Vec<Ctor>,
    pub deriving: Vec<(String, Span)>,
    pub newtype: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Ctor {
    pub name: String,
    pub args: Vec<Ty>,
    pub fields: Option<Vec<(String, Ty)>>,
}

/// How a constructor addresses its fields: positional or record.
///
/// `Positional` carries the arg types (indexed); `Record` the named fields.
/// Recovered once from `fields` being absent or present, so no site re-tests
/// `fields.is_some()` to rediscover the case.
#[derive(Debug)]
pub enum CtorShape<'a> {
    Positional(&'a [Ty]),
    Record(&'a [(String, Ty)]),
}

impl Ctor {
    #[must_use]
    pub fn shape(&self) -> CtorShape<'_> {
        self.fields.as_ref().map_or_else(
            || CtorShape::Positional(&self.args),
            |fields| CtorShape::Record(fields),
        )
    }
}

// A `stable` block: a datatype's frozen version history plus the converters
// between adjacent rungs. Desugared in `syntax/desugar/stable.rs` to the frozen rung record
// types, the current rung under the bare type name, the generated and
// hand-written `upgrade`/`downgrade` ladder functions, and the per-rung shape
// golden. Surface-only, like every `Item`, so it is not `Phase`-generic: desugar
// consumes it entirely into ordinary types, functions, and instances.
#[derive(Clone, Debug)]
pub struct StableDecl {
    pub name: String,
    pub rungs: Vec<Rung>,
    pub converters: Vec<Converter>,
    pub span: Span,
}

// One version of a stable type. `base` is the predecessor rung it extends
// (`..V1`), absent on the first. `fields` are the rung's own field declarations:
// a genuinely new field carries a `default` the generated `upgrade` uses, while a
// field reusing a base name with a changed type is a type mutation (no default,
// requiring a hand-written converter). `frozen` is the committed shape-digest
// golden, seeded once a rung ships; a recomputed digest that no longer matches it
// is the frozen-format compile error.
#[derive(Clone, Debug)]
pub struct Rung {
    pub name: String,
    pub base: Option<String>,
    pub fields: Vec<RungField>,
    pub frozen: Option<String>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct RungField {
    pub name: String,
    pub ty: Ty,
    pub default: Option<SExpr>,
}

// A hand-written converter between two adjacent rungs, for a type mutation the
// compiler cannot generate. `base`/`overrides` are the `{ ..base, f = e, .. }`
// record body: the target rung is rebuilt field by field, taking each field from
// `overrides` when named there and from `base.<field>` otherwise. `drop_loss`
// names the fields a downgrade reports as dropped `Loss`.
#[derive(Clone, Debug)]
pub struct Converter {
    pub dir: ConvDir,
    pub from: String,
    pub to: String,
    pub base: SExpr,
    pub overrides: Vec<(String, SExpr)>,
    pub drop_loss: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConvDir {
    Upgrade,
    Downgrade,
}

#[derive(Clone, Debug)]
pub struct EffectDecl {
    pub name: String,
    pub params: Vec<String>,
    pub ops: Vec<EffOp>,
    pub span: Span,
}

// The resumption multiplicity an effect operation permits its handler clauses,
// a three-point lattice ordered `Never < Once < Many` (the derived variant
// order, so `<=` is the typing rule "clause grade at most op grade"). Declared
// per op; the surface prefixes are `never`, `once`, and `many`, the same words
// the value multiplicity lattice uses. `Many` is the default (unmarked op), so a
// bare declaration and every existing effect keeps the most general meaning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Grade {
    // `never`: the clause never resumes; the continuation is dropped.
    Never,
    // `once`: the clause resumes exactly once, in tail position (no capture).
    // On an operation this is stronger than the affine value-side `once`: it is
    // exactly-once-in-tail, which is what the direct-call lowering exploits.
    Once,
    // `many`: the clause may capture the continuation and resume any number of
    // times. The default and the most general grade.
    #[default]
    Many,
}

impl Grade {
    // The grade-only word (`never`); `once` and `many` share their spelling with
    // the value multiplicity lattice, so renaming a coeffect word renames the
    // grade word too and the shared-lattice claim stays true in code.
    pub const NEVER: &'static str = "never";

    // The surface word for this grade, used by the formatter and the doc
    // generator so a printed op declaration round-trips through the parser.
    // `Many` is the default and prints bare; callers that emit a prefix suppress
    // it for `Many` (see `is_default`).
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::Never => Self::NEVER,
            Self::Once => CoeffectFact::Once.name(),
            Self::Many => CoeffectFact::Many.name(),
        }
    }

    // Whether this is the unmarked default (`Many`), which is written with no
    // prefix at all.
    #[must_use]
    pub fn is_default(self) -> bool {
        self == Self::Many
    }

    // A leading op/clause word parsed as a grade; `None` if the word names no
    // grade (the grammar turns that into a pointed error).
    #[must_use]
    pub fn parse(word: &str) -> Option<Self> {
        match word {
            _ if word == Self::NEVER => Some(Self::Never),
            _ if word == CoeffectFact::Once.name() => Some(Self::Once),
            _ if word == CoeffectFact::Many.name() => Some(Self::Many),
            _ => None,
        }
    }

    // The frozen digest tag for effect shape encoding, decoupled from `word` so a
    // later respelling of the surface keyword can never move an effect shape
    // digest again. Only a non-default grade is ever emitted (see `shape.rs`), so
    // every ungraded op keeps its digest; the internal control effects
    // (`Break`/`Continue`/`Fail`/`Return`) are declared `Never`, so their tag is
    // committed in the stdlib root. These tags were reseated once, at this
    // rename, from the retired spelling to the grade words below, moving the root
    // deliberately; from here they are frozen.
    #[must_use]
    pub const fn digest_tag(self) -> &'static str {
        match self {
            Self::Never => GRADE_TAG_NEVER,
            Self::Once => GRADE_TAG_ONCE,
            Self::Many => GRADE_TAG_MANY,
        }
    }
}

// Frozen effect-shape digest tags for the grades, one canonical home. These are
// content hashes' input, so their spelling is opaque and their stability is what
// matters; do not respell them. `MANY` is never emitted (the default is
// suppressed), but is frozen for completeness.
pub const GRADE_TAG_NEVER: &str = "never";
pub const GRADE_TAG_ONCE: &str = "once";
pub const GRADE_TAG_MANY: &str = "many";

#[derive(Clone, Debug)]
pub struct EffOp {
    pub name: String,
    pub params: Vec<Ty>,
    pub ret: Ty,
    // Declared resumption multiplicity (see `Grade`); `Many` unless the op's
    // surface prefix narrows it.
    pub grade: Grade,
}

// Several independent surface flags (`konst`, `replayable`, `no_alloc`); a
// flat set of one-shot booleans, not a state machine.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone)]
pub struct Decl<P: Phase = Surface> {
    pub name: String,
    pub params: Vec<Param<P>>,
    pub ret: Option<Ty>,
    pub eff: Option<Vec<EffLabel>>,
    pub constraints: Vec<Constraint>,
    pub body: S<Expr<P>>,
    // Trailing `where` bindings (non-recursive, let*-style): desugared into
    // nested `let`s around `body`, kept here so the formatter can restore them.
    pub wheres: Vec<(String, S<Expr<P>>)>,
    // A top-level `let NAME = EXPR` constant: zero params, its type is the
    // body's value type, and every reference inlines the body instead of
    // pushing a call frame. Set only by the const decl form.
    pub konst: bool,
    // The FP^2 in-place annotation (`fip`/`fbip` keyword before `fn`), checked
    // over the reuse-lowered core. `No` for a plain `fn`.
    pub fip: Fip,
    // The `replayable` annotation (orthogonal to `fip`/`fbip`): the inferred row
    // must stay within the recordable capabilities plus the deterministic builtin
    // effects, so a record/replay handler can reproduce every observation.
    pub replayable: bool,
    // The `@ noalloc` allocation certificate, written at the root of the return
    // annotation and lifted off the type at parse: the function and its whole
    // call tree must allocate no fresh heap cell. Checked over the reuse-lowered
    // core with `fbip` semantics (no linearity or bounded-stack requirement).
    pub no_alloc: bool,
    pub span: Span,
}

// `konst` is shown only when set, so a plain `fn` dumps identically to the
// pre-constant form and a constant stands out.
impl<P: Phase + fmt::Debug> fmt::Debug for Decl<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Decl");
        d.field("name", &self.name)
            .field("params", &self.params)
            .field("ret", &self.ret)
            .field("eff", &self.eff)
            .field("constraints", &self.constraints)
            .field("body", &self.body)
            .field("wheres", &self.wheres);
        if self.konst {
            d.field("konst", &self.konst);
        }
        if self.fip != Fip::No {
            d.field("fip", &self.fip);
        }
        if self.replayable {
            d.field("replayable", &self.replayable);
        }
        if self.no_alloc {
            d.field("no_alloc", &self.no_alloc);
        }
        d.field("span", &self.span).finish()
    }
}

#[derive(Clone, Debug)]
pub struct Param<P: Phase = Surface> {
    pub name: String,
    pub ty: Option<Ty>,
    pub borrow: bool,
    // A capture-free default, honored only on top-level `fn` parameters: a call
    // omitting this argument (or any call using named arguments) fills it in.
    pub default: Option<S<Expr<P>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    Int,
    I64,
    U64,
    Bool,
    Unit,
    Float,
    Char,
    Str,
    Var(String),
    // Higher-kinded application of a type variable: `f(a)`, `t(a, b)`. The head is
    // always a (lowercase) variable; a constructor head parses as `Con` instead.
    App(String, Vec<Self>),
    // A `var x := e` state cell, lowered straight to the pinned existential
    // `Exist(n)` so every read/write/handler of one var unifies through it. Only
    // desugar produces it. It never appears in source or surviving annotations.
    #[doc(hidden)]
    State(u32),
    Forall(Vec<String>, Box<Self>),
    Fun(Vec<Self>, Row, Box<Self>),
    Con(String, Vec<Self>),
    Tuple(Vec<Self>),
    // Unboxed product types, written with the `#` sigil: `#(a, b)` is an unboxed
    // tuple and `#{ x : a, y : b }` an unboxed record. Their runtime representation
    // is `Repr::Product`, so they move without a heap cell. Distinct from the boxed
    // `Tuple` above (whose representation is `Repr::Value`); the field names of an
    // `UnboxedRecord` are part of its identity and are kept in written order.
    UnboxedTuple(Vec<Self>),
    UnboxedRecord(Vec<(String, Self)>),
    // A `{ E, .. | r }` effect-row literal written in type-argument position, the
    // argument for a `Row`-kinded parameter (`Cmd(Int, {IO})`). Only valid at a
    // `Row`-kinded position; the kind check rejects it anywhere a type is wanted.
    RowLit(Row),
    // A type-level natural literal in a dimension position (`Vec(Int, 3)`), the
    // argument for a `Nat`-kinded parameter. Only valid at a `Nat`-kinded
    // position; the kind check rejects it anywhere a type is wanted.
    Nat(u64),
    // A usage row (`T @ noalloc`, `T @ {once, portable}`) attached to an atomic
    // or parenthesized type; the compiler-internal name is the coeffect row. A
    // row written at the root of a `fn` return annotation spelling exactly
    // `@ noalloc` is lifted onto `Decl::no_alloc` at parse and never reaches
    // here; every row that survives in a `Ty` is a reserved fact the checker
    // rejects with a pointed diagnostic.
    Coeffect(Box<Self>, CoeffectRow),
}

impl Ty {
    /// Visit each directly-nested `Ty` (including those inside effect-row label
    /// arguments). This is the single exhaustive statement of `Ty`'s structural
    /// children: a walker that recurses through it cannot silently drop a variant,
    /// and adding a variant forces an update here rather than a quiet miss at every
    /// hand-written `match`.
    pub fn each_child(&self, f: &mut impl FnMut(&Self)) {
        match self {
            Self::App(_, args)
            | Self::Con(_, args)
            | Self::Tuple(args)
            | Self::UnboxedTuple(args) => {
                for a in args {
                    f(a);
                }
            }
            Self::UnboxedRecord(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Self::Forall(_, b) | Self::Coeffect(b, _) => f(b),
            Self::Fun(ps, row, ret) => {
                for p in ps {
                    f(p);
                }
                for a in row_label_args(row) {
                    f(a);
                }
                f(ret);
            }
            Self::RowLit(row) => {
                for a in row_label_args(row) {
                    f(a);
                }
            }
            Self::Int
            | Self::I64
            | Self::U64
            | Self::Bool
            | Self::Unit
            | Self::Float
            | Self::Char
            | Self::Str
            | Self::Var(_)
            | Self::State(_)
            | Self::Nat(_) => {}
        }
    }

    /// Mutable counterpart of [`Ty::each_child`].
    pub fn each_child_mut(&mut self, f: &mut impl FnMut(&mut Self)) {
        match self {
            Self::App(_, args)
            | Self::Con(_, args)
            | Self::Tuple(args)
            | Self::UnboxedTuple(args) => {
                for a in args {
                    f(a);
                }
            }
            Self::UnboxedRecord(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Self::Forall(_, b) | Self::Coeffect(b, _) => f(b),
            Self::Fun(ps, row, ret) => {
                for p in ps {
                    f(p);
                }
                for a in row_label_args_mut(row) {
                    f(a);
                }
                f(ret);
            }
            Self::RowLit(row) => {
                for a in row_label_args_mut(row) {
                    f(a);
                }
            }
            Self::Int
            | Self::I64
            | Self::U64
            | Self::Bool
            | Self::Unit
            | Self::Float
            | Self::Char
            | Self::Str
            | Self::Var(_)
            | Self::State(_)
            | Self::Nat(_) => {}
        }
    }

    /// Fallible mutable child walk: stops and returns the first error `f` yields.
    ///
    /// # Errors
    /// Propagates the first `Err` returned by `f` for any child, leaving the
    /// remaining children unvisited.
    pub fn try_each_child_mut<E>(
        &mut self,
        f: &mut impl FnMut(&mut Self) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut out = Ok(());
        self.each_child_mut(&mut |c| {
            if out.is_ok() {
                out = f(c);
            }
        });
        out
    }
}

fn row_label_args(row: &Row) -> impl Iterator<Item = &Ty> {
    let labels = if let Row::Cons(ls, _) = row {
        ls.as_slice()
    } else {
        &[]
    };
    labels.iter().flat_map(|l| l.args.iter())
}

fn row_label_args_mut(row: &mut Row) -> impl Iterator<Item = &mut Ty> {
    let labels = if let Row::Cons(ls, _) = row {
        ls.as_mut_slice()
    } else {
        &mut []
    };
    labels.iter_mut().flat_map(|l| l.args.iter_mut())
}

#[derive(Clone, Debug, PartialEq)]
pub enum Row {
    Empty,
    Cons(Vec<EffLabel>, Option<String>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    // Exponentiation, one operator over Int and Float. Unlike the other
    // arithmetic ops it has no single primitive: elaboration lowers it to an
    // integer or floating power call by the operand types, promoting a mixed pair
    // to Float. Not a `CoreOp`.
    Pow,
}

impl BinOp {
    /// The canonical source spelling of this operator.
    #[must_use]
    pub const fn spelling(self) -> &'static str {
        match self {
            Self::Add => kw::PLUS,
            Self::Sub => kw::MINUS,
            Self::Mul => kw::STAR,
            Self::Div => kw::SLASH,
            Self::Rem => kw::PERCENT,
            Self::Eq => kw::EQ_EQ,
            Self::Ne => kw::NE,
            Self::Lt => kw::LT,
            Self::Le => kw::LE,
            Self::Gt => kw::GT,
            Self::Ge => kw::GE,
            Self::And => kw::AMP_AMP,
            Self::Or => kw::PIPE_PIPE,
            Self::Pow => kw::CARET,
        }
    }
}

// The compilation phase an expression tree belongs to. `Surface` is the parsed
// sugar-bearing AST; `Core` is desugar's output, where the sugar payloads become
// the uninhabited `Never` so every sugar variant is statically impossible and
// downstream passes need no arm for it. `Phase` threads through `Expr`/
// `HandlerArm` (and the structs holding them) so one set of definitions serves
// both phases.
pub trait Phase: Sized {
    // Payload of `Expr::Sugar` (the surface-only expression forms).
    type Sugar: Clone + fmt::Debug;
    // Payload of `HandlerArm::Sugar` (the three surface-only handler clauses).
    type Arm: Clone + fmt::Debug;
    // Payload of `Expr::Marker` (the parse-time markers).
    type Marker: Clone + fmt::Debug;

    #[doc(hidden)]
    fn each_sugar_child<F: FnMut(&S<Expr<Self>>)>(s: &Self::Sugar, f: &mut F);

    #[doc(hidden)]
    fn each_arm_child<F: FnMut(&S<Expr<Self>>)>(a: &Self::Arm, f: &mut F);
}

#[derive(Clone, Debug)]
pub enum Surface {}
#[derive(Clone, Debug)]
pub enum Core {}

// Uninhabited: a `Never` value cannot exist, so an `Expr<Core>::Sugar(Never)`
// cannot be constructed and an empty `match` over it is exhaustive.
#[derive(Clone, Debug)]
pub enum Never {}

impl Phase for Surface {
    type Sugar = Sugar<Self>;
    type Arm = SugarArm<Self>;
    type Marker = Marker;

    fn each_sugar_child<F: FnMut(&S<Expr<Self>>)>(s: &Self::Sugar, f: &mut F) {
        match s {
            Sugar::NamedHandle(_, body, arms) => {
                f(body);
                for a in arms {
                    a.each_child(f);
                }
            }
            Sugar::VarDecl(_, v, b) => {
                f(v);
                f(b);
            }
            Sugar::Assign(_, v) | Sugar::OptChain(v, _) | Sugar::Probe(_, v) | Sugar::Return(v) => {
                f(v);
            }
            Sugar::IndexAssign(recv, key, v) => {
                f(recv);
                f(key);
                f(v);
            }
            Sugar::Throw(_, args) => {
                for a in args {
                    f(a);
                }
            }
            Sugar::TryCatch(body, arms) => {
                f(body);
                for a in arms {
                    f(&a.body);
                }
            }
            Sugar::For(_, seq, quals, body) => {
                f(seq);
                for q in quals {
                    q.each_child(f);
                }
                f(body);
            }
            Sugar::While(cond, body) => {
                if let Some(cond) = cond {
                    f(cond);
                }
                f(body);
            }
            Sugar::Comp(head, _, seq, quals) => {
                f(head);
                f(seq);
                for q in quals {
                    q.each_child(f);
                }
            }
            Sugar::Default(a, b) | Sugar::Transact(a, b) | Sugar::Compose(_, a, b) => {
                f(a);
                f(b);
            }
            Sugar::Range(prefix, hi) => {
                for a in prefix {
                    f(a);
                }
                f(hi);
            }
            Sugar::ReadPath(base, steps) => {
                f(base);
                for s in steps {
                    if let Some(e) = s.sub_expr() {
                        f(e);
                    }
                }
            }
            Sugar::Break | Sugar::Continue => {}
        }
    }

    fn each_arm_child<F: FnMut(&S<Expr<Self>>)>(a: &Self::Arm, f: &mut F) {
        match a {
            SugarArm::Once(_, _, body) | SugarArm::Val(_, body) | SugarArm::Never(_, _, body) => {
                f(body);
            }
        }
    }
}
impl Phase for Core {
    type Sugar = Never;
    type Arm = Never;
    type Marker = Never;

    #[expect(
        clippy::uninhabited_references,
        reason = "a `&Never` cannot be constructed; the empty match documents vacuity"
    )]
    fn each_sugar_child<F: FnMut(&S<Expr<Self>>)>(s: &Self::Sugar, _f: &mut F) {
        match *s {}
    }

    #[expect(
        clippy::uninhabited_references,
        reason = "a `&Never` cannot be constructed; the empty match documents vacuity"
    )]
    fn each_arm_child<F: FnMut(&S<Expr<Self>>)>(a: &Self::Arm, _f: &mut F) {
        match *a {}
    }
}

// The default phase is `Surface`, so a bare `Expr`/`HandlerArm` (parser,
// formatter, resolver, the desugar input) means the full sugar-bearing AST.
pub type SExpr = S<Expr<Surface>>;

// Surface-only handler clauses, all rewritten to `Op` by desugar. `Once` is
// tail-resumptive (`once op(x) => e` is `op(x, k) => k(e)`). `Val` is an
// install-time constant (`val v = e` binds e once before the handler, each `v()`
// resumes with it). `Never` never resumes (`never op(x) => e` discards k).
#[derive(Clone, Debug)]
pub enum SugarArm<P: Phase> {
    Once(String, Vec<String>, S<Expr<P>>),
    Val(String, S<Expr<P>>),
    Never(String, Vec<String>, S<Expr<P>>),
}

#[derive(Clone, Debug)]
pub enum HandlerArm<P: Phase = Surface> {
    Return(String, S<Expr<P>>),
    Op(String, Vec<String>, String, S<Expr<P>>),
    // The surface-only clauses. `P::Arm = Never` in core, so this is dead there.
    Sugar(P::Arm),
}

impl<P: Phase> HandlerArm<P> {
    pub fn each_child(&self, f: &mut impl FnMut(&S<Expr<P>>)) {
        match self {
            Self::Return(_, body) | Self::Op(_, _, _, body) => f(body),
            Self::Sugar(a) => P::each_arm_child(a, f),
        }
    }
}

// The surface-only expression forms, removed by desugar.
#[derive(Clone, Debug)]
pub enum Sugar<P: Phase> {
    // `with f <- handler { .. }`: a named handler instance. Desugar clones the
    // handled ops into a fresh private effect and rewrites `f.op(..)` to it,
    // so dispatch targets this handler regardless of dynamically nearer ones.
    NamedHandle(String, Box<S<Expr<P>>>, Vec<HandlerArm<P>>),
    VarDecl(String, Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    Assign(String, Box<S<Expr<P>>>),
    // `recv[key] := value` on a `var`: a functional indexed write that rebinds
    // the root variable. Desugars to `root := index_set(...)` (nested for
    // `grid[i][j] := v`); the formatter restores this surface form.
    IndexAssign(Box<S<Expr<P>>>, Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    Throw(String, Vec<S<Expr<P>>>),
    TryCatch(Box<S<Expr<P>>>, Vec<CatchArm<P>>),
    // `for x in s, <quals> do body`: the generator drives an emit-consumer. The
    // qualifiers (guards, binders) fold inside-out around the body.
    For(String, Box<S<Expr<P>>>, Vec<Qualifier<P>>, Box<S<Expr<P>>>),
    // `while cond do body` (`Some(cond)`) or `loop body` (`None`, an unconditional
    // loop). Desugars to the tail-recursive prelude `repeat_while`; `break`/
    // `continue` in the body add internal, fully-handled `Break`/`Continue` effects.
    While(Option<Box<S<Expr<P>>>>, Box<S<Expr<P>>>),
    // `break` / `continue` inside a loop body: non-resumable performs of the
    // internal loop-control effects, caught by the enclosing loop's handlers.
    Break,
    Continue,
    // `return e`: a non-resumable perform of the internal `Return` effect, caught
    // by the handler wrapped around the enclosing function's body.
    Return(Box<S<Expr<P>>>),
    // `[ head for x in s, <quals> ]`: the comprehension. Lowers to a stream that
    // emits `head` per surviving element, collected with `scollect`.
    Comp(Box<S<Expr<P>>>, String, Box<S<Expr<P>>>, Vec<Qualifier<P>>),
    // `a ?? b`: run `a` in a `Fail` context, falling back to `b` on failure.
    Default(Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    // `transact body else fallback`: snapshot every live `var`, run `body` in a
    // `Fail` context, and on failure restore each var before yielding `fallback`,
    // so a failed attempt leaves observable state unchanged.
    Transact(Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    // `probe "name" do body`: source-level instrumentation. Desugars to an
    // environment-gated branch, so a disabled probe evaluates neither body nor
    // any formatting work inside it.
    Probe(String, Box<S<Expr<P>>>),
    // `a?.b`: failable field access through an option, `force(a).b`. A `None`
    // raises `Fail`, so chains like `a?.b?.c` short-circuit and default with
    // `??`. Meaningful only inside a failure context.
    OptChain(Box<S<Expr<P>>>, String),
    // `[a..z]` / `[a, b..z]`: a Haskell-style arithmetic sequence. The prefix
    // (one or more exprs) sets the start and, from its first two, the step;
    // desugars to prelude `enum_from_to` / `enum_from_then_to`.
    Range(Vec<S<Expr<P>>>, Box<S<Expr<P>>>),
    // Point-free function composition `f >> g` (forward, `true`) or `f << g`
    // (backward, `false`). Kept as sugar so the surface operator survives
    // formatting; desugar lowers it to `\x -> g(f(x))` / `\x -> f(g(x))`.
    Compose(bool, Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    // `s.[ path ]`: read every focus the path selects into a `List`, the read
    // twin of the `{ s | path = .. }` update. Desugars to a `map`/`concat` fold.
    ReadPath(Box<S<Expr<P>>>, Vec<PathStep<P>>),
}

// One step of an update path, read left to right. `Field(f)` descends into a
// record field; `Each` fans out over every element of a functor; `Case(C)`
// focuses through a sum constructor (a prism), leaving other constructors
// untouched; `Index(i)` focuses one element of an array/list; `Where(p)` keeps
// only foci satisfying `p`. All but `Field` are removed by desugar (lowered to
// `fmap`, a `match`, `index_set`, and a guard), so a path that reaches
// tc/elaborate is `Field`-only.
#[derive(Clone, Debug)]
pub enum PathStep<P: Phase = Surface> {
    Field(String),
    Each,
    Case(String),
    Index(S<Expr<P>>),
    Where(S<Expr<P>>),
}

impl<P: Phase> PathStep<P> {
    // The subterm an `[i]` index or a `where p` filter carries, the steps a
    // surface traversal must descend into.
    pub const fn sub_expr(&self) -> Option<&S<Expr<P>>> {
        match self {
            Self::Index(e) | Self::Where(e) => Some(e),
            _ => None,
        }
    }

    pub const fn sub_expr_mut(&mut self) -> Option<&mut S<Expr<P>>> {
        match self {
            Self::Index(e) | Self::Where(e) => Some(e),
            _ => None,
        }
    }
}

// The terminal action of an update path. `= e` (`Set`) replaces the focus with
// `e`; `~ f` (`Modify`) applies `f` to the current focus. The distinction is
// purely in the desugaring: `Set` ignores the old focus, `Modify` reads it and
// calls `f`. Both carry an ordinary expression, so neither reaches the core.
#[derive(Clone, Debug)]
pub enum PathOp<P: Phase = Surface> {
    Set(S<Expr<P>>),
    Modify(S<Expr<P>>),
}

impl<P: Phase> PathOp<P> {
    pub const fn expr(&self) -> &S<Expr<P>> {
        match self {
            Self::Set(e) | Self::Modify(e) => e,
        }
    }

    pub const fn expr_mut(&mut self) -> &mut S<Expr<P>> {
        match self {
            Self::Set(e) | Self::Modify(e) => e,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr<P: Phase = Surface> {
    Int(IntLit),
    Float(f64),
    Char(char),
    Bool(bool),
    Unit,
    Str(String),
    Var(String),
    Bin(BinOp, Box<S<Self>>, Box<S<Self>>),
    // Unary minus. Binds looser than application, projection, and postfix but
    // tighter than every binary operator, so `-f(x)` is `-(f(x))` and `-x * y`
    // is `(-x) * y`. The numeric lane (Int/I64/Float) is resolved by the checker
    // and recorded on this node's `NodeId`; elaboration lowers it per lane (exact
    // bignum negation, two's-complement wrap on I64, IEEE sign flip on Float).
    Neg(Box<S<Self>>),
    If(Box<S<Self>>, Box<S<Self>>, Box<S<Self>>),
    Let(String, Box<S<Self>>, Box<S<Self>>),
    Lam(Vec<Param<P>>, Box<S<Self>>),
    Call(Box<S<Self>>, Vec<S<Self>>),
    Pipe(Box<S<Self>>, Box<S<Self>>),
    Match(Box<S<Self>>, Vec<Arm<P>>),
    List(Vec<S<Self>>),
    Tuple(Vec<S<Self>>),
    FieldAccess(Box<S<Self>>, String),
    // Unboxed product values, the `#` sigil forms: `#(a, b)` builds an unboxed
    // tuple, `#{ x = a, y = b }` an unboxed record (anonymous, structural, unlike
    // the nominal `RecordCreate`), and `e.#field` projects an unboxed record field.
    UnboxedTuple(Vec<S<Self>>),
    UnboxedRecord(Vec<(String, S<Self>)>),
    UnboxedField(Box<S<Self>>, String),
    RecordCreate(String, Vec<(String, S<Self>)>),
    RecordUpdate(Box<S<Self>>, String, Vec<(String, S<Self>)>),
    // `{ base | a.b.c = v, xs.each ~ f }`: nested functional update along paths
    // of steps (`Field`/`Each`/`Case`/`Index`). Each path ends in a `PathOp`:
    // `= v` sets the focus, `~ f` modifies it. `Field`-only paths rebuild
    // single-constructor records (reused in place by the reuse pass); the optic
    // steps desugar to `fmap`/`match`/`index_set`.
    RecordUpdatePath(Box<S<Self>>, Vec<(Vec<PathStep<P>>, PathOp<P>)>),
    Handle(Box<S<Self>>, Vec<HandlerArm<P>>),
    Mask(String, Box<S<Self>>),
    Inst(Box<S<Self>>, Vec<String>),
    // `recv[key]`: a failable indexed read, dispatched at elaboration on the
    // head type of `recv` (Array/HashMap/String/List) to a builtin accessor.
    // Reads perform `Fail` when the index or key is absent.
    Index(Box<S<Self>>, Box<S<Self>>),
    // A functional indexed write `index_set(recv, key, val)` returning the new
    // container, dispatched at elaboration on `recv`'s head type to the in-place
    // (FBIP) setter. Produced by desugaring `recv[key] := val`, never written.
    IndexSet(Box<S<Self>>, Box<S<Self>>, Box<S<Self>>),
    Ann(Box<S<Self>>, Ty),
    // A compiler-synthesized parse-time marker, never a source variable. Each is
    // consumed (or rejected) by desugar; the formatter restores its surface form.
    // A dedicated variant so a marker can never masquerade as an ordinary `Var`
    // detected by string comparison. `P::Marker = Never` in core, so dead there.
    Marker(P::Marker),
    // The surface-only forms. `P::Sugar = Never` in core, so this is dead there.
    Sugar(P::Sugar),
}

impl<P: Phase> Expr<P> {
    /// Visit each directly-nested expression child.
    ///
    /// This is the single exhaustive statement of `Expr`'s structural children:
    /// walkers that recurse through it cannot silently drop a new expression
    /// variant, and adding a variant forces an update here rather than a quiet
    /// miss at every hand-written `match`.
    pub fn each_child(&self, f: &mut impl FnMut(&S<Self>)) {
        match self {
            Self::Bin(_, a, b) | Self::Let(_, a, b) | Self::Pipe(a, b) | Self::Index(a, b) => {
                f(a);
                f(b);
            }
            Self::Neg(a)
            | Self::Lam(_, a)
            | Self::FieldAccess(a, _)
            | Self::UnboxedField(a, _)
            | Self::Inst(a, _)
            | Self::Ann(a, _)
            | Self::Mask(_, a) => f(a),
            Self::If(a, b, c) | Self::IndexSet(a, b, c) => {
                f(a);
                f(b);
                f(c);
            }
            Self::Call(head, args) => {
                f(head);
                for a in args {
                    f(a);
                }
            }
            Self::Match(scrut, arms) => {
                f(scrut);
                for a in arms {
                    if let Some(g) = &a.guard {
                        f(g);
                    }
                    f(&a.body);
                }
            }
            Self::List(items) | Self::Tuple(items) | Self::UnboxedTuple(items) => {
                for a in items {
                    f(a);
                }
            }
            Self::RecordCreate(_, fields) | Self::UnboxedRecord(fields) => {
                for (_, value) in fields {
                    f(value);
                }
            }
            Self::RecordUpdate(base, _, fields) => {
                f(base);
                for (_, value) in fields {
                    f(value);
                }
            }
            Self::RecordUpdatePath(base, updates) => {
                f(base);
                for (steps, op) in updates {
                    for step in steps {
                        if let Some(e) = step.sub_expr() {
                            f(e);
                        }
                    }
                    f(op.expr());
                }
            }
            Self::Handle(body, arms) => {
                f(body);
                for a in arms {
                    a.each_child(f);
                }
            }
            Self::Sugar(s) => P::each_sugar_child(s, f),
            Self::Int(_)
            | Self::Float(_)
            | Self::Char(_)
            | Self::Bool(_)
            | Self::Unit
            | Self::Str(_)
            | Self::Var(_)
            | Self::Marker(_) => {}
        }
    }
}

// Parse-time markers stuffed into the expression tree, all removed by desugar.
// `With` is a standalone placeholder for a trailing `with` (rejected). `Try`
// and `Interp` are call heads: `Try` marks `e?`, `Interp` marks an interpolated
// string literal whose call alternates segments and holes.
#[derive(Clone, Debug)]
pub enum Marker {
    With,
    Try,
    Interp,
}

// A comprehension/loop qualifier following the generator: a Bool `if` filter or
// a `let` binder. A failing guard or binder prunes the element.
#[derive(Clone, Debug)]
pub enum Qualifier<P: Phase = Surface> {
    Guard(S<Expr<P>>),
    Bind(String, S<Expr<P>>),
}

impl<P: Phase> Qualifier<P> {
    pub fn each_child(&self, f: &mut impl FnMut(&S<Expr<P>>)) {
        match self {
            Self::Guard(e) | Self::Bind(_, e) => f(e),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CatchArm<P: Phase = Surface> {
    pub name: String,
    pub binders: Vec<String>,
    pub body: S<Expr<P>>,
    pub span: Span,
}

#[derive(Clone)]
pub struct Arm<P: Phase = Surface> {
    pub pat: S<Pattern>,
    pub guard: Option<S<Expr<P>>>,
    pub body: S<Expr<P>>,
}

// An absent guard is omitted from the debug dump, matching the derived
// output for guard-free arms.
impl<P: Phase + fmt::Debug> fmt::Debug for Arm<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Arm");
        d.field("pat", &self.pat);
        if let Some(g) = &self.guard {
            d.field("guard", g);
        }
        d.field("body", &self.body).finish()
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wild,
    Var(String),
    Int(IntLit),
    Float(f64),
    Char(char),
    Bool(bool),
    Ctor(String, Vec<S<Self>>),
    Tuple(Vec<S<Self>>),
    Record(String, Vec<(String, S<Self>)>, bool),
}
