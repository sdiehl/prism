pub use marginalia::Span;
pub use num_bigint::BigInt;

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

impl std::fmt::Display for IntLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self.suffix {
            Suffix::None => "",
            Suffix::I64 => "i64",
            Suffix::U64 => "u64",
        };
        write!(f, "{}{}", self.value, s)
    }
}

#[derive(Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
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
            synth: false,
        }
    }
    #[must_use]
    pub const fn sugar(node: T, span: Span) -> Self {
        Self {
            node,
            span,
            synth: true,
        }
    }
}

// Show `synth` only when set, so a sugar node stands out and non-sugar nodes
// render identically to the derived form.
impl<T: std::fmt::Debug> std::fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    pub patterns: Vec<PatternDecl<P>>,
    pub fns: Vec<Decl<P>>,
    // Module imports, resolved away by the name-resolution pass.
    pub imports: Vec<ImportDecl>,
    // Top-level names marked `pub`. Visibility lives here, off the decls, so an
    // AST dump of a `pub`-free program is byte-identical to one without modules.
    pub exports: std::collections::BTreeSet<String>,
    // Type names marked `opaque`: exported by name but with their constructors
    // hidden outside the defining module. A subset of `exports`.
    pub opaques: std::collections::BTreeSet<String>,
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

// `patterns`, `imports`, and `exports` are omitted from the debug dump when
// empty, matching the derived output for import-free, pattern-free programs.
impl<P: Phase + std::fmt::Debug> std::fmt::Debug for Program<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
        d.finish()
    }
}

// `import Data.Map`, `import List (map, filter)`, `import Json as J`. The path
// is the dotted module path. `names` present means a selective unqualified
// import; absent means a qualified import bound under `alias` or the last path
// component.
#[derive(Clone, Debug)]
pub struct ImportDecl {
    pub path: Vec<String>,
    pub alias: Option<String>,
    pub names: Option<Vec<String>>,
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
    Pattern(PatternDecl),
    Fn(Decl),
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

#[derive(Clone, Debug)]
pub struct EffectDecl {
    pub name: String,
    pub params: Vec<String>,
    pub ops: Vec<EffOp>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EffOp {
    pub name: String,
    pub params: Vec<Ty>,
    pub ret: Ty,
}

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
    pub span: Span,
}

// `konst` is shown only when set, so a plain `fn` dumps identically to the
// pre-constant form and a constant stands out.
impl<P: Phase + std::fmt::Debug> std::fmt::Debug for Decl<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    State(u32),
    Forall(Vec<String>, Box<Self>),
    Fun(Vec<Self>, Row, Box<Self>),
    Con(String, Vec<Self>),
    Tuple(Vec<Self>),
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
    Addf,
    Subf,
    Mulf,
    Divf,
    Eqf,
    Nef,
    Ltf,
    Lef,
    Gtf,
    Gef,
}

impl BinOp {
    /// The canonical source spelling of this operator.
    #[must_use]
    pub const fn spelling(self) -> &'static str {
        use crate::kw;
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
            Self::Addf => kw::PLUS_DOT,
            Self::Subf => kw::MINUS_DOT,
            Self::Mulf => kw::STAR_DOT,
            Self::Divf => kw::SLASH_DOT,
            Self::Eqf => kw::EQ_DOT,
            Self::Nef => kw::NE_DOT,
            Self::Ltf => kw::LT_DOT,
            Self::Lef => kw::LE_DOT,
            Self::Gtf => kw::GT_DOT,
            Self::Gef => kw::GE_DOT,
        }
    }
}

// The compilation phase an expression tree belongs to. `Surface` is the parsed
// sugar-bearing AST; `Core` is desugar's output, where the sugar payloads become
// the uninhabited `Never` so every sugar variant is statically impossible and
// downstream passes need no arm for it. `Phase` threads through `Expr`/
// `HandlerArm` (and the structs holding them) so one set of definitions serves
// both phases.
pub trait Phase {
    // Payload of `Expr::Sugar` (the surface-only expression forms).
    type Sugar: Clone + std::fmt::Debug;
    // Payload of `HandlerArm::Sugar` (the three surface-only handler clauses).
    type Arm: Clone + std::fmt::Debug;
    // Payload of `Expr::Marker` (the parse-time markers).
    type Marker: Clone + std::fmt::Debug;
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
}
impl Phase for Core {
    type Sugar = Never;
    type Arm = Never;
    type Marker = Never;
}

// The default phase is `Surface`, so a bare `Expr`/`HandlerArm` (parser,
// formatter, resolver, the desugar input) means the full sugar-bearing AST.
pub type SExpr = S<Expr<Surface>>;

// Surface-only handler clauses, all rewritten to `Op` by desugar. `Fun` is
// tail-resumptive (`fun op(x) => e` is `op(x, k) => k(e)`). `Val` is an
// install-time constant (`val v = e` binds e once before the handler, each `v()`
// resumes with it). `Final` never resumes (`final ctl op(x) => e` discards k).
#[derive(Clone, Debug)]
pub enum SugarArm<P: Phase> {
    Fun(String, Vec<String>, S<Expr<P>>),
    Val(String, S<Expr<P>>),
    Final(String, Vec<String>, S<Expr<P>>),
}

#[derive(Clone, Debug)]
pub enum HandlerArm<P: Phase = Surface> {
    Return(String, S<Expr<P>>),
    Op(String, Vec<String>, String, S<Expr<P>>),
    // The surface-only clauses. `P::Arm = Never` in core, so this is dead there.
    Sugar(P::Arm),
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
    Throw(String, Vec<S<Expr<P>>>),
    TryCatch(Box<S<Expr<P>>>, Vec<CatchArm<P>>),
    // `for x in s, <quals> do body`: the generator drives an emit-consumer. The
    // qualifiers (guards, binders) fold inside-out around the body.
    For(String, Box<S<Expr<P>>>, Vec<Qualifier<P>>, Box<S<Expr<P>>>),
    // `[ head for x in s, <quals> ]`: the comprehension. Lowers to a stream that
    // emits `head` per surviving element, collected with `scollect`.
    Comp(Box<S<Expr<P>>>, String, Box<S<Expr<P>>>, Vec<Qualifier<P>>),
    // `a ?? b`: run `a` in a `Fail` context, falling back to `b` on failure.
    Default(Box<S<Expr<P>>>, Box<S<Expr<P>>>),
    // `transact body else fallback`: snapshot every live `var`, run `body` in a
    // `Fail` context, and on failure restore each var before yielding `fallback`,
    // so a failed attempt leaves observable state unchanged.
    Transact(Box<S<Expr<P>>>, Box<S<Expr<P>>>),
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
    If(Box<S<Self>>, Box<S<Self>>, Box<S<Self>>),
    Let(String, Box<S<Self>>, Box<S<Self>>),
    Lam(Vec<Param<P>>, Box<S<Self>>),
    Call(Box<S<Self>>, Vec<S<Self>>),
    Pipe(Box<S<Self>>, Box<S<Self>>),
    Match(Box<S<Self>>, Vec<Arm<P>>),
    List(Vec<S<Self>>),
    Tuple(Vec<S<Self>>),
    FieldAccess(Box<S<Self>>, String),
    RecordCreate(String, Vec<(String, S<Self>)>),
    RecordUpdate(Box<S<Self>>, String, Vec<(String, S<Self>)>),
    // `{ base | a.b.c = v, d = w }`: nested functional update along field
    // paths, each level a single-constructor rebuild (reusable under Perceus).
    RecordUpdatePath(Box<S<Self>>, Vec<(Vec<String>, S<Self>)>),
    Handle(Box<S<Self>>, Vec<HandlerArm<P>>),
    Mask(String, Box<S<Self>>),
    Inst(Box<S<Self>>, Vec<String>),
    Ann(Box<S<Self>>, Ty),
    // A compiler-synthesized parse-time marker, never a source variable. Each is
    // consumed (or rejected) by desugar; the formatter restores its surface form.
    // A dedicated variant so a marker can never masquerade as an ordinary `Var`
    // detected by string comparison. `P::Marker = Never` in core, so dead there.
    Marker(P::Marker),
    // The surface-only forms. `P::Sugar = Never` in core, so this is dead there.
    Sugar(P::Sugar),
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
// a `let` binder. A failing guard or binder (Wave 2) prunes the element.
#[derive(Clone, Debug)]
pub enum Qualifier<P: Phase = Surface> {
    Guard(S<Expr<P>>),
    Bind(String, S<Expr<P>>),
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
impl<P: Phase + std::fmt::Debug> std::fmt::Debug for Arm<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
