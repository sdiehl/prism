mod code;
mod lex;
mod parse;
mod phase;
pub mod suggest;

pub use code::{ErrorCode, ErrorPhase};
pub use lex::LexError;
pub use parse::ParseError;
pub use phase::Error;

use std::ops::Range;

use ariadne::{Color, Config, Label, Report, ReportKind, Source};

use crate::driver::{PRELUDE, PRELUDE_END_MARK};
use marginalia::Span;
use thiserror::Error;

/// Locates the prelude prefix that `with_prelude` prepends, so positions shown
/// to users are relative to their own file. Spans inside the prelude are
/// reported against the prelude explicitly.
#[derive(Debug)]
pub struct SourceMap<'a> {
    full: &'a str,
    prelude: usize,
}

impl<'a> SourceMap<'a> {
    #[must_use]
    pub fn new(full: &'a str) -> Self {
        let n = PRELUDE.len() + 1;
        let prelude =
            if full.len() >= n && full.as_bytes()[n - 1] == b'\n' && full.starts_with(PRELUDE) {
                n
            } else {
                custom_prelude_end(full)
            };
        Self { full, prelude }
    }

    #[must_use]
    pub fn user(&self) -> &'a str {
        &self.full[self.prelude..]
    }

    /// Byte offset where the user's own source begins (0 when no prelude prefix
    /// is present). Spans below it belong to the prepended prelude.
    #[must_use]
    pub const fn prelude_len(&self) -> usize {
        self.prelude
    }

    #[must_use]
    pub fn at(&self, byte: usize) -> String {
        if byte < self.prelude {
            let (l, c) = line_col(self.full, byte);
            format!("line {l}:{c} (in prelude)")
        } else {
            let (l, c) = line_col(self.user(), byte - self.prelude);
            format!("line {l}:{c}")
        }
    }
}

// Locate the boundary a custom prelude stamped (`with_custom_prelude`): the
// byte offset just past the first `PRELUDE_END_MARK` line, or 0 when the source
// carries no custom prelude. The first occurrence is authoritative; the mark's
// spelling is not one ordinary source or the formatter produces.
fn custom_prelude_end(full: &str) -> usize {
    let line = format!("{PRELUDE_END_MARK}\n");
    if full.starts_with(&line) {
        return line.len();
    }
    let sep = format!("\n{line}");
    full.find(&sep).map_or(0, |pos| pos + sep.len())
}

pub(crate) fn line_col(src: &str, byte: usize) -> (u32, u32) {
    let (mut line, mut col) = (1u32, 1u32);
    for (i, c) in src.char_indices() {
        if i >= byte {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("unbound variable '{name}'")]
    UnboundVariable { span: Span, name: String },
    #[error("type mismatch: expected {expected}, got {found}")]
    TypeMismatch {
        span: Span,
        expected: String,
        found: String,
    },
    #[error("{msg}")]
    ScopeFailure { span: Span, msg: String },
    /// A located diagnostic from the structured, coded catalogue ([`ErrKind`]),
    /// with its provenance ([`Diag`]). This is the home every semantic checker
    /// failure is migrating to.
    #[error("{0}")]
    Kind(Box<Diag>),
    #[error("{msg}")]
    TypeFailure { span: Span, msg: String },
    #[error("internal compiler error (please report): {msg}")]
    InternalInvariant { msg: String },
}

/// One frame of an error's context stack: where the failure arose.
///
/// Frames are pushed innermost-last as the error unwinds; the renderer shows them
/// outermost-first as `in `...`:` prefixes. Structured (not a pre-rendered string)
/// so a future renderer can present the descent as a list or use it for blame
/// heuristics.
#[derive(Debug, Clone)]
pub enum Frame {
    /// Checking the body of the named top-level function or method.
    InFn(String),
}

impl std::fmt::Display for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InFn(name) => write!(f, "in `{name}`"),
        }
    }
}

/// A located diagnostic: the structured error [`ErrKind`] plus the provenance and
/// guidance a good message carries.
///
/// - `context` is the descent stack (the *where*): `in fn foo`, `while resolving
///   Eq(Foo)`, ...
/// - `labels` are secondary spans: the *other* locations that contribute to the
///   failure (the conflicting site, the annotation that forced the expectation).
/// - `help` is one actionable suggestion; `notes` are extra explanation.
///
/// Built ergonomically with [`ErrKind::at`] and the chained builders, so a site
/// reads `ErrKind::NoInstance { .. }.at(span).with_help("derive `Eq`")`.
#[derive(Debug, Clone)]
pub struct Diag {
    pub span: Span,
    pub kind: ErrKind,
    pub context: Vec<Frame>,
    pub labels: Vec<(Span, String)>,
    pub help: Option<String>,
    pub notes: Vec<String>,
}

impl Diag {
    #[must_use]
    pub const fn new(span: Span, kind: ErrKind) -> Self {
        Self {
            span,
            kind,
            context: Vec::new(),
            labels: Vec::new(),
            help: None,
            notes: Vec::new(),
        }
    }

    /// Attach a secondary span with its own label (a contributing location).
    #[must_use]
    pub fn label(mut self, span: Span, msg: impl Into<String>) -> Self {
        self.labels.push((span, msg.into()));
        self
    }

    /// Attach a single actionable suggestion.
    #[must_use]
    pub fn with_help(mut self, msg: impl Into<String>) -> Self {
        self.help = Some(msg.into());
        self
    }

    /// Attach an explanatory note.
    #[must_use]
    pub fn note(mut self, msg: impl Into<String>) -> Self {
        self.notes.push(msg.into());
        self
    }
}

impl std::fmt::Display for Diag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Context frames render outermost-first (last-pushed is innermost), the
        // same `in `f`: ` nesting the prior string-wrapping produced.
        for frame in self.context.iter().rev() {
            write!(f, "{frame}: ")?;
        }
        write!(f, "{}", self.kind)
    }
}

impl ErrKind {
    /// Locate this error kind at `span`, producing a [`TypeError`] with empty
    /// provenance ready to enrich via the builders below.
    #[must_use]
    pub fn at(self, span: Span) -> TypeError {
        TypeError::Kind(Box::new(Diag::new(span, self)))
    }
}

impl TypeError {
    /// Attach an actionable suggestion (a no-op on the legacy variants). Chains
    /// after [`ErrKind::at`]: `ErrKind::UnknownClass { .. }.at(span).with_help(..)`.
    #[must_use]
    pub fn with_help(mut self, msg: impl Into<String>) -> Self {
        if let Self::Kind(diag) = &mut self {
            diag.help = Some(msg.into());
        }
        self
    }

    /// Attach a suggestion only when one exists, the shape `suggest::suggestion`
    /// returns: `.maybe_help(suggestion(name, in_scope))`.
    #[must_use]
    pub fn maybe_help(mut self, msg: Option<String>) -> Self {
        if let (Self::Kind(diag), Some(m)) = (&mut self, msg) {
            diag.help = Some(m);
        }
        self
    }

    /// Attach a secondary span with its own label (a contributing location).
    #[must_use]
    pub fn label(mut self, span: Span, msg: impl Into<String>) -> Self {
        if let Self::Kind(diag) = &mut self {
            diag.labels.push((span, msg.into()));
        }
        self
    }

    /// Attach an explanatory note.
    #[must_use]
    pub fn note(mut self, msg: impl Into<String>) -> Self {
        if let Self::Kind(diag) = &mut self {
            diag.notes.push(msg.into());
        }
        self
    }
}

/// The structured catalogue of typechecker error kinds.
///
/// One variant per semantic failure the checker reports. Each carries the facts
/// of the failure (the offending name, the mismatched types, the class) as typed
/// fields rather than a pre-rendered string, so provenance survives onto the
/// value; its `#[error("...")]` attribute is the single home of the message text,
/// and [`ErrKind::code`] its stable diagnostic code. New checker errors are added
/// here, never as an inline `format!`.
#[derive(Debug, Clone, Error)]
pub enum ErrKind {
    /// The receiver of an `a[i]` index has no indexable type.
    #[error("type `{ty}` is not indexable with `[]`")]
    NotIndexable { ty: String },
    // --- scope ---
    /// A variable was used with no binder in scope.
    #[error("unbound variable '{name}'")]
    UnboundVar { name: String },
    // --- types ---
    #[error(
        "type mismatch in recursive `{name}`: expected {expected}, got {found}. \
                 If `{name}` is called at more than one type within its recursion group that is \
                 polymorphic recursion; add a type signature to `{name}`."
    )]
    PolyRecursionMismatch {
        name: String,
        expected: String,
        found: String,
    },
    #[error("unknown type `{name}`")]
    UnknownType { name: String },
    #[error(
        "`OrNull` requires a non-null, single-word element (a heap type or tagged scalar); {found} does not qualify"
    )]
    OrNullBadElement { found: String },
    #[error("`{name}` is applied to too many arguments: it takes {takes}, but {given} were given")]
    TooManyTypeArgs {
        name: String,
        takes: usize,
        given: usize,
    },
    #[error("kind mismatch: parameter {index} of `{name}` has kind `{expected}`, but a `{actual}` was given")]
    KindMismatch {
        index: usize,
        name: String,
        expected: String,
        actual: String,
    },
    #[error(
        "impredicative type: a polymorphic type cannot be a type argument to `{head}` \
                 (a type parameter ranges over monomorphic types). Higher-rank types are \
                 allowed as function arguments, results, and declared data fields; wrap the \
                 polymorphic type in a data type with a polymorphic field to carry it here."
    )]
    ImpredicativeTypeArg { head: String },
    #[error("integer literal out of range for {ty}")]
    IntLiteralOutOfRange { ty: String },
    #[error("unknown record constructor {ctor}")]
    UnknownRecordCtor { ctor: String },
    #[error("{ctor} is not a record constructor")]
    NotRecordCtor { ctor: String },
    #[error("missing field(s) {fields} in {ctor}")]
    MissingFields { fields: String, ctor: String },
    #[error("field access on non-record type {ty}")]
    FieldAccessNonRecord { ty: String },
    /// Unboxed-values surface (`#(...)`, `#{...}`, `.#field`) parsed, but its
    /// representation-aware checking and lowering are not implemented yet. The
    /// `what` names the form ("tuples", "records", "projection").
    #[error("unboxed {what} are not lowered: the `#` surface parses, but representation-aware compilation is not implemented")]
    UnboxedUnsupported { what: String },
    #[error("conflicting update paths `{a}` and `{b}`")]
    ConflictingUpdatePaths { a: String, b: String },
    #[error("internal: optic path step survived desugaring")]
    OpticPathSurvived,
    #[error("field path segment `{seg}` on non-record type {ty}")]
    FieldPathNonRecord { seg: String, ty: String },
    #[error("update path needs a single-constructor record, `{ty}` has {n} constructors")]
    UpdatePathMultiCtor { ty: String, n: usize },
    #[error("type `{ty}` does not support indexed assignment `a[i] := v`")]
    NotIndexAssignable { ty: String },
    #[error("cannot negate an unsigned `U64` value; unary minus is defined on `Int`, `I64`, and `Float`")]
    NegateUnsigned,
    #[error("function expects {expected} arguments, got {got}")]
    ArgCountMismatch { expected: usize, got: usize },
    #[error("cannot apply non-function {ty}")]
    ApplyNonFunction { ty: String },
    // --- classes ---
    #[error("`{name}` has a where clause and needs full parameter and return type annotations")]
    WhereClauseNeedsAnnotations { name: String },
    #[error("unknown class {class}")]
    UnknownClass { class: String },
    #[error("explicit instance selection `f(using ..)` requires a named function")]
    InstSelectNeedsName,
    #[error("`{name}` has {expected} constraint(s), got {got} instance argument(s)")]
    ConstraintArgCountMismatch {
        name: String,
        expected: usize,
        got: usize,
    },
    #[error("`{name}` has no class constraints to instantiate")]
    NoClassConstraints { name: String },
    #[error("ambiguous constraint {class}({ty}): it must mention a type variable from the signature of `{name}`")]
    AmbiguousConstraint {
        class: String,
        ty: String,
        name: String,
    },
    #[error("instance method `{inst}.{method}` performs {effects}, which the class method signature does not permit; a universally quantified effect row obligates parametricity, not permission to choose a concrete effect")]
    InstanceMethodImpure {
        inst: String,
        method: String,
        effects: String,
    },
    #[error("cyclic instance resolution: {class}({ty}) depends on itself")]
    CyclicInstance { class: String, ty: String },
    #[error("instance resolution for {class}({ty}) is too deep")]
    InstanceTooDeep { class: String, ty: String },
    #[error("unknown instance `{name}`")]
    UnknownInstance { name: String },
    #[error("instance `{name}` is for class {found}, expected {class}")]
    InstanceClassMismatch {
        name: String,
        found: String,
        class: String,
    },
    #[error("ambiguous instance for {class}({ty}): {listed}; designate one with `canonical {class}({ty}) = name`")]
    AmbiguousInstance {
        class: String,
        ty: String,
        listed: String,
    },
    #[error("no instance for {class}({ty})")]
    NoInstance { class: String, ty: String },
    #[error("instance `{inst}` : {class}({head}) does not match {ty}")]
    InstanceHeadMismatch {
        inst: String,
        class: String,
        head: String,
        ty: String,
    },
    #[error("cannot infer the type for constraint {class}(_); add a type annotation")]
    CannotInferConstraint { class: String },
    #[error("cannot discharge constraint {class}({var}); add `given {class}({var})` to the enclosing function")]
    CannotDischargeConstraint { class: String, var: String },
    #[error("superclass cycle: {path}")]
    SuperclassCycle { path: String },
    #[error("duplicate class {name}")]
    DuplicateClass { name: String },
    #[error("class method `{method}` must have a function type")]
    ClassMethodNotFunction { method: String },
    #[error("class method `{method}` must mention the class parameter `{param}`")]
    ClassMethodMissingParam { method: String, param: String },
    #[error("class method `{method}` clashes with an existing definition")]
    ClassMethodClash { method: String },
    #[error("instance name `{name}` clashes with an existing definition")]
    InstanceNameClash { name: String },
    #[error("class {class} names unknown superclass {sup}")]
    UnknownSuperclass { class: String, sup: String },
    #[error("instance head must be a primitive type or a data type constructor")]
    InstanceHeadNotType,
    #[error("instance head arguments must be distinct type variables")]
    InstanceHeadArgsNotVars,
    #[error("instance context constraints must be over the head's type variables")]
    InstanceContextNotHeadVars,
    #[error("duplicate method `{method}` in instance `{instance}`")]
    DuplicateInstanceMethod { method: String, instance: String },
    #[error("class {class} has no method `{method}`")]
    ClassHasNoMethod { class: String, method: String },
    #[error(
        "instance method `{method}` takes its signature from class {class}; drop the annotations"
    )]
    InstanceMethodAnnotated { method: String, class: String },
    #[error("method `{method}` of class {class} takes {arity} parameter(s), got {got}")]
    MethodArityMismatch {
        method: String,
        class: String,
        arity: usize,
        got: usize,
    },
    #[error("instance `{instance}` is missing method(s): {methods}")]
    InstanceMissingMethods { instance: String, methods: String },
    #[error("canonical head must be a primitive type or a data type constructor")]
    CanonicalHeadNotType,
    #[error("`{name}` is not an instance of {class}({ty})")]
    NotAnInstance {
        name: String,
        class: String,
        ty: String,
    },
    #[error("duplicate canonical designation for {class}({ty})")]
    DuplicateCanonical { class: String, ty: String },
    #[error("{n} instances for {class}({head}): {listed}; designate one with `canonical {class}({head}) = name`")]
    MultipleInstances {
        n: usize,
        class: String,
        head: String,
        listed: String,
    },
    // --- patterns ---
    #[error("unreachable match arm")]
    UnreachableMatchArm,
    #[error("non-exhaustive match: missing {witness}")]
    NonExhaustiveMatch { witness: String },
    #[error("suffixed literal patterns are not supported; match on Int")]
    SuffixedLiteralPattern,
    #[error("unknown record constructor {ctor_name}")]
    UnknownRecordConstructor { ctor_name: String },
    #[error("unknown field {field} on {ctor}")]
    UnknownField { field: String, ctor: String },
    #[error("unknown constructor {name}")]
    UnknownConstructor { name: String },
    #[error("constructor {name} expects {expected} arguments, got {got}")]
    CtorArity {
        name: String,
        expected: usize,
        got: usize,
    },
    #[error("no field `{field}` on type `{ctor_name}`")]
    NoFieldOnType { field: String, ctor_name: String },
    // --- effects ---
    #[error("effect `{name}` expects {want} type argument(s), got {got}")]
    EffectArity {
        name: String,
        want: usize,
        got: usize,
    },
    #[error("unknown effect `{name}`")]
    UnknownEffect { name: String },
    #[error("top-level constant `{name}` must be effect-free; it performs {effects}")]
    KonstNotPure { name: String, effects: String },
    #[error("`{name}` has a `borrow` parameter but is not pure; it performs {effects}")]
    BorrowNotPure { name: String, effects: String },
    #[error("`{name}` has a `borrow` parameter but forwards effects through its interface (its effect row {row} is shared with a parameter or result); a borrowed parameter requires a body that performs no effects, since the caller retains ownership across the call and a forwarded effect can suspend or capture it")]
    BorrowRowNotClosed { name: String, row: String },
    #[error("in `{name}`: effect `{eff}` not declared in annotation")]
    UndeclaredEffect { name: String, eff: String },
    #[error("unknown effect operation `{op}`")]
    UnknownEffectOp { op: String },
    #[error("effect instantiation mismatch: `{actual}` is not compatible with `{expected}`")]
    EffectInstMismatch { actual: String, expected: String },
    #[error("unknown effect `{eff}` in mask")]
    UnknownEffectInMask { eff: String },
    #[error("duplicate handler clause for operation `{op}`; a handler binds each operation exactly once")]
    DuplicateHandlerArm { op: String },
    #[error("duplicate `return` clause; a handler has at most one")]
    DuplicateReturnArm,
    #[error("handler clause for `{op}` binds {provided} parameter(s) besides the continuation, but the operation declares {declared}")]
    HandlerArmArity {
        op: String,
        declared: usize,
        provided: usize,
    },
    #[error("handler for effect `{effect}` is missing {missing}; a handler must implement every operation of the effect it handles")]
    IncompleteHandler { effect: String, missing: String },
    // --- declarations / desugar ---
    #[error("{kind} `{name}` is declared more than once")]
    DuplicateDecl { kind: String, name: String },
    #[error("{kind} cycle: {path}")]
    DefCycle { kind: String, path: String },
    #[error("unknown type synonym `{name}`")]
    UnknownSynonym { name: String },
    #[error("unknown effect alias `{name}`")]
    UnknownAlias { name: String },
    #[error("type synonym `{name}` expects {want} argument(s), got {got}")]
    SynonymArity {
        name: String,
        want: usize,
        got: usize,
    },
    #[error("unknown effect `{eff}` in alias `{alias}`")]
    UnknownEffectInAlias { eff: String, alias: String },
    #[error("effect `{name}` is a reserved name (reserved for {reason})")]
    ReservedEffectName { name: String, reason: String },
    #[error("operation `{op}` is declared in both `{first}` and `{second}`")]
    DuplicateEffectOp {
        op: String,
        first: String,
        second: String,
    },
    #[error("pattern `{name}` clashes with a constructor of the same name")]
    PatternClashesCtor { name: String },
    #[error("class-dispatched pattern `{name}` cannot have a `make` clause")]
    ClassPatternHasMake { name: String },
    #[error("class-dispatched pattern `{name}` view must name a method of `{class}`")]
    ClassPatternViewNotMethod { name: String, class: String },
    #[error("`{method}` is not a method of class `{class}`")]
    PatternViewUnknownMethod { method: String, class: String },
    #[error("view method `{method}` must be a one-argument function")]
    ViewMethodNotFunction { method: String },
    #[error("view method `{method}` must take exactly one argument")]
    ViewMethodArity { method: String },
    #[error("pattern `{name}` is for undeclared type or class `{ty}`")]
    PatternForUnknownType { name: String, ty: String },
    #[error(
        "`{clause}` clause of pattern `{pat}` must be a lambda, as in `{clause} \\(x) -> ...`"
    )]
    PatternClauseNotLambda { clause: String, pat: String },
    #[error(
        "`Stable` cannot be given a hand-written instance; its shape digest is \
         compiler-computed. Write `deriving (Stable)` on `{head}` instead."
    )]
    StableHandWritten { head: String },
    #[error("unknown class in deriving: {class}")]
    UnknownDerivingClass { class: String },
    #[error(
        "cannot derive {class} for {ty}; derivable are Eq, Ord, Show, Hash, \
         Serialize, Stable, Arbitrary, Lens"
    )]
    NotDerivable { class: String, ty: String },
    #[error("cannot derive Lens for {ty}: needs a single record constructor")]
    LensNeedsRecord { ty: String },
    #[error("cannot derive Lens for {ty}: `{ctor}` has no named fields")]
    LensNeedsNamedFields { ty: String, ctor: String },
    #[error(
        "cannot derive Stable for {ty}: {field} has type `{field_ty}`, which is not Stable. \
         A frozen format cannot contain a value that is not itself serializable."
    )]
    StableFieldNotStable {
        ty: String,
        field: String,
        field_ty: String,
    },
    #[error("empty string interpolation")]
    EmptyInterpolation,
    #[error("`stable {name}` needs the `{class}` class in scope; add `import Wire (..)`")]
    StableNeedsClass { name: String, class: String },
    #[error(
        "rung `{rung}` extends `..{base}`, which is not the rung directly above it in `stable {block}`"
    )]
    RungExtendsNonAdjacent {
        rung: String,
        base: String,
        block: String,
    },
    #[error(
        "new field `{field}` in rung `{rung}` needs a default (`{field} : {field_ty} = <expr>`) so the upgrade can fill it"
    )]
    RungFieldNeedsDefault {
        field: String,
        rung: String,
        field_ty: String,
    },
    #[error(
        "frozen format `{display}` changed shape\n  \
         its committed shape digest no longer matches. A shipped stable version is\n  \
         immutable: add a new rung (`V = {{ ..{rung}, ... }}`) instead of editing `{rung}`.\n  \
         If this rung never shipped, run `prism wire --accept {display}` to reseat it."
    )]
    FrozenShapeChanged { display: String, rung: String },
    #[error(
        "rung `{to}` retypes a field of `{from}`, a type mutation, so `stable {block}` \
         must give a `{dir} {from} -> {to} = ...` converter"
    )]
    RungNeedsConverter {
        to: String,
        from: String,
        block: String,
        dir: String,
    },
    #[error("handler clause for `{op}` exceeds its declared grade `{grade}` ({limit}): {did}")]
    HandlerGradeExceeded {
        op: String,
        grade: String,
        limit: String,
        did: String,
    },
    #[error("op `{op}` has a polymorphic return type and can only be handled by `never`")]
    OpPolymorphicReturn { op: String },
    #[error("never clause cannot resume")]
    NeverClauseResumes,
    #[error("unknown effect operation `{op}` in handler `{handler}`")]
    UnknownHandlerOp { op: String, handler: String },
    #[error(
        "handler `{handler}` mixes operations from effects `{first}` and `{second}`; \
         a named handler must handle a single effect"
    )]
    HandlerMixesEffects {
        handler: String,
        first: String,
        second: String,
    },
    #[error("handler `{handler}` must handle at least one operation")]
    HandlerNoOps { handler: String },
    #[error("handler instance `{handler}` escapes its `with` block: the value here is a function that still performs `{handler}`'s operations after its handler is gone")]
    HandlerEscapes { handler: String },
    #[error("unknown constructor `{ctor}` in `?{ctor}` path step")]
    UnknownPathCtor { ctor: String },
    #[error("`?{ctor}` must be followed by one of its fields")]
    PathCtorNeedsField { ctor: String },
    #[error("`var {var}` escapes its block: the value here is a function that still uses `{var}` after its scope ends")]
    VarEscapes { var: String },
    #[error("view pattern `{name}` cannot be nested inside another pattern")]
    ViewPatternNested { name: String },
    #[error("pattern `{name}` takes {arity} argument(s), {got} given")]
    PatternArity {
        name: String,
        arity: usize,
        got: usize,
    },
    #[error("match through view pattern `{name}` is never exhaustive: add a catchall arm")]
    ViewMatchNotExhaustive { name: String },
    #[error("`with` cannot be the last statement of a block: there is nothing for it to wrap")]
    WithNotLast,
    #[error("handler instance `{name}` is not a value: call its operations as `{name}.op(...)`")]
    InstanceNotValue { name: String },
    #[error("pattern `{name}` is not a value: apply it as `{name}(...)`")]
    PatternNotValue { name: String },
    #[error("`?` is only allowed on a whole statement: write `let x = e?` or `e?`")]
    TryNotWholeStatement,
    #[error("pattern `{name}` has no `make` clause and cannot be used as an expression")]
    PatternNoMake { name: String },
    #[error("handler instance `{instance}` has no operation `{op}`")]
    InstanceNoOp { instance: String, op: String },
    #[error("the base of an indexed assignment must be a variable")]
    IndexAssignBaseNotVar,
    #[error("cannot assign to `{name}`: declare it with `var {name} := ...`")]
    CannotAssign { name: String },
    #[error("`{name}` is not a declared error")]
    NotDeclaredError { name: String },
    #[error("`{name}` carries {arity} value(s), this catch arm binds {got}")]
    CatchArmArity {
        name: String,
        arity: usize,
        got: usize,
    },
    #[error("probe name must match [A-Za-z0-9_.:-]+")]
    InvalidProbeName,
    #[error("usage fact `{fact}` is reserved but not implemented")]
    CoeffectFactUnimplemented { fact: String },
    #[error("`@ noalloc` certifies a function declaration: write it after a `fn`'s return type")]
    CoeffectRowMisplaced,
    #[error("parameter `{param}` is marked `@ once` but may be used more than once in `{fn_name}`; a `@ once` closure must be called or passed at most once, and only directly (not aliased, captured, or reused)")]
    OnceUsedMoreThanOnce { fn_name: String, param: String },
    #[error("a `@ portable` closure cannot capture `{subject}`: only top-level functions, constructors, and portable-typed parameters may be captured, so the closure can move to a fresh runtime")]
    PortableCapturesNonportable { subject: String },
    #[error("`{token}` is marked `@ noescape` and escapes the closure passed to `{callee}`: a scoped value may be used inside the closure but not returned, embedded in returned data, aliased, or captured by another closure")]
    NoescapeTokenEscapes { token: String, callee: String },
    #[error("the `@ noescape` parameter of `{callee}` needs a closure literal or a top-level function, so the no-escape promise can be checked")]
    NoescapeUncheckable { callee: String },
    #[error("`{fn_name}` has no parameter `{param}`")]
    NoParameter { fn_name: String, param: String },
    #[error("argument `{param}` to `{fn_name}` given more than once")]
    ArgGivenTwice { param: String, fn_name: String },
    #[error("positional argument after named argument in call to `{fn_name}`")]
    PositionalAfterNamed { fn_name: String },
    #[error("`{fn_name}` takes {takes} argument(s), more were given")]
    TooManyArgs { fn_name: String, takes: usize },
    #[error("call to `{fn_name}` is missing argument `{param}`")]
    MissingArgument { fn_name: String, param: String },
}

impl ErrKind {
    /// The stable diagnostic code for this error kind. Codes are grouped by
    /// domain (`E1xxx` types, `E2xxx` scope, `E3xxx` classes/instances, `E4xxx`
    /// patterns/matching, `E5xxx` effects/handlers, `E6xxx` declarations); a code
    /// is permanent once assigned, so a diagnostic can be looked up by it.
    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::NotIndexable { .. } => "E1099",
            Self::UnboundVar { .. } => "E2000",
            Self::PolyRecursionMismatch { .. } => "E1000",
            Self::UnknownType { .. } => "E1001",
            Self::OrNullBadElement { .. } => "E1019",
            Self::TooManyTypeArgs { .. } => "E1002",
            Self::KindMismatch { .. } => "E1003",
            Self::ImpredicativeTypeArg { .. } => "E1004",
            Self::IntLiteralOutOfRange { .. } => "E1005",
            Self::UnknownRecordCtor { .. } => "E1006",
            Self::NotRecordCtor { .. } => "E1007",
            Self::MissingFields { .. } => "E1008",
            Self::FieldAccessNonRecord { .. } => "E1009",
            Self::UnboxedUnsupported { .. } => "E1018",
            Self::ConflictingUpdatePaths { .. } => "E1010",
            Self::OpticPathSurvived { .. } => "E1011",
            Self::FieldPathNonRecord { .. } => "E1012",
            Self::UpdatePathMultiCtor { .. } => "E1013",
            Self::NotIndexAssignable { .. } => "E1014",
            Self::NegateUnsigned { .. } => "E1015",
            Self::ArgCountMismatch { .. } => "E1016",
            Self::ApplyNonFunction { .. } => "E1017",
            Self::WhereClauseNeedsAnnotations { .. } => "E3000",
            Self::UnknownClass { .. } => "E3001",
            Self::InstSelectNeedsName { .. } => "E3002",
            Self::ConstraintArgCountMismatch { .. } => "E3003",
            Self::NoClassConstraints { .. } => "E3004",
            Self::AmbiguousConstraint { .. } => "E3005",
            Self::InstanceMethodImpure { .. } => "E3006",
            Self::CyclicInstance { .. } => "E3007",
            Self::InstanceTooDeep { .. } => "E3008",
            Self::UnknownInstance { .. } => "E3009",
            Self::InstanceClassMismatch { .. } => "E3010",
            Self::AmbiguousInstance { .. } => "E3011",
            Self::NoInstance { .. } => "E3012",
            Self::InstanceHeadMismatch { .. } => "E3013",
            Self::CannotInferConstraint { .. } => "E3014",
            Self::CannotDischargeConstraint { .. } => "E3015",
            Self::SuperclassCycle { .. } => "E3016",
            Self::DuplicateClass { .. } => "E3017",
            Self::ClassMethodNotFunction { .. } => "E3018",
            Self::ClassMethodMissingParam { .. } => "E3019",
            Self::ClassMethodClash { .. } => "E3020",
            Self::InstanceNameClash { .. } => "E3021",
            Self::UnknownSuperclass { .. } => "E3022",
            Self::InstanceHeadNotType { .. } => "E3023",
            Self::InstanceHeadArgsNotVars { .. } => "E3024",
            Self::InstanceContextNotHeadVars { .. } => "E3025",
            Self::DuplicateInstanceMethod { .. } => "E3026",
            Self::ClassHasNoMethod { .. } => "E3027",
            Self::InstanceMethodAnnotated { .. } => "E3028",
            Self::MethodArityMismatch { .. } => "E3029",
            Self::InstanceMissingMethods { .. } => "E3030",
            Self::CanonicalHeadNotType { .. } => "E3031",
            Self::NotAnInstance { .. } => "E3032",
            Self::DuplicateCanonical { .. } => "E3033",
            Self::MultipleInstances { .. } => "E3034",
            Self::UnreachableMatchArm { .. } => "E4000",
            Self::NonExhaustiveMatch { .. } => "E4001",
            Self::SuffixedLiteralPattern { .. } => "E4002",
            Self::UnknownRecordConstructor { .. } => "E4003",
            Self::UnknownField { .. } => "E4004",
            Self::UnknownConstructor { .. } => "E4005",
            Self::CtorArity { .. } => "E4006",
            Self::NoFieldOnType { .. } => "E4007",
            Self::EffectArity { .. } => "E5000",
            Self::UnknownEffect { .. } => "E5001",
            Self::KonstNotPure { .. } => "E5002",
            Self::BorrowNotPure { .. } => "E5003",
            Self::UndeclaredEffect { .. } => "E5004",
            Self::UnknownEffectOp { .. } => "E5005",
            Self::EffectInstMismatch { .. } => "E5006",
            Self::UnknownEffectInMask { .. } => "E5007",
            Self::BorrowRowNotClosed { .. } => "E5012",
            Self::DuplicateHandlerArm { .. } => "E5008",
            Self::DuplicateReturnArm => "E5009",
            Self::HandlerArmArity { .. } => "E5010",
            Self::IncompleteHandler { .. } => "E5011",
            Self::DuplicateDecl { .. } => "E6000",
            Self::DefCycle { .. } => "E6001",
            Self::UnknownSynonym { .. } => "E6002",
            Self::UnknownAlias { .. } => "E6003",
            Self::SynonymArity { .. } => "E6004",
            Self::UnknownEffectInAlias { .. } => "E6005",
            Self::ReservedEffectName { .. } => "E6006",
            Self::DuplicateEffectOp { .. } => "E6007",
            Self::PatternClashesCtor { .. } => "E6008",
            Self::ClassPatternHasMake { .. } => "E6009",
            Self::ClassPatternViewNotMethod { .. } => "E6010",
            Self::PatternViewUnknownMethod { .. } => "E6011",
            Self::ViewMethodNotFunction { .. } => "E6012",
            Self::ViewMethodArity { .. } => "E6013",
            Self::PatternForUnknownType { .. } => "E6014",
            Self::PatternClauseNotLambda { .. } => "E6015",
            Self::StableHandWritten { .. } => "E6016",
            Self::UnknownDerivingClass { .. } => "E6017",
            Self::NotDerivable { .. } => "E6018",
            Self::LensNeedsRecord { .. } => "E6019",
            Self::LensNeedsNamedFields { .. } => "E6020",
            Self::StableFieldNotStable { .. } => "E6021",
            Self::EmptyInterpolation { .. } => "E6022",
            Self::StableNeedsClass { .. } => "E6023",
            Self::RungExtendsNonAdjacent { .. } => "E6024",
            Self::RungFieldNeedsDefault { .. } => "E6025",
            Self::FrozenShapeChanged { .. } => "E6026",
            Self::RungNeedsConverter { .. } => "E6027",
            Self::HandlerGradeExceeded { .. } => "E6028",
            Self::OpPolymorphicReturn { .. } => "E6029",
            Self::NeverClauseResumes { .. } => "E6030",
            Self::UnknownHandlerOp { .. } => "E6031",
            Self::HandlerMixesEffects { .. } => "E6032",
            Self::HandlerNoOps { .. } => "E6033",
            Self::HandlerEscapes { .. } => "E6034",
            Self::UnknownPathCtor { .. } => "E6035",
            Self::PathCtorNeedsField { .. } => "E6036",
            Self::VarEscapes { .. } => "E6037",
            Self::ViewPatternNested { .. } => "E6038",
            Self::PatternArity { .. } => "E6039",
            Self::ViewMatchNotExhaustive { .. } => "E6040",
            Self::WithNotLast { .. } => "E6041",
            Self::InstanceNotValue { .. } => "E6042",
            Self::PatternNotValue { .. } => "E6043",
            Self::TryNotWholeStatement { .. } => "E6044",
            Self::PatternNoMake { .. } => "E6045",
            Self::InstanceNoOp { .. } => "E6046",
            Self::IndexAssignBaseNotVar { .. } => "E6047",
            Self::CannotAssign { .. } => "E6048",
            Self::NotDeclaredError { .. } => "E6049",
            Self::CatchArmArity { .. } => "E6050",
            Self::InvalidProbeName { .. } => "E6051",
            Self::CoeffectFactUnimplemented { .. } => "E6052",
            Self::CoeffectRowMisplaced { .. } => "E6053",
            Self::OnceUsedMoreThanOnce { .. } => "E6059",
            Self::PortableCapturesNonportable { .. } => "E6060",
            Self::NoescapeTokenEscapes { .. } => "E6061",
            Self::NoescapeUncheckable { .. } => "E6062",
            Self::NoParameter { .. } => "E6054",
            Self::ArgGivenTwice { .. } => "E6055",
            Self::PositionalAfterNamed { .. } => "E6056",
            Self::TooManyArgs { .. } => "E6057",
            Self::MissingArgument { .. } => "E6058",
        }
    }

    /// The origin label shown in the diagnostic header. Scope-resolution faults
    /// read as "Scope Error"; everything else is a "Type Error".
    #[must_use]
    pub const fn class(&self) -> &'static str {
        match self {
            Self::UnboundVar { .. } => "Scope Error",
            _ => "Type Error",
        }
    }
}

impl TypeError {
    #[must_use]
    pub const fn span(&self) -> Option<&Span> {
        match self {
            Self::UnboundVariable { span, .. }
            | Self::TypeMismatch { span, .. }
            | Self::ScopeFailure { span, .. }
            | Self::TypeFailure { span, .. } => Some(span),
            Self::Kind(diag) => Some(&diag.span),
            Self::InternalInvariant { .. } => None,
        }
    }

    /// The stable diagnostic code, when the error comes from the structured
    /// catalogue ([`ErrKind`]); `None` for the transitional/legacy variants.
    #[must_use]
    pub const fn code(&self) -> Option<&'static str> {
        match self {
            Self::Kind(diag) => Some(diag.kind.code()),
            _ => None,
        }
    }

    /// Stable code for both catalogue and legacy type errors.
    #[must_use]
    pub const fn error_code(&self) -> ErrorCode {
        let spelling = match self {
            Self::UnboundVariable { .. } => code::SCOPE_UNBOUND,
            Self::TypeMismatch { .. } => code::TYPE_MISMATCH_LEGACY,
            Self::ScopeFailure { .. } => code::SCOPE_OTHER_LEGACY,
            Self::Kind(diag) => diag.kind.code(),
            Self::TypeFailure { .. } => code::TYPE_OTHER_LEGACY,
            Self::InternalInvariant { .. } => code::INTERNAL_TYPE,
        };
        let phase = if matches!(self, Self::InternalInvariant { .. }) {
            ErrorPhase::Internal
        } else {
            ErrorPhase::Type
        };
        ErrorCode::new(phase, spelling)
    }

    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::UnboundVariable { .. } | Self::ScopeFailure { .. } => "Scope Error",
            Self::Kind(diag) => diag.kind.class(),
            Self::TypeMismatch { .. } | Self::TypeFailure { .. } => "Type Error",
            Self::InternalInvariant { .. } => "Internal Error",
        }
    }

    #[must_use]
    pub fn in_fn(self, fn_name: &str) -> Self {
        match self {
            // Structured diagnostics carry the context as a real stack frame, so
            // the kind, code, and any labels/help survive the wrapping.
            Self::Kind(mut diag) => {
                diag.context.push(Frame::InFn(fn_name.to_string()));
                Self::Kind(diag)
            }
            Self::InternalInvariant { msg } => Self::InternalInvariant {
                msg: format!("in `{fn_name}`: {msg}"),
            },
            // Legacy string-carrying variants: prepend the context textually until
            // they too move onto the catalogue.
            Self::UnboundVariable { span, .. } | Self::ScopeFailure { span, .. } => {
                Self::ScopeFailure {
                    span,
                    msg: format!("in `{fn_name}`: {self}"),
                }
            }
            Self::TypeMismatch { span, .. } | Self::TypeFailure { span, .. } => Self::TypeFailure {
                span,
                msg: format!("in `{fn_name}`: {self}"),
            },
        }
    }
}

impl Error {
    /// A short origin label for the failure, so diagnostics name their
    /// component ("Scope Error", "Type Error") rather than a bare "Error".
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Lex(_) => "Lexical Error",
            Self::Parse(_) => "Parse Error",
            Self::Type(e) => e.kind(),
            Self::CodegenBackend(_)
            | Self::CodegenDocs(_)
            | Self::CodegenFormat(_)
            | Self::CodegenDump(_)
            | Self::CodegenVerification(_) => "Codegen Error",
            Self::ResolveModule(_)
            | Self::ResolveProject(_)
            | Self::ResolvePackage(_)
            | Self::ResolveLineage(_)
            | Self::ResolveCommand(_) => "Module Error",
            Self::Io(_) => "IO Error",
            Self::RuntimeEvaluation(_) | Self::RuntimeReplay(_) | Self::RuntimeDebugger(_) => {
                "Runtime Error"
            }
            Self::InternalInvariant(_) => "Internal Error",
        }
    }

    /// The byte range in the full source this error points at, if any.
    #[must_use]
    pub fn primary_span(&self) -> Option<Range<usize>> {
        match self {
            Self::Lex(e) => Some(e.offset()..e.offset()),
            Self::Parse(ParseError::Syntax { span, .. }) => Some(span_range(span)),
            Self::Type(e) => e.span().map(span_range),
            _ => None,
        }
    }

    /// Render with ANSI color, for an interactive terminal.
    #[must_use]
    pub fn render(&self, src: &str, name: &str) -> String {
        self.render_with(src, name, true)
    }

    /// Render without color, for captured/piped output (the `report` dump and
    /// snapshot tests) where ANSI escapes would be noise.
    #[must_use]
    pub fn render_plain(&self, src: &str, name: &str) -> String {
        self.render_with(src, name, false)
    }

    fn render_with(&self, src: &str, name: &str, color: bool) -> String {
        let map = SourceMap::new(src);
        let kind = self.kind();
        let code = self.code();
        let mut buf = Vec::<u8>::new();
        let ok = match self {
            Self::Lex(e) => {
                let off = e.offset();
                let msg = format!("{e} at {}", map.at(off));
                write_report(
                    &map,
                    kind,
                    code,
                    name,
                    off..off,
                    &msg,
                    "here",
                    color,
                    &mut buf,
                )
                .is_ok()
            }
            Self::Parse(e) => {
                let (range, label) = match e {
                    ParseError::Syntax { span, .. } => (span_range(span), "here"),
                    ParseError::UnexpectedEof => (src.len()..src.len(), "expected more input here"),
                };
                write_report(
                    &map,
                    kind,
                    code,
                    name,
                    range,
                    &e.to_string(),
                    label,
                    color,
                    &mut buf,
                )
                .is_ok()
            }
            // A structured diagnostic renders its code, secondary spans, help,
            // and notes (the catalogue is the one place carrying them).
            Self::Type(TypeError::Kind(diag)) => {
                write_report_rich(&map, kind, name, diag, color, &mut buf).is_ok()
            }
            Self::Type(e) => {
                let located = match e {
                    TypeError::UnboundVariable { span, name: n } => {
                        Some((span, format!("'{n}' not in scope")))
                    }
                    TypeError::TypeMismatch {
                        span,
                        expected,
                        found,
                    } => Some((span, format!("expected {expected}, got {found}"))),
                    TypeError::ScopeFailure { span, msg }
                    | TypeError::TypeFailure { span, msg } => Some((span, msg.clone())),
                    TypeError::Kind(_) => unreachable!("handled above"),
                    // No span to point at; fall through to the plain message.
                    TypeError::InternalInvariant { .. } => None,
                };
                located.is_some_and(|(span, label)| {
                    write_report(
                        &map,
                        kind,
                        code,
                        name,
                        span_range(span),
                        &e.to_string(),
                        &label,
                        color,
                        &mut buf,
                    )
                    .is_ok()
                })
            }
            _ => false,
        };
        if !ok {
            return format!("{kind}[{code}]: {self}");
        }
        let rendered = String::from_utf8_lossy(&buf).into_owned();
        if color {
            rendered
        } else {
            strip_ansi(&rendered)
        }
    }
}

// Drop CSI escape sequences (`\x1b[ ... m`). ariadne colors the report-kind
// label independently of `Config::with_color`, so the no-color path scrubs the
// residual escapes for stable, pipe-safe output.
fn strip_ansi(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            for d in chars.by_ref() {
                if d.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

const fn span_range(s: &Span) -> Range<usize> {
    s.start..s.end
}

/// Render a non-fatal warning against `src`.
///
/// Produces a yellow source caret when `span` is a non-empty range inside `src`,
/// and a plain `warning: ...` line otherwise (e.g. a warning about a definition
/// in another module, whose span does not index this source). Always ends with a
/// newline.
#[must_use]
pub fn render_warning(src: &str, name: &str, span: &Span, msg: &str, color: bool) -> String {
    let range = span_range(span);
    let plain = || format!("warning: {msg}\n");
    if range.start >= range.end || range.end > src.len() {
        return plain();
    }
    let map = SourceMap::new(src);
    let n = map.prelude;
    let (body, file, at) = if range.start < n {
        (&map.full[..n], "<prelude>", range.start..range.end.min(n))
    } else {
        (map.user(), name, range.start - n..range.end - n)
    };
    let mut buf = Vec::<u8>::new();
    let ok = Report::build(
        ReportKind::Custom("warning", Color::Yellow),
        (file, at.clone()),
    )
    .with_config(Config::default().with_color(color))
    .with_message(msg)
    .with_label(
        Label::new((file, at))
            .with_message("here")
            .with_color(Color::Yellow),
    )
    .finish()
    .write((file, Source::from(body)), &mut buf)
    .is_ok();
    if !ok {
        return plain();
    }
    let rendered = String::from_utf8_lossy(&buf).into_owned();
    if color {
        rendered
    } else {
        strip_ansi(&rendered)
    }
}

#[allow(clippy::too_many_arguments)]
fn write_report(
    map: &SourceMap<'_>,
    kind: &str,
    code: ErrorCode,
    name: &str,
    range: Range<usize>,
    msg: &str,
    label: &str,
    color: bool,
    out: &mut Vec<u8>,
) -> std::io::Result<()> {
    let n = map.prelude;
    let (src, name, range) = if range.start < n {
        (&map.full[..n], "<prelude>", range.start..range.end.min(n))
    } else {
        (map.user(), name, range.start - n..range.end - n)
    };
    // `Config::with_color(false)` suppresses every ANSI escape, so the label
    // hue below is rendered only when `color` is set.
    Report::build(ReportKind::Custom(kind, Color::Red), (name, range.clone()))
        .with_config(Config::default().with_color(color))
        .with_code(code)
        .with_message(msg)
        .with_label(
            Label::new((name, range))
                .with_message(label)
                .with_color(Color::Red),
        )
        .finish()
        .write((name, Source::from(src)), out)
}

// Render a structured [`Diag`]: the code in the header, the primary span, any
// secondary spans (contributing locations), and the help/notes. Best-practice
// diagnostic shape (a code you can look up, blame across several locations, and
// an actionable suggestion), all from the one catalogue entry.
fn write_report_rich(
    map: &SourceMap<'_>,
    kind: &str,
    name: &str,
    diag: &Diag,
    color: bool,
    out: &mut Vec<u8>,
) -> std::io::Result<()> {
    let n = map.prelude;
    let prim = span_range(&diag.span);
    // Labels must all index the same source, so pick the region the primary span
    // falls in and keep only same-region secondaries.
    let in_user = prim.start >= n;
    let (src, sname) = if in_user {
        (map.user(), name)
    } else {
        (&map.full[..n], "<prelude>")
    };
    let adj = |r: &Range<usize>| -> Range<usize> {
        if in_user {
            (r.start - n)..(r.end - n)
        } else {
            r.start..r.end.min(n)
        }
    };
    let msg = diag.to_string();
    let mut report = Report::build(ReportKind::Custom(kind, Color::Red), (sname, adj(&prim)))
        .with_config(Config::default().with_color(color))
        .with_code(diag.kind.code())
        .with_message(&msg)
        .with_label(
            Label::new((sname, adj(&prim)))
                .with_message(&msg)
                .with_color(Color::Red)
                .with_order(0),
        );
    for (i, (lspan, lmsg)) in diag.labels.iter().enumerate() {
        let lr = span_range(lspan);
        let same_region = (lr.start >= n) == in_user;
        if same_region && lr.start < lr.end {
            report = report.with_label(
                Label::new((sname, adj(&lr)))
                    .with_message(lmsg)
                    .with_color(Color::Blue)
                    .with_order(i32::try_from(i).unwrap_or(0) + 1),
            );
        }
    }
    if let Some(help) = &diag.help {
        report = report.with_help(help);
    }
    for note in &diag.notes {
        report = report.with_note(note);
    }
    report.finish().write((sname, Source::from(src)), out)
}

#[cfg(test)]
mod tests {
    use super::SourceMap;
    use crate::driver::{with_custom_prelude, with_prelude};

    // Diagnostics under a custom prelude must be user-relative, exactly like
    // the built-in path: the composed source carries the boundary mark, and
    // SourceMap reads it back. This was silently wrong (offset by the whole
    // custom prelude) before the mark existed.
    #[test]
    fn custom_prelude_positions_are_user_relative() {
        let user_src = "fn main() =\n  oops()\n";
        let full = with_custom_prelude("fn helper() = 1\nfn helper2() = 2", user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        let off = map.prelude_len() + map.user().find("oops").unwrap();
        assert_eq!(map.at(off), "line 2:3");
    }

    // The built-in prelude path is unchanged: located by its known text, no
    // boundary mark involved.
    #[test]
    fn builtin_prelude_positions_are_user_relative() {
        let user_src = "fn main() = 1\n";
        let full = with_prelude(user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        assert_eq!(map.at(map.prelude_len()), "line 1:1");
    }
}
