//! The named failures of the typed-Core judgments.
//!
//! Every way the typed prefix can refuse a term has a variant here. The proof
//! checker in `super::verify` reports these, the builder in `super::build`
//! reports [`BuildError`], and the substitution helpers both share report the
//! leaf errors ([`InstantiationError`], [`RowUnionError`], [`SchemeError`]).
//!
//! Three properties are the point of naming them.
//!
//! A failure is *classifiable*. A caller that wants to know whether a
//! verification failed because a row was too small or because a node was
//! illegal in its phase can match on the variant. Before, that question could
//! only be answered by substring-matching a sentence, which is a contract no
//! compiler should have with itself: renaming a noun in a message silently
//! changed which failures a downstream test believed it was catching.
//!
//! A failure's *operands are typed*. The types, rows, and names a judgment
//! disagreed about are carried as themselves rather than pre-rendered, so the
//! decision about how to show a type to a person is made once, at the boundary,
//! by the same printers the checker's own diagnostics use. That is what stops a
//! `Debug` dump of an internal signature from reaching a user.
//!
//! A failure is *total*. Adding a way to fail means adding a variant, which the
//! `Display` match then forces the author to give a sentence to. A free-form
//! string had no such obligation, so the wording of a new failure was decided
//! in whichever pass happened to introduce it.

use std::fmt;

use prism_common::sym::Sym;

use crate::core::builtins::Builtin;
use crate::core::typed::{CoreFnSig, CoreType, LoweredType};
use crate::core::IoOp;
use crate::types::ty::{EffRow, Label};
use crate::types::Type;

/// The position a judgment was made at.
///
/// This names *where* in a node the checker was looking ("bind binder", "if
/// condition", "operation argument"), and pairs with a [`Violation`] variant
/// naming *what* it found wrong. Almost every position is a fixed label, and
/// the `&'static str` is the constraint on those: a site is a compile-time
/// constant chosen by the checker, never assembled from the program under test,
/// so no operand can be smuggled into a position label where it would escape
/// both typing and the structured rendering. The one position that genuinely
/// varies with the program carries its name as a `Sym`, for the same reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Site {
    /// A fixed position within a node.
    At(&'static str),
    /// The use of a named local binder.
    LocalReference(Sym),
}

impl fmt::Display for Site {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::At(label) => f.write_str(label),
            Self::LocalReference(name) => write!(f, "local reference `{name}`"),
        }
    }
}

impl From<&'static str> for Site {
    fn from(label: &'static str) -> Self {
        Self::At(label)
    }
}

/// Which of the two kinds of Core quantifier a name was bound at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantifierKind {
    /// A type- or natural-kinded variable.
    Type,
    /// An effect-row-kinded variable.
    Row,
}

impl fmt::Display for QuantifierKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Type => "type",
            Self::Row => "row",
        })
    }
}

/// How a counted operand list must relate to the count its witness declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArityRelation {
    /// The two counts must be equal.
    Exact,
    /// The found count must not exceed the declared one.
    AtMost,
}

impl fmt::Display for ArityRelation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Exact => "does not match",
            Self::AtMost => "exceeds",
        })
    }
}

/// The declared count an operand list was measured against, named for the
/// witness it was read from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArityBound {
    /// The enclosing function's parameter list.
    Parameter,
    /// The function's declared signature.
    Signature,
    /// The type witness stored on the node.
    Witness,
    /// The count a declaration fixes (a constructor, an operation).
    Declared,
    /// The count the checked position expects.
    Expected,
    /// The scrutinee a pattern is matched against.
    Scrutinee,
    /// The field capacity of a reuse shell.
    ShellCapacity,
}

impl fmt::Display for ArityBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Parameter => "parameter arity",
            Self::Signature => "signature arity",
            Self::Witness => "witness arity",
            Self::Declared => "declared arity",
            Self::Expected => "expected arity",
            Self::Scrutinee => "scrutinee arity",
            Self::ShellCapacity => "shell capacity",
        })
    }
}

/// The syntactic form a position requires of its operand's type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form {
    /// A suspended computation.
    Thunk,
    /// A callable closure.
    Function,
    /// A mutable cell.
    Reference,
    /// A constructor application or a boxed tuple.
    Allocation,
}

impl fmt::Display for Form {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Thunk => "a thunk",
            Self::Function => "a function",
            Self::Reference => "a reference",
            Self::Allocation => "a constructor or boxed tuple",
        })
    }
}

/// The sort of name a reference failed to resolve to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NameKind {
    /// A data constructor named by a term.
    Constructor,
    /// A data constructor named by a pattern.
    PatternConstructor,
    /// A data constructor named by a representation coercion.
    CoercionConstructor,
    /// A local value reference.
    ValueReference,
    /// An effect operation a handler clause answers.
    HandledOperation,
    /// A top-level function named by a direct call.
    Function,
    /// An effect operation.
    Operation,
}

impl fmt::Display for NameKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Constructor => "unknown constructor",
            Self::PatternConstructor => "pattern names unknown constructor",
            Self::CoercionConstructor => "representation coercion names unknown constructor",
            Self::ValueReference => "unknown value reference",
            Self::HandledOperation => "handler names unknown operation",
            Self::Function => "call targets unknown function",
            Self::Operation => "unknown effect operation",
        })
    }
}

/// How a stored type must relate to the type its position derives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeRelation {
    /// The stored type must equal the expected one.
    Equal,
    /// The stored type may refine the expected one.
    Subtype,
}

/// How a stored effect row must relate to the row its position derives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowRelation {
    /// The stored row must equal the expected one.
    Equal,
    /// The stored row must be contained in the expected one.
    Subrow,
    /// The stored row must contain every derived effect: a node never sheds an
    /// effect it observes.
    Includes,
}

/// A failure of the linear reuse-token discipline.
///
/// A reuse token is the shell of a dead cell, and it must be consumed exactly
/// once on every path that creates it. These are the ways a term can violate
/// that, all of which are unsoundness rather than a typing disagreement: a
/// token consumed twice writes two constructors into one cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReuseFault {
    /// A token was mentioned somewhere other than the reuse operand it belongs
    /// to, so a use could outlive the shell.
    Escapes(Sym),
    /// Some path through the body leaves the token unconsumed.
    NotConsumedOnce(Sym),
    /// One path consumes the token twice.
    ConsumedTwice(Sym),
    /// The name is bound, but not to a token that is live here.
    NotActive(Sym),
    /// The name is not bound at this point at all.
    OutOfScope(Sym),
    /// A closure captured an enclosing token, which would let the shell be
    /// consumed once per invocation.
    CapturesToken(Site),
    /// A closure frees an enclosing shell, so the shell's lifetime is no longer
    /// the activation's.
    FreesShell(Site),
    /// Two arms of a branch leave different numbers of tokens live, so the join
    /// has no single credit.
    UnequalCredits(Site),
    /// A rebuild's payload is not something a shell can hold.
    RebuildIsNotAllocation,
    /// A `with-reuse` frees a value that is not the case scrutinee whose shell
    /// is live here.
    ScrutineeNotActive,
    /// The live scrutinee's shell was already freed on this path.
    ScrutineeFreedTwice,
}

impl fmt::Display for ReuseFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Escapes(name) => {
                write!(f, "reuse token {name} escapes its dedicated reuse operand")
            }
            Self::NotConsumedOnce(name) => write!(
                f,
                "reuse token {name} is not consumed exactly once on every path"
            ),
            Self::ConsumedTwice(name) => {
                write!(
                    f,
                    "reuse token {name} is consumed more than once on one path"
                )
            }
            Self::NotActive(name) => write!(f, "{name} is not an active reuse token"),
            Self::OutOfScope(name) => write!(f, "reuse token {name} is out of scope"),
            Self::CapturesToken(site) => {
                write!(f, "{site} consumes an enclosing reuse token")
            }
            Self::FreesShell(site) => write!(f, "{site} frees an enclosing reuse shell"),
            Self::UnequalCredits(site) => {
                write!(f, "{site} consume different reuse-token credits")
            }
            Self::RebuildIsNotAllocation => {
                write!(f, "reuse rebuild is not a constructor or boxed tuple")
            }
            Self::ScrutineeNotActive => write!(
                f,
                "with-reuse does not free the active boxed case scrutinee"
            ),
            Self::ScrutineeFreedTwice => write!(
                f,
                "the active boxed case scrutinee is freed more than once on one path"
            ),
        }
    }
}

/// A reference-count operation acting on a value that cannot be counted.
///
/// `dup`/`drop` (and the cell a `with-reuse` frees) may act on any value that
/// is one runtime word at run time; the layout authority decides that from the
/// operand's type. These are the operand shapes it refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcOperandFault {
    /// The operand is a linear reuse token, which the count never touches.
    ReuseToken,
    /// The operand's source type has no runtime value representation at all
    /// (an effect row or a type-level natural).
    NotAValue,
}

impl fmt::Display for RcOperandFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReuseToken => write!(f, "RC operation acts on a linear reuse token"),
            Self::NotAValue => write!(
                f,
                "RC operation acts on a type with no runtime value representation"
            ),
        }
    }
}

/// A failure of the erased-RC-sequencing discipline.
///
/// After reference counting runs, a `dup`/`drop` pair is sequenced through a
/// binder with a reserved identity, and erasure recognises that identity to
/// drop the bind. These are the ways that agreement can be broken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcSequenceFault {
    /// The reserved witness appeared on a bind that is not administrative.
    OutsideAdministrativeBind,
    /// The reserved identity was used without the witness erasure depends on.
    MissingErasureWitness,
    /// The witness carries an identity other than the reserved one.
    WrongReservedIdentity,
    /// The witness sequences something other than a `dup` or a `drop`.
    NotADupOrDrop,
    /// The operation acts on a value that reads no binding.
    OperandIsNotAReference,
}

impl fmt::Display for RcSequenceFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutsideAdministrativeBind => write!(
                f,
                "RC sequence witness used outside an administrative dup/drop bind"
            ),
            Self::MissingErasureWitness => {
                write!(f, "reserved RC sequence identity lacks its erasure witness")
            }
            Self::WrongReservedIdentity => {
                write!(f, "RC sequence witness has the wrong reserved identity")
            }
            Self::NotADupOrDrop => {
                write!(f, "RC sequence witness does not sequence a dup or drop")
            }
            Self::OperandIsNotAReference => {
                write!(f, "RC operation acts on a value that reads no binding")
            }
        }
    }
}

/// A scheme did not peel down to the function type an operation required.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemeError {
    /// What the scheme's quantifier prefix bottomed out in.
    pub found: Type,
}

impl fmt::Display for SchemeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "expected a function scheme, got {}", self.found.show())
    }
}

impl std::error::Error for SchemeError {}

/// Explicit instantiation arguments did not match the scheme they instantiate.
///
/// Typed Core never searches for an instantiation: a polymorphic use site
/// carries its arguments, and the checker substitutes and compares. So these
/// are the only two ways instantiation can fail, and both are structural.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstantiationError {
    /// The scheme is not a function scheme, so it quantifies nothing to apply.
    Scheme(SchemeError),
    /// The argument list and the quantifier prefix differ in length.
    Count {
        /// Arguments supplied at the use site.
        found: usize,
        /// Quantifiers the scheme declares.
        quantifiers: usize,
    },
    /// An argument is of the other kind than the quantifier it fills.
    Kind {
        /// Position in the argument list.
        index: usize,
        /// The kind the quantifier at that position demands.
        expected: QuantifierKind,
    },
}

impl fmt::Display for InstantiationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Scheme(error) => write!(f, "{error}"),
            Self::Count { found, quantifiers } => write!(
                f,
                "argument count {found} does not match quantifier count {quantifiers}"
            ),
            Self::Kind { index, expected } => {
                write!(f, "argument {index} is not a {expected} argument")
            }
        }
    }
}

impl std::error::Error for InstantiationError {}

impl From<SchemeError> for InstantiationError {
    fn from(error: SchemeError) -> Self {
        Self::Scheme(error)
    }
}

/// Two effect rows have no join the checker can prove.
///
/// A row union is not a set union: two rows with distinct open tails have a
/// join only if one of the unknown remainders is known to contain the other,
/// and nothing here knows that. The same holds for one effect label carried at
/// two different argument lists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowUnionError {
    /// The two rows end in distinct open tails.
    OpenTails {
        /// The left row's tail.
        left: EffRow,
        /// The right row's tail.
        right: EffRow,
    },
    /// One effect name occurs on both sides at incompatible arguments.
    Labels {
        /// The occurrence already absorbed.
        left: Label,
        /// The occurrence that could not join it.
        right: Label,
    },
}

impl fmt::Display for RowUnionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpenTails { left, right } => write!(
                f,
                "cannot prove union of distinct open tails {} and {}",
                left.show(),
                right.show()
            ),
            Self::Labels { left, right } => write!(
                f,
                "cannot prove union of effect labels {} and {}",
                left.show(),
                right.show()
            ),
        }
    }
}

impl std::error::Error for RowUnionError {}

/// What a polymorphic use site was instantiating.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstantiationSubject {
    /// A reference to a local binder, named.
    Local(Sym),
    /// A fixed position in a node.
    At(Site),
}

impl fmt::Display for InstantiationSubject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(name) => write!(f, "local {name}"),
            Self::At(site) => write!(f, "{site}"),
        }
    }
}

/// One failed typed-Core judgment, named.
///
/// The variants are grouped by the invariant they belong to rather than by the
/// node that happened to detect them, so that a family (arity, rows, the reuse
/// discipline, phase legality) can be recognised without reading prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Violation {
    /// One name is bound twice in a single quantifier prefix.
    DuplicateQuantifier {
        /// Which kind of quantifier bound it.
        kind: QuantifierKind,
        /// Whether the prefix is an inner (rank-N) one rather than the
        /// declaration's own.
        nested: bool,
        /// The name bound twice.
        name: Sym,
    },
    /// One binder identity is introduced twice in one binding group, so a
    /// reference to it has no unique referent.
    DuplicateBinder {
        /// The duplicated identity.
        name: Sym,
    },
    /// Two functions in the program share one global identity, so a call has no
    /// unique callee.
    DuplicateGlobal,
    /// A record term names a field the witness does not name at that position.
    RecordField {
        /// The name the term carries.
        found: Sym,
        /// The name the witness fixes.
        expected: Sym,
    },
    /// A counted operand list disagrees with the count its witness declares.
    Arity {
        /// What was counted.
        counted: Site,
        /// How the counts must relate.
        relation: ArityRelation,
        /// The witness the declared count was read from.
        bound: ArityBound,
        /// The count found.
        found: usize,
        /// The count declared.
        expected: usize,
    },
    /// A newtype constructor is not the single-field constructor a
    /// representation coercion requires.
    NewtypeFieldCount {
        /// The constructor named by the coercion.
        constructor: Sym,
        /// How many fields it actually declares.
        found: usize,
    },
    /// A stored type disagrees with the type its position derives.
    TypeMismatch {
        /// Where the judgment was made.
        site: Site,
        /// How the two must relate.
        relation: TypeRelation,
        /// The type stored on the node.
        actual: CoreType,
        /// The type the position derives.
        expected: CoreType,
    },
    /// A stored effect row disagrees with the row its position derives.
    RowMismatch {
        /// Where the judgment was made.
        site: Site,
        /// How the two must relate.
        relation: RowRelation,
        /// The row stored on the node.
        actual: EffRow,
        /// The row the position derives.
        expected: EffRow,
    },
    /// An operand's type is not the form its position requires.
    NotAForm {
        /// The operand position.
        site: Site,
        /// The form required.
        expected: Form,
        /// The type found instead.
        found: CoreType,
    },
    /// A literal's stored witness is not one this literal can carry.
    LiteralWitness {
        /// The literal form.
        site: Site,
        /// The witness stored on it.
        witness: CoreType,
    },
    /// A reference resolves to neither a local binder nor a global.
    UnboundReference {
        /// The unresolved name.
        name: Sym,
    },
    /// A name does not resolve in the declaration environment.
    UnknownName {
        /// The sort of name, which also fixes how the failure reads.
        kind: NameKind,
        /// The unresolved name.
        name: Sym,
    },
    /// An elaborator-only builtin reached the checker with no signature to
    /// check it against.
    MissingBuiltinSignature {
        /// The builtin's name.
        builtin: Sym,
    },
    /// A constructor occurrence carries a tag other than the one its
    /// declaration fixes, so the runtime match would take a different arm.
    ConstructorTag {
        /// The constructor.
        name: Sym,
        /// The tag stored at the occurrence.
        found: usize,
        /// The tag the declaration fixes.
        declared: usize,
    },
    /// A product term's shape does not match the product its witness names.
    ProductShape {
        /// The witness stored on the term.
        witness: CoreType,
    },
    /// A runtime cell slot holds a type whose boundary layout is not exactly
    /// one GC-scanned word.
    ///
    /// Constructor fields, boxed tuple fields, and closure captures each occupy
    /// one word of a heap cell: allocation sizes, field offsets, and reuse
    /// capacities are all computed as plain field counts on that assumption. A
    /// slot type that widens, vanishes, or admits a non-value bit pattern would
    /// silently corrupt every one of those computations, so it is rejected
    /// here, where the type is still attached to the slot.
    CellSlotNotOneWord {
        /// The slot position.
        site: Site,
        /// The slot's type.
        ty: CoreType,
    },
    /// An unboxed record term carries a witness that is not a record type.
    UnboxedRecordWitness {
        /// The witness stored on the term.
        witness: CoreType,
    },
    /// An error node's payload has a witness the error representation cannot
    /// carry.
    ErrorArgumentWitness {
        /// The witness stored on the payload.
        witness: CoreType,
    },
    /// A field projection names a field the operand's record does not have.
    AbsentField {
        /// The projected field.
        field: Sym,
        /// The operand's record type.
        operand: CoreType,
    },
    /// An integer-lane comparison was given operands that are not both in that
    /// lane, so the primitive has no meaning at these types.
    LaneOperands {
        /// The left operand's type.
        lhs: CoreType,
        /// The right operand's type.
        rhs: CoreType,
    },
    /// A tuple pattern was matched against a scrutinee that is not a product.
    TuplePatternScrutinee {
        /// The scrutinee's type.
        scrutinee: CoreType,
    },
    /// A case has no arms, so it denotes no computation.
    CaseHasNoArms,
    /// An `init-at` appears with no allocation for it to initialise.
    InitAtWithoutAlloc,
    /// An `init-at` payload is not something a cell can hold.
    InitAtPayloadIsNotAllocation,
    /// A handler declares one half of its return clause.
    HandlerReturnClauseIncomplete,
    /// The forwarding a handler stores is not the forwarding its arms derive,
    /// so an operation would be forwarded that the handler discharges (or the
    /// reverse).
    ForwardingMismatch {
        /// The forwarding the arms derive.
        derived: Vec<(Sym, Label)>,
        /// The forwarding stored on the handler.
        stored: Vec<(Sym, Label)>,
    },
    /// A handler's stored residual row does not cover what its body leaves
    /// undischarged together with what its clauses perform.
    HandlerResidualRow {
        /// The residual the handler derives.
        derived: EffRow,
        /// The upper bound the handler stores.
        stored: EffRow,
    },
    /// A representation coercion names a constructor that is not a newtype, so
    /// there is no representation identity to appeal to.
    NotANewtype {
        /// The constructor named.
        constructor: Sym,
    },
    /// A representation-preserving coercion relates two types with different
    /// representations.
    ReprCoercionIllegal {
        /// The operand's type.
        from: CoreType,
        /// The result's type.
        to: CoreType,
    },
    /// A lowered-representation conversion relates two types the effect-runtime
    /// ABI does not identify.
    ReprConversionIllegal {
        /// The operand's type.
        from: CoreType,
        /// The result's type.
        to: CoreType,
    },
    /// A newtype coercion's operand and result do not stand at the two ends of
    /// the constructor it names.
    NewtypeCoercionDisconnected {
        /// The constructor named.
        constructor: Sym,
        /// The constructor's single field type.
        field: CoreType,
        /// The constructor's result type.
        result: CoreType,
        /// The operand's type.
        inner: CoreType,
        /// The result's type.
        outer: CoreType,
    },
    /// A node or witness appears in a phase whose Core does not admit it.
    ///
    /// This is what keeps the phases genuinely distinct: each typed pass runs
    /// the same checker at a different phase marker, and a node the phase
    /// forbids is rejected there rather than surviving to a backend that cannot
    /// lower it.
    PhaseIllegal {
        /// The node or witness form.
        what: Site,
        /// The phase that forbids it.
        phase: &'static str,
    },
    /// A failure of the linear reuse-token discipline.
    Reuse(ReuseFault),
    /// A failure of the erased-RC-sequencing discipline.
    RcSequence(RcSequenceFault),
    /// A reference-count operation acting on a value that cannot be counted.
    RcOperand(RcOperandFault),
    /// A polymorphic use site's explicit instantiation does not fit its scheme.
    Instantiation {
        /// What was being instantiated.
        subject: InstantiationSubject,
        /// Why it did not fit.
        error: InstantiationError,
    },
    /// A signature the checker holds for a builtin does not peel down to a
    /// function type.
    CanonicalSignature {
        /// The registry the signature came from.
        site: Site,
        /// Why it did not peel down.
        error: SchemeError,
    },
    /// A signature the checker holds for a builtin does not parse.
    ///
    /// The parse error is rendered here rather than carried: it is a foreign
    /// diagnostic type with no value semantics, and this is the one boundary a
    /// violation crosses to reach it.
    CanonicalSignatureParse {
        /// The registry the signature came from.
        site: Site,
        /// The rendered parse failure.
        error: String,
    },
    /// Two rows a node must join have no provable union.
    RowUnion {
        /// The position whose row is the join.
        site: Site,
        /// Why the join is not provable.
        error: RowUnionError,
    },
    /// Metavariables survive into a type that must be ground by now.
    UnsolvedMeta {
        /// Which kind of metavariable survived.
        kind: QuantifierKind,
        /// The type they survive in.
        ty: Type,
    },
    /// Metavariables survive into an effect row that must be ground by now.
    UnsolvedRowMeta {
        /// The row they survive in.
        row: EffRow,
    },
    /// A type mentions a rigid variable no enclosing quantifier binds.
    UnboundRigid {
        /// Which kind of variable.
        kind: QuantifierKind,
        /// The unbound name.
        name: Sym,
        /// The type mentioning it.
        ty: Type,
    },
    /// An effect row mentions a rigid tail variable no enclosing quantifier
    /// binds.
    UnboundRigidRow {
        /// The unbound name.
        name: Sym,
    },
    /// An effect row is not in the canonical form every comparison assumes.
    ///
    /// Rows are compared structurally, so a row that duplicates a label or
    /// orders one differently would compare unequal to a row denoting the same
    /// effects, and the checker would reject a valid program.
    RowNotCanonical {
        /// The row as stored.
        row: EffRow,
    },
    /// A lowered ABI type appears in a phase before the ABI exists.
    LoweredAbiIllegal {
        /// The phase that forbids it.
        phase: &'static str,
        /// The ABI type found.
        found: LoweredType,
    },
}

impl fmt::Display for Violation {
    #[allow(clippy::too_many_lines)] // One arm per variant; splitting hides the total.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateQuantifier { kind, nested, name } => {
                let nested = if *nested { "nested " } else { "" };
                write!(f, "duplicate {nested}{kind} quantifier {name}")
            }
            Self::DuplicateBinder { name } => {
                write!(
                    f,
                    "binder identity {name} is duplicated in one binding group"
                )
            }
            Self::DuplicateGlobal => f.write_str("duplicate global function identity"),
            Self::RecordField { found, expected } => write!(
                f,
                "record field {found} does not match witness field {expected}"
            ),
            Self::Arity {
                counted,
                relation,
                bound,
                found,
                expected,
            } => write!(f, "{counted} arity {found} {relation} {bound} {expected}"),
            Self::NewtypeFieldCount { constructor, found } => write!(
                f,
                "newtype constructor {constructor} has {found} fields rather than one"
            ),
            Self::TypeMismatch {
                site,
                relation,
                actual,
                expected,
            } => {
                let relation = match relation {
                    TypeRelation::Equal => "expected",
                    TypeRelation::Subtype => "expected a subtype of",
                };
                write!(
                    f,
                    "{site} type mismatch: stored {actual}, {relation} {expected}"
                )
            }
            Self::RowMismatch {
                site,
                relation,
                actual,
                expected,
            } => {
                let actual = actual.show();
                let expected = expected.show();
                match relation {
                    RowRelation::Equal => {
                        write!(
                            f,
                            "{site} row mismatch: stored {actual}, expected {expected}"
                        )
                    }
                    RowRelation::Subrow => write!(
                        f,
                        "{site} row mismatch: stored {actual}, expected a subrow of {expected}"
                    ),
                    RowRelation::Includes => write!(
                        f,
                        "{site} row mismatch: stored {actual}, does not include derived {expected}"
                    ),
                }
            }
            Self::NotAForm {
                site,
                expected,
                found,
            } => write!(f, "{site} is not {expected}: {found}"),
            Self::LiteralWitness { site, witness } => {
                write!(f, "{site} has witness {witness}")
            }
            Self::UnboundReference { name } => {
                write!(f, "reference {name} is neither local nor global")
            }
            Self::UnknownName { kind, name } => write!(f, "{kind} {name}"),
            Self::MissingBuiltinSignature { builtin } => write!(
                f,
                "elaborator-only builtin {builtin} has no verifier signature override"
            ),
            Self::ConstructorTag {
                name,
                found,
                declared,
            } => write!(
                f,
                "constructor {name} tag {found} does not match declared tag {declared}"
            ),
            Self::ProductShape { witness } => {
                write!(f, "product shape does not match witness {witness}")
            }
            Self::CellSlotNotOneWord { site, ty } => {
                write!(f, "{site} of type {ty} is not one runtime word")
            }
            Self::UnboxedRecordWitness { witness } => {
                write!(f, "unboxed record has non-record witness {witness}")
            }
            Self::ErrorArgumentWitness { witness } => {
                write!(f, "error argument has unsupported witness {witness}")
            }
            Self::AbsentField { field, operand } => write!(
                f,
                "field {field} is absent from unboxed-record operand {operand}"
            ),
            Self::LaneOperands { lhs, rhs } => {
                write!(f, "integer-lane comparison has operands {lhs} and {rhs}")
            }
            Self::TuplePatternScrutinee { scrutinee } => {
                write!(f, "tuple pattern has non-product scrutinee {scrutinee}")
            }
            Self::CaseHasNoArms => write!(f, "case has no arms"),
            Self::InitAtWithoutAlloc => {
                write!(f, "init-at without a declared alloc operation")
            }
            Self::InitAtPayloadIsNotAllocation => {
                write!(f, "init-at payload is not a constructor or boxed tuple")
            }
            Self::HandlerReturnClauseIncomplete => write!(
                f,
                "handler return binder and return body must appear together"
            ),
            Self::ForwardingMismatch { derived, stored } => write!(
                f,
                "handler residual-forwarding witness mismatch: derived {}, stored {}",
                show_forwarding(derived),
                show_forwarding(stored)
            ),
            Self::HandlerResidualRow { derived, stored } => write!(
                f,
                "handler residual effects row mismatch: derived {}, stored upper bound {}",
                derived.show(),
                stored.show()
            ),
            Self::NotANewtype { constructor } => write!(
                f,
                "representation coercion names non-newtype constructor {constructor}"
            ),
            Self::ReprCoercionIllegal { from, to } => write!(
                f,
                "illegal representation-preserving coercion {from} to {to}"
            ),
            Self::ReprConversionIllegal { from, to } => write!(
                f,
                "illegal lowered representation conversion {from} to {to}"
            ),
            Self::NewtypeCoercionDisconnected {
                constructor,
                field,
                result,
                inner,
                outer,
            } => write!(
                f,
                "newtype representation coercion for {constructor} does not connect field {field} \
                 and result {result}: inner {inner}, outer {outer}"
            ),
            Self::PhaseIllegal { what, phase } => {
                write!(f, "{what} is illegal in {phase} Core")
            }
            Self::Reuse(fault) => write!(f, "{fault}"),
            Self::RcSequence(fault) => write!(f, "{fault}"),
            Self::RcOperand(fault) => write!(f, "{fault}"),
            Self::Instantiation { subject, error } => {
                write!(f, "invalid {subject} instantiation: {error}")
            }
            Self::CanonicalSignature { site, error } => {
                write!(f, "invalid canonical {site} signature: {error}")
            }
            Self::CanonicalSignatureParse { site, error } => {
                write!(f, "cannot parse canonical {site} signature: {error}")
            }
            Self::RowUnion { site, error } => write!(f, "{site}: {error}"),
            Self::UnsolvedMeta { kind, ty } => {
                write!(f, "unsolved {kind} metavariables survive in {}", ty.show())
            }
            Self::UnsolvedRowMeta { row } => write!(
                f,
                "unsolved effect-row metavariables survive in {}",
                row.show()
            ),
            Self::UnboundRigid { kind, name, ty } => {
                write!(f, "unbound rigid {kind} variable {name} in {}", ty.show())
            }
            Self::UnboundRigidRow { name } => {
                write!(f, "unbound rigid effect-row variable {name}")
            }
            Self::RowNotCanonical { row } => {
                write!(f, "effect row is not canonical: {}", row.show())
            }
            Self::LoweredAbiIllegal { phase, found } => {
                write!(f, "lowered ABI type {found} is illegal in {phase} Core")
            }
        }
    }
}

/// The nouns the solver's failed judgments are phrased over. One home, because
/// the same noun appears under several relations and a second spelling of it
/// would read as a second kind of witness.
const CORE_TYPE: &str = "Core type";
const SOURCE_TYPE: &str = "source type";
const FUNCTION_SIGNATURE: &str = "function signature";
const EFFECT_ROW: &str = "effect row";
const EFFECT_ROW_TAIL: &str = "effect-row tail";
const EFFECT_LABEL: &str = "effect label";

/// The judgment the Core solver was making when two witnesses disagreed.
///
/// The solver relates witnesses in exactly these four ways, and which one was
/// being made is what decides whether a failure is a genuine disagreement or
/// merely a direction the checker cannot prove.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveRelation {
    /// The two witnesses must be made equal.
    Unify,
    /// The left witness must refine the right one.
    Subtype,
    /// The left row's effects must all appear in the right row.
    Subrow,
    /// The two witnesses must have a least upper bound.
    Join,
}

impl SolveRelation {
    /// Phrase this relation over one noun and the two operands it related.
    fn describe(
        self,
        f: &mut fmt::Formatter<'_>,
        noun: &str,
        left: &dyn fmt::Display,
        right: &dyn fmt::Display,
    ) -> fmt::Result {
        match self {
            Self::Unify => write!(f, "cannot unify {noun}s {left} and {right}"),
            Self::Join => write!(f, "cannot join {noun}s {left} and {right}"),
            Self::Subtype => write!(f, "{noun} {left} is not a subtype of {right}"),
            Self::Subrow => write!(f, "{noun} {left} is not included in {right}"),
        }
    }
}

/// Which substitution table a metavariable belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetaKind {
    /// A placeholder for a CBPV shape with no source-language spelling.
    Core,
    /// A placeholder for a source type.
    Source,
    /// A placeholder for an effect row.
    Row,
}

/// One solver metavariable, named the way the solver's tables name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MetaVar {
    /// The table it lives in.
    pub kind: MetaKind,
    /// Its identity within that table.
    pub id: u32,
}

impl fmt::Display for MetaVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let id = self.id;
        match self.kind {
            MetaKind::Core => write!(f, "Core metavariable ?{id}"),
            MetaKind::Source => write!(f, "type metavariable ?{id}"),
            MetaKind::Row => write!(f, "row metavariable ?r{id}"),
        }
    }
}

/// The witness a metavariable was about to be bound to when it was found to
/// contain that same variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Within {
    /// A Core type reached by unification.
    Core(CoreType),
    /// A Core type reached by joining two lower bounds.
    Joined(CoreType),
    /// A source type.
    Source(Type),
    /// An effect row.
    Row(EffRow),
}

impl fmt::Display for Within {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(ty) => write!(f, "{ty}"),
            Self::Joined(ty) => write!(f, "joined type {ty}"),
            Self::Source(ty) => f.write_str(&ty.show()),
            Self::Row(row) => f.write_str(&row.show()),
        }
    }
}

/// A failure of the Core solver: two witnesses that could not be related.
///
/// The solver runs under the builder rather than over the source language, so
/// none of these is a user-facing type error. Each one says that reconstructed
/// evidence disagreed with declared evidence, which is a compiler fault, and
/// naming them is what lets the fault be classified without reading its prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveError {
    /// A metavariable would have to be bound to a witness containing itself.
    Occurs {
        /// The variable being solved.
        meta: MetaVar,
        /// The witness it occurs in.
        within: Within,
    },
    /// Two Core types do not stand in the required relation.
    Core {
        /// The judgment that failed.
        relation: SolveRelation,
        /// The two operands, left and right.
        operands: Box<(CoreType, CoreType)>,
    },
    /// Two source types cannot be unified.
    Source {
        /// The two operands, left and right.
        operands: Box<(Type, Type)>,
    },
    /// Two calling conventions do not stand in the required relation.
    Signature {
        /// The judgment that failed.
        relation: SolveRelation,
        /// The two operands, left and right.
        operands: Box<(CoreFnSig, CoreFnSig)>,
    },
    /// Two effect rows do not stand in the required relation.
    Row {
        /// The judgment that failed.
        relation: SolveRelation,
        /// The left operand.
        left: EffRow,
        /// The right operand.
        right: EffRow,
    },
    /// Two rows end in open tails that cannot be identified.
    RowTails {
        /// The left tail.
        left: EffRow,
        /// The right tail.
        right: EffRow,
    },
    /// An effect performed on the left is absent from the row on the right.
    LabelNotIncluded {
        /// The effect that has nowhere to go.
        label: Label,
        /// The row that does not carry it.
        row: EffRow,
    },
    /// Two rows have no join the checker can prove.
    Union(RowUnionError),
    /// Two unboxed records disagree on a field name at the same position.
    RecordField {
        /// The left field name.
        left: Sym,
        /// The right field name.
        right: Sym,
    },
    /// A join widened past the type its position had already fixed.
    JoinExceeds {
        /// The least upper bound of the observed lower bounds, and the type the
        /// position expects.
        operands: Box<(CoreType, CoreType)>,
    },
    /// A failure found under a named position of a compound witness.
    In {
        /// Where in the compound the operands were taken from.
        site: Site,
        /// What went wrong there.
        error: Box<Self>,
    },
}

impl SolveError {
    /// Record that this failure was found under `site` of a compound witness.
    #[must_use]
    pub fn at(self, site: impl Into<Site>) -> Self {
        Self::In {
            site: site.into(),
            error: Box::new(self),
        }
    }
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Occurs { meta, within } => write!(f, "recursive {meta} in {within}"),
            Self::Core { relation, operands } => {
                relation.describe(f, CORE_TYPE, &operands.0, &operands.1)
            }
            Self::Source { operands } => SolveRelation::Unify.describe(
                f,
                SOURCE_TYPE,
                &operands.0.show(),
                &operands.1.show(),
            ),
            Self::Signature { relation, operands } => {
                relation.describe(f, FUNCTION_SIGNATURE, &operands.0, &operands.1)
            }
            Self::Row {
                relation,
                left,
                right,
            } => relation.describe(f, EFFECT_ROW, &left.show(), &right.show()),
            Self::RowTails { left, right } => {
                SolveRelation::Unify.describe(f, EFFECT_ROW_TAIL, &left.show(), &right.show())
            }
            Self::LabelNotIncluded { label, row } => {
                SolveRelation::Subrow.describe(f, EFFECT_LABEL, &label.show(), &row.show())
            }
            Self::Union(error) => write!(f, "{error}"),
            Self::RecordField { left, right } => {
                write!(f, "record field mismatch {left} and {right}")
            }
            Self::JoinExceeds { operands } => write!(
                f,
                "joined result {} exceeds expected type {}",
                operands.0, operands.1
            ),
            Self::In { site, error } => write!(f, "{site}: {error}"),
        }
    }
}

impl std::error::Error for SolveError {}

impl From<RowUnionError> for SolveError {
    fn from(error: RowUnionError) -> Self {
        Self::Union(error)
    }
}

/// Which part of a `Bind` a failure was found under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindPart {
    /// The bound computation.
    First,
    /// The continuation.
    Rest,
    /// The continuation, checked against the exact expected signature rather
    /// than a relaxed one.
    ExactRest,
}

impl fmt::Display for BindPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::First => "first",
            Self::Rest => "rest",
            Self::ExactRest => "exact rest",
        })
    }
}

/// The position a builder failure was found under.
///
/// This is the builder's analogue of [`Site`], widened because reconstructing a
/// witness fails inside a term rather than at a fixed slot of a node: the
/// positions that matter carry the binder, the argument index, or the rows a
/// handler derived, and those are what make a report locatable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuildContext {
    /// A fixed position within a node.
    At(Site),
    /// One half of a sequencing node, named by its binder.
    Binding {
        /// The name bound.
        binder: Sym,
        /// Which half.
        part: BindPart,
    },
    /// One argument of a computed application.
    Argument {
        /// Position in the argument list.
        index: usize,
        /// The parameter type it was checked against.
        expected: CoreType,
    },
    /// The body of one handler clause.
    HandlerOperationBody(Sym),
    /// A handler's derived row against the row its position expects.
    HandlerEffects {
        /// The row the handler's own clauses derived.
        derived: EffRow,
        /// The row the enclosing position fixes, if it fixes one.
        expected: Option<EffRow>,
    },
}

impl fmt::Display for BuildContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::At(site) => write!(f, "{site}"),
            Self::Binding { binder, part } => write!(f, "bind {binder} {part}"),
            Self::Argument { index, expected } => {
                write!(
                    f,
                    "computed application argument {index} against {expected}"
                )
            }
            Self::HandlerOperationBody(name) => write!(f, "handler operation {name} body"),
            Self::HandlerEffects { derived, expected } => {
                let expected = expected
                    .as_ref()
                    .map_or_else(|| "an unconstrained row".to_string(), EffRow::show);
                write!(
                    f,
                    "handler effects derived {}, expected {expected}",
                    derived.show()
                )
            }
        }
    }
}

impl From<&'static str> for BuildContext {
    fn from(label: &'static str) -> Self {
        Self::At(Site::At(label))
    }
}

/// What a miscounted operand list belonged to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildSubject {
    /// A data constructor, named.
    Constructor(Sym),
    /// An application whose callee is a value rather than a known function.
    ComputedApplication,
    /// A direct call to a top-level function, named.
    Call(Sym),
    /// A builtin I/O operation.
    Io(IoOp),
    /// A compiler builtin.
    Builtin(Builtin),
    /// An effect operation, named.
    Operation(Sym),
    /// A constructor pattern, named.
    Pattern(Sym),
    /// A handler clause answering an operation, named.
    HandlerOperation(Sym),
}

impl fmt::Display for BuildSubject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constructor(name) => write!(f, "constructor {name}"),
            Self::ComputedApplication => f.write_str("computed application"),
            Self::Call(name) => write!(f, "call {name}"),
            Self::Io(op) => write!(f, "I/O {}", op.kind()),
            Self::Builtin(builtin) => write!(f, "builtin {}", builtin.name()),
            Self::Operation(name) => write!(f, "operation {name}"),
            Self::Pattern(name) => write!(f, "pattern {name}"),
            Self::HandlerOperation(name) => write!(f, "handler operation {name}"),
        }
    }
}

/// A failure to reconstruct a typed witness at the elaboration boundary.
///
/// The builder is not an inference pass: every witness it needs is already
/// determined by a checked declaration, so each of these says that the Core the
/// elaborator produced and the schemes the checker recorded describe different
/// programs. That is always a compiler fault, never a user's type error, and
/// naming the faults is what keeps them distinguishable once they are wrapped
/// into a construction failure and rendered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// The solver could not relate two witnesses.
    Solve(Box<SolveError>),
    /// A declared scheme is not a function scheme.
    Scheme(SchemeError),
    /// An explicit instantiation did not match the scheme it instantiates.
    Instantiation(InstantiationError),
    /// A signature the builder itself writes did not parse.
    ///
    /// The parser's error has no value semantics, so this is the one place the
    /// family carries rendered text rather than an operand.
    SignatureParse {
        /// What the signature was written for.
        item: &'static str,
        /// The parse failure, rendered.
        error: String,
    },
    /// A name the term uses is absent from the environment the checker built.
    UnknownName {
        /// What sort of name failed to resolve.
        kind: NameKind,
        /// The name.
        name: Sym,
    },
    /// A builtin the elaborator emitted has no Core calling convention, so it
    /// was meant to have been erased before this point.
    MissingBuiltinSignature {
        /// The builtin with no signature.
        builtin: Builtin,
    },
    /// A handler carries no return clause at all.
    HandlerWithoutResultClause,
    /// A Core type has no source-language value type to read back out of it.
    NoSourceType {
        /// The type with no inverse.
        found: CoreType,
    },
    /// A constructor use carries a different tag than its declaration.
    ConstructorTag {
        /// The constructor named.
        name: Sym,
        /// The tag the term carries.
        found: usize,
        /// The tag the declaration fixes.
        expected: usize,
    },
    /// An operand list is the wrong length for what it fills.
    Arity {
        /// What the operands belong to.
        subject: BuildSubject,
        /// Operands supplied.
        found: usize,
        /// Operands the declaration fixes.
        expected: usize,
    },
    /// A position requires a form its operand's type does not have.
    NotAForm {
        /// Where the operand sits.
        site: Site,
        /// The form the position requires.
        expected: Form,
        /// The type found instead.
        found: CoreType,
    },
    /// A node that only exists after effect lowering reached the builder.
    RuntimeNode,
    /// A case with no arms fixes no result type.
    CaseWithoutArms,
    /// A handler carries half of a return clause.
    IncompleteHandlerReturn,
    /// Two clauses of one handler answer the same operation.
    DuplicateHandlerOperation(Sym),
    /// A failure found under a named position of the term.
    In {
        /// Where in the term the builder was working.
        context: BuildContext,
        /// What went wrong there.
        error: Box<Self>,
    },
}

impl BuildError {
    /// Record that this failure was found under `context`.
    #[must_use]
    pub fn at(self, context: impl Into<BuildContext>) -> Self {
        Self::In {
            context: context.into(),
            error: Box::new(self),
        }
    }
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Solve(error) => write!(f, "{error}"),
            Self::Scheme(error) => write!(f, "{error}"),
            Self::Instantiation(error) => write!(f, "{error}"),
            Self::SignatureParse { item, error } => {
                write!(f, "cannot parse the {item} signature: {error}")
            }
            Self::UnknownName { kind, name } => write!(f, "{kind} {name}"),
            Self::MissingBuiltinSignature { builtin } => write!(
                f,
                "elaborator-only builtin {} has no signature",
                builtin.name()
            ),
            Self::HandlerWithoutResultClause => f.write_str("handler has no result clause"),
            Self::NoSourceType { found } => {
                write!(f, "{found} has no source-language value type")
            }
            Self::ConstructorTag {
                name,
                found,
                expected,
            } => write!(
                f,
                "constructor {name} carries tag {found} rather than {expected}"
            ),
            Self::Arity {
                subject,
                found,
                expected,
            } => write!(f, "{subject} arity {found} does not match {expected}"),
            Self::NotAForm {
                site,
                expected,
                found,
            } => write!(f, "{site} is not {expected}: {found}"),
            Self::RuntimeNode => f.write_str("runtime node reached the typed builder"),
            Self::CaseWithoutArms => f.write_str("case has no arms"),
            Self::IncompleteHandlerReturn => f.write_str("incomplete handler return clause"),
            Self::DuplicateHandlerOperation(name) => {
                write!(f, "duplicate handler operation {name}")
            }
            Self::In { context, error } => write!(f, "{context}: {error}"),
        }
    }
}

impl std::error::Error for BuildError {}

impl From<SolveError> for BuildError {
    fn from(error: SolveError) -> Self {
        Self::Solve(Box::new(error))
    }
}

impl From<RowUnionError> for BuildError {
    fn from(error: RowUnionError) -> Self {
        Self::Solve(Box::new(SolveError::Union(error)))
    }
}

impl From<SchemeError> for BuildError {
    fn from(error: SchemeError) -> Self {
        Self::Scheme(error)
    }
}

impl From<InstantiationError> for BuildError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
    }
}

/// The operation-to-effect pairs a handler forwards, as one readable list.
fn show_forwarding(pairs: &[(Sym, Label)]) -> String {
    let shown: Vec<String> = pairs
        .iter()
        .map(|(operation, effect)| format!("{operation}: {}", effect.show()))
        .collect();
    format!("[{}]", shown.join(", "))
}
