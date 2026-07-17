//! Typed CBPV Core, the witness-carrying semantic spine.
//!
//! The frontend constructs this representation from checked declarations, runs
//! an independent proof checker, and erases it at an explicit compatibility
//! boundary. [`super::Core`] remains the executable representation consumed by
//! passes outside the verified typed prefix.

mod build;
mod cse;
mod effect_lower;
mod fuse;
mod inline;
mod late;
mod newtypes;
mod pre;
mod rc;
mod reuse;
mod simplify;
pub(crate) mod specialize;
mod specialize_support;
mod verify;

pub(in crate::core) use build::{build_typed, build_verify_env, core_fn_sig, dict_type};
// Exposed for typed-lowering compatibility tests. The production route accepts
// only strategies whose erased result is exact at the compatibility boundary.
pub use effect_lower::abi::LoweredReprProof;
pub(crate) use effect_lower::{lower_effects, TypedLowering};
pub(crate) use late::{execute as execute_late, LateExecutorFailure};
pub(crate) use pre::{execute as execute_pre, PreExecutorFailure};
pub(crate) use rc::insert_rc;
pub(crate) use reuse::reuse;
pub(in crate::core) use verify::{
    instantiate_constructor, instantiate_fn, instantiate_operation, instantiate_value_scheme,
    scheme_to_fn_sig,
};
pub use verify::{verify, ConstructorSig, CoreViolation, OperationSig, TypedCorePhase, VerifyEnv};

use std::marker::PhantomData;

use crate::sym::Sym;
use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::{builtins::Builtin, builtins::FloatOp};
use super::{CheckedHandler, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, IoOp, NegLane, Value};

/// A value type in typed Core.
///
/// Most values retain their checked source type. The other variants name
/// representation-only values introduced after elaboration: suspended
/// computations, local mutable cells, and linear reuse tokens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreType {
    /// A value whose type comes from the checked source language.
    Source(Type),
    /// A suspended computation.
    Thunk(Box<CompSig>),
    /// A callable closure with its explicit Core signature.
    Function(Box<CoreFnSig>),
    /// A local mutable cell introduced by effect lowering.
    Ref(Box<Self>),
    /// The shell consumed by one in-place constructor rebuild.
    ReuseToken(Box<Self>),
    /// A value in the phase-private effect-runtime ABI.
    Lowered(LoweredType),
}

/// One closed representation in the phase-private effect-runtime ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredType {
    /// One native Prism value word whose source type is existential here.
    Word,
    /// A reified free-monad computation.
    Eff(EffRow),
    /// A type-aligned continuation queue.
    Queue(EffRow),
    /// The result of inspecting one continuation queue.
    QueueView(EffRow),
}

/// One outer quantifier on a Core function, constructor, or operation scheme.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreQuantifier {
    /// A type- or natural-kinded variable.
    Type(Sym),
    /// An effect-row-kinded variable.
    Row(Sym),
}

/// One explicit instantiation argument carried at a polymorphic Core use site.
///
/// The verifier substitutes these arguments into the declared scheme and only
/// compares the result; it never searches for an instantiation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreInstantiation {
    /// A type or type-level natural argument.
    Type(Type),
    /// An effect-row argument.
    Row(EffRow),
}

/// The result type and observable effect row of a Core computation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompSig {
    result: CoreType,
    effects: EffRow,
}

impl CompSig {
    /// The computation's result value type.
    #[must_use]
    pub const fn result(&self) -> &CoreType {
        &self.result
    }

    /// The computation's observable effect row.
    #[must_use]
    pub const fn effects(&self) -> &EffRow {
        &self.effects
    }

    pub(super) const fn new(result: CoreType, effects: EffRow) -> Self {
        Self { result, effects }
    }
}

/// The checked signature of one Core function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreFnSig {
    quantifiers: Vec<CoreQuantifier>,
    params: Vec<CoreType>,
    body: CompSig,
}

impl CoreFnSig {
    /// Outer scheme quantifiers, in instantiation order.
    #[must_use]
    pub fn quantifiers(&self) -> &[CoreQuantifier] {
        &self.quantifiers
    }

    /// Parameter types in calling-convention order, including dictionary
    /// parameters inserted by elaboration.
    #[must_use]
    pub fn params(&self) -> &[CoreType] {
        &self.params
    }

    /// The function body's result type and effect row.
    #[must_use]
    pub const fn body(&self) -> &CompSig {
        &self.body
    }

    pub(super) const fn new(
        quantifiers: Vec<CoreQuantifier>,
        params: Vec<CoreType>,
        body: CompSig,
    ) -> Self {
        Self {
            quantifiers,
            params,
            body,
        }
    }
}

/// A typed local binder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedBinder {
    name: Sym,
    ty: CoreType,
    erasure: BinderErasure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BinderErasure {
    Identity,
    RcSequence,
}

impl TypedBinder {
    /// The hygienic Core name.
    #[must_use]
    pub const fn name(&self) -> Sym {
        self.name
    }

    /// The value type introduced into scope.
    #[must_use]
    pub const fn ty(&self) -> &CoreType {
        &self.ty
    }

    pub(super) const fn new(name: Sym, ty: CoreType) -> Self {
        Self {
            name,
            ty,
            erasure: BinderErasure::Identity,
        }
    }

    /// Build the non-binding witness for an administrative RC sequence.
    ///
    /// Its typed name cannot shadow a source binder. Erasure restores raw
    /// Core's legacy `_` binder exactly at the compatibility boundary.
    pub(in crate::core::typed) fn rc_sequence() -> Self {
        Self {
            name: Sym::new(crate::names::RC_SEQUENCE_BINDER),
            ty: CoreType::Source(Type::Unit),
            erasure: BinderErasure::RcSequence,
        }
    }

    fn erase_name(&self) -> Sym {
        match self.erasure {
            BinderErasure::Identity => self.name,
            BinderErasure::RcSequence => Sym::new("_"),
        }
    }
}

/// A Core case pattern whose introduced binders retain their types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedPattern {
    /// Ignore the scrutinee.
    Wild,
    /// Bind the complete scrutinee.
    Var(TypedBinder),
    /// Match a constructor and optionally bind each field.
    Ctor {
        /// Constructor name.
        name: Sym,
        /// Explicit arguments for its declared scheme.
        instantiation: Vec<CoreInstantiation>,
        /// Optional field binders.
        fields: Vec<Option<TypedBinder>>,
    },
    /// Destructure a tuple and optionally bind each component.
    Tuple(Vec<Option<TypedBinder>>),
}

impl TypedPattern {
    fn erase(self) -> CorePat {
        match self {
            Self::Wild => CorePat::Wild,
            Self::Var(binder) => CorePat::Var(binder.name),
            Self::Ctor {
                name,
                instantiation: _,
                fields,
            } => CorePat::Ctor(
                name,
                fields
                    .into_iter()
                    .map(|binder| binder.map(|binder| binder.name))
                    .collect(),
            ),
            Self::Tuple(fields) => CorePat::Tuple(
                fields
                    .into_iter()
                    .map(|binder| binder.map(|binder| binder.name))
                    .collect(),
            ),
        }
    }
}

/// A typed Core value.
///
/// Fields are private so only the checked builders in this module can pair a
/// [`TypedValueKind`] with its witness type.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedValue {
    ty: CoreType,
    kind: TypedValueKind,
}

impl TypedValue {
    /// The checked value type.
    #[must_use]
    pub const fn ty(&self) -> &CoreType {
        &self.ty
    }

    /// The value node, exposed read-only to verifiers and typed passes.
    #[must_use]
    pub const fn kind(&self) -> &TypedValueKind {
        &self.kind
    }

    pub(super) const fn new(ty: CoreType, kind: TypedValueKind) -> Self {
        Self { ty, kind }
    }

    fn erase(self) -> Value {
        match self.kind {
            TypedValueKind::Var {
                name,
                instantiation: _,
            } => Value::Var(name),
            TypedValueKind::Int(value) => Value::Int(value),
            TypedValueKind::I64(value) => Value::I64(value),
            TypedValueKind::U64(value) => Value::U64(value),
            TypedValueKind::Float(value) => Value::Float(value),
            TypedValueKind::Bool(value) => Value::Bool(value),
            TypedValueKind::Unit => Value::Unit,
            TypedValueKind::Str(value) => Value::Str(value),
            TypedValueKind::Reinterpret(value)
            | TypedValueKind::LoweredRepr { value, proof: _ }
            | TypedValueKind::NewtypeRepr {
                constructor: _,
                instantiation: _,
                value,
            } => value.erase(),
            TypedValueKind::Thunk(body) => Value::Thunk(Box::new(body.erase())),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation: _,
                fields,
            } => Value::Ctor(name, tag, fields.into_iter().map(Self::erase).collect()),
            TypedValueKind::Tuple(fields) => {
                Value::Tuple(fields.into_iter().map(Self::erase).collect())
            }
            TypedValueKind::UnboxedTuple(fields) => {
                Value::UnboxedTuple(fields.into_iter().map(Self::erase).collect())
            }
            TypedValueKind::UnboxedRecord(fields) => Value::UnboxedRecord(
                fields
                    .into_iter()
                    .map(|(name, value)| (name, value.erase()))
                    .collect(),
            ),
        }
    }
}

/// The node family of a typed Core value.
#[derive(Clone, Debug, PartialEq)]
pub enum TypedValueKind {
    /// A local or global reference.
    Var {
        /// The referenced binder or definition.
        name: Sym,
        /// Explicit scheme arguments for polymorphic local or global uses.
        instantiation: Vec<CoreInstantiation>,
    },
    /// A machine-sized signed integer.
    Int(i64),
    /// A fixed-width signed integer.
    I64(i64),
    /// A fixed-width unsigned integer.
    U64(u64),
    /// A floating-point value, compared and erased by its IEEE value.
    Float(f64),
    /// A boolean.
    Bool(bool),
    /// The unit value.
    Unit,
    /// A string.
    Str(String),
    /// A representation-preserving scalar coercion erased by legacy Core.
    Reinterpret(Box<TypedValue>),
    /// An explicit pack or unpack at the phase-private effect-runtime ABI.
    LoweredRepr {
        /// The value on the other side of the runtime representation boundary.
        value: Box<TypedValue>,
        /// Unforgeable evidence that typed effect lowering introduced this node.
        proof: LoweredReprProof,
    },
    /// A checked representation coercion across a declared `newtype` boundary.
    ///
    /// The constructor and its explicit instantiation let the independent
    /// verifier prove either direction (construction or irrefutable-match
    /// projection) without inference. Erasure drops only this evidence node.
    NewtypeRepr {
        /// The program-declared newtype constructor proving the coercion.
        constructor: Sym,
        /// Explicit arguments for the constructor's declared scheme.
        instantiation: Vec<CoreInstantiation>,
        /// The value on the other side of the representation boundary.
        value: Box<TypedValue>,
    },
    /// A suspended computation.
    Thunk(Box<TypedComp>),
    /// A boxed data constructor.
    Ctor {
        /// Constructor name.
        name: Sym,
        /// Stable runtime tag.
        tag: usize,
        /// Explicit arguments for the constructor scheme.
        instantiation: Vec<CoreInstantiation>,
        /// Constructor fields.
        fields: Vec<TypedValue>,
    },
    /// A boxed tuple.
    Tuple(Vec<TypedValue>),
    /// An unboxed positional product.
    UnboxedTuple(Vec<TypedValue>),
    /// An unboxed named product.
    UnboxedRecord(Vec<(Sym, TypedValue)>),
}

/// One typed handler operation clause.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedHandleOp {
    name: Sym,
    instantiation: Vec<CoreInstantiation>,
    params: Vec<TypedBinder>,
    resume: TypedBinder,
    body: TypedComp,
}

impl TypedHandleOp {
    /// The handled operation name.
    #[must_use]
    pub const fn name(&self) -> Sym {
        self.name
    }

    /// Explicit arguments for the handled operation's declared scheme.
    #[must_use]
    pub fn instantiation(&self) -> &[CoreInstantiation] {
        &self.instantiation
    }

    /// Operation argument binders.
    #[must_use]
    pub fn params(&self) -> &[TypedBinder] {
        &self.params
    }

    /// The resumption binder.
    #[must_use]
    pub const fn resume(&self) -> &TypedBinder {
        &self.resume
    }

    /// The checked clause body.
    #[must_use]
    pub const fn body(&self) -> &TypedComp {
        &self.body
    }

    pub(super) const fn new(
        name: Sym,
        instantiation: Vec<CoreInstantiation>,
        params: Vec<TypedBinder>,
        resume: TypedBinder,
        body: TypedComp,
    ) -> Self {
        Self {
            name,
            instantiation,
            params,
            resume,
            body,
        }
    }

    fn erase(self) -> HandleOp {
        HandleOp {
            name: self.name,
            params: self.params.into_iter().map(|binder| binder.name).collect(),
            resume: self.resume.name,
            body: self.body.erase(),
        }
    }
}

/// Typed evidence that an omitted operation is forwarded through a partial
/// handler at this effect instantiation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypedForward {
    operation: Sym,
    effect: Label,
}

impl TypedForward {
    /// The original operation identity re-performed by the forwarding path.
    #[must_use]
    pub const fn operation(&self) -> Sym {
        self.operation
    }

    /// The residual effect instantiation carried by the forwarding path.
    #[must_use]
    pub const fn effect(&self) -> &Label {
        &self.effect
    }

    pub(super) const fn new(operation: Sym, effect: Label) -> Self {
        Self { operation, effect }
    }
}

/// A duplicate-free typed handler clause collection with explicit residual
/// forwarding evidence.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedHandler {
    arms: Vec<TypedHandleOp>,
    forwarded: Vec<TypedForward>,
}

impl TypedHandler {
    /// Handler clauses in source order.
    #[must_use]
    pub fn arms(&self) -> &[TypedHandleOp] {
        &self.arms
    }

    /// Omitted operations forwarded outward, in canonical operation order.
    #[must_use]
    pub fn forwarded(&self) -> &[TypedForward] {
        &self.forwarded
    }

    pub(super) fn new(arms: Vec<TypedHandleOp>) -> Result<Self, Sym> {
        let mut names = std::collections::BTreeSet::new();
        let duplicate = arms
            .iter()
            .map(|arm| arm.name)
            .find(|name| !names.insert(*name));
        duplicate.map_or_else(
            || {
                Ok(Self {
                    arms,
                    forwarded: Vec::new(),
                })
            },
            Err,
        )
    }

    fn with_forwarded(mut self, mut forwarded: Vec<TypedForward>) -> Self {
        forwarded.sort();
        forwarded.dedup();
        self.forwarded = forwarded;
        self
    }

    fn erase(self) -> CheckedHandler {
        CheckedHandler::new(self.arms.into_iter().map(TypedHandleOp::erase).collect())
            .expect("typed handler uniqueness survives erasure")
    }
}

/// A typed Core computation.
///
/// Fields are private so a node cannot be paired with an arbitrary result and
/// effect witness outside the typed builder boundary.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedComp {
    sig: CompSig,
    kind: TypedCompKind,
}

impl TypedComp {
    /// The checked result type and effect row.
    #[must_use]
    pub const fn sig(&self) -> &CompSig {
        &self.sig
    }

    /// The computation node, exposed read-only to verifiers and typed passes.
    #[must_use]
    pub const fn kind(&self) -> &TypedCompKind {
        &self.kind
    }

    pub(super) const fn new(sig: CompSig, kind: TypedCompKind) -> Self {
        Self { sig, kind }
    }

    #[allow(clippy::too_many_lines)]
    fn erase(self) -> Comp {
        match self.kind {
            TypedCompKind::Return(value) => Comp::Return(value.erase()),
            TypedCompKind::Bind(first, binder, rest) => Comp::Bind(
                Box::new(first.erase()),
                binder.erase_name(),
                Box::new(rest.erase()),
            ),
            TypedCompKind::Force(value) => Comp::Force(value.erase()),
            TypedCompKind::Lam(params, body) => Comp::Lam(
                params.into_iter().map(|binder| binder.name).collect(),
                Box::new(body.erase()),
            ),
            TypedCompKind::App {
                callee,
                instantiation: _,
                args,
            } => Comp::App(
                Box::new(callee.erase()),
                args.into_iter().map(TypedValue::erase).collect(),
            ),
            TypedCompKind::If(cond, yes, no) => {
                Comp::If(cond.erase(), Box::new(yes.erase()), Box::new(no.erase()))
            }
            TypedCompKind::Prim(op, lhs, rhs) => Comp::Prim(op, lhs.erase(), rhs.erase()),
            TypedCompKind::Call {
                callee: name,
                instantiation: _,
                args,
            } => Comp::Call(name, args.into_iter().map(TypedValue::erase).collect()),
            TypedCompKind::Io(op, args) => {
                Comp::Io(op, args.into_iter().map(TypedValue::erase).collect())
            }
            TypedCompKind::Error(value) => Comp::Error(value.erase()),
            TypedCompKind::Case(scrutinee, arms) => Comp::Case(
                scrutinee.erase(),
                arms.into_iter()
                    .map(|(pattern, body)| (pattern.erase(), body.erase()))
                    .collect(),
            ),
            TypedCompKind::FloatBuiltin(op, value) => Comp::FloatBuiltin(op, value.erase()),
            TypedCompKind::Neg(lane, value) => Comp::Neg(lane, value.erase()),
            TypedCompKind::UnboxedProject(value, field) => {
                Comp::UnboxedProject(value.erase(), field)
            }
            TypedCompKind::Do {
                operation: name,
                instantiation: _,
                args,
            } => Comp::Do(name, args.into_iter().map(TypedValue::erase).collect()),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => Comp::Handle {
                body: Box::new(body.erase()),
                return_var: return_binder.map(|binder| binder.name),
                return_body: return_body.map(|body| Box::new(body.erase())),
                ops: ops.erase(),
            },
            TypedCompKind::Mask(effects, body) => Comp::Mask(effects, Box::new(body.erase())),
            TypedCompKind::StrBuiltin {
                op,
                instantiation: _,
                args,
            } => Comp::StrBuiltin(op, args.into_iter().map(TypedValue::erase).collect()),
            TypedCompKind::Dup(value) => Comp::Dup(value.erase()),
            TypedCompKind::Drop(value) => Comp::Drop(value.erase()),
            TypedCompKind::WithReuse { token, freed, body } => Comp::WithReuse {
                token: token.name,
                freed: freed.erase(),
                body: Box::new(body.erase()),
            },
            TypedCompKind::Reuse(token, value) => Comp::Reuse(token.name, value.erase()),
            TypedCompKind::InitAt(cell, ctor) => Comp::InitAt(cell.erase(), ctor.erase()),
            TypedCompKind::RefNew(value) => Comp::RefNew(value.erase()),
            TypedCompKind::RefGet(value) => Comp::RefGet(value.erase()),
            TypedCompKind::RefSet(cell, value) => Comp::RefSet(cell.erase(), value.erase()),
        }
    }
}

/// The node family of a typed Core computation.
#[derive(Clone, Debug, PartialEq)]
pub enum TypedCompKind {
    /// Return a value.
    Return(TypedValue),
    /// Sequence two computations and bind the first result.
    Bind(Box<TypedComp>, TypedBinder, Box<TypedComp>),
    /// Force a suspended computation.
    Force(TypedValue),
    /// Produce a function closure.
    Lam(Vec<TypedBinder>, Box<TypedComp>),
    /// Apply a computed function closure.
    App {
        /// Computation producing the closure.
        callee: Box<TypedComp>,
        /// Explicit arguments for a polymorphic computed closure.
        instantiation: Vec<CoreInstantiation>,
        /// Runtime arguments.
        args: Vec<TypedValue>,
    },
    /// Branch on a boolean value.
    If(TypedValue, Box<TypedComp>, Box<TypedComp>),
    /// Apply a primitive operator.
    Prim(CoreOp, TypedValue, TypedValue),
    /// Directly call a top-level function.
    Call {
        /// Global function name.
        callee: Sym,
        /// Explicit arguments for its declared scheme.
        instantiation: Vec<CoreInstantiation>,
        /// Runtime arguments.
        args: Vec<TypedValue>,
    },
    /// Execute a builtin I/O operation.
    Io(IoOp, Vec<TypedValue>),
    /// Raise the builtin fatal error.
    Error(TypedValue),
    /// Match a value against compiled patterns.
    Case(TypedValue, Vec<(TypedPattern, TypedComp)>),
    /// Execute a floating-point builtin.
    FloatBuiltin(FloatOp, TypedValue),
    /// Negate a numeric value in its checked lane.
    Neg(NegLane, TypedValue),
    /// Project an unboxed record field.
    UnboxedProject(TypedValue, Sym),
    /// Perform an algebraic effect operation.
    Do {
        /// Effect operation name.
        operation: Sym,
        /// Explicit arguments for its declared scheme.
        instantiation: Vec<CoreInstantiation>,
        /// Runtime operation arguments.
        args: Vec<TypedValue>,
    },
    /// Handle a computation.
    Handle {
        /// The handled computation.
        body: Box<TypedComp>,
        /// Optional return-clause binder.
        return_binder: Option<TypedBinder>,
        /// Optional return-clause body.
        return_body: Option<Box<TypedComp>>,
        /// Duplicate-free operation clauses.
        ops: TypedHandler,
    },
    /// Mask named effects while evaluating a computation.
    Mask(Vec<Sym>, Box<TypedComp>),
    /// Execute a string builtin.
    StrBuiltin {
        /// Runtime builtin.
        op: Builtin,
        /// Explicit arguments for a polymorphic builtin signature.
        instantiation: Vec<CoreInstantiation>,
        /// Runtime arguments.
        args: Vec<TypedValue>,
    },
    /// Increment a value's reference count.
    Dup(TypedValue),
    /// Decrement a value's reference count.
    Drop(TypedValue),
    /// Free a cell and bind its reusable shell.
    WithReuse {
        /// The linear reuse-token binder.
        token: TypedBinder,
        /// The cell whose shell becomes reusable.
        freed: TypedValue,
        /// The token's scope.
        body: Box<TypedComp>,
    },
    /// Spend a reuse token rebuilding a constructor in place.
    Reuse(TypedBinder, TypedValue),
    /// Write a constructor into a cell an allocator handed out.
    InitAt(TypedValue, TypedValue),
    /// Allocate a local mutable cell.
    RefNew(TypedValue),
    /// Read a local mutable cell.
    RefGet(TypedValue),
    /// Write a local mutable cell.
    RefSet(TypedValue, TypedValue),
}

/// One typed top-level Core function.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedCoreFn {
    name: Sym,
    params: Vec<TypedBinder>,
    body: TypedComp,
    sig: CoreFnSig,
    dict_arity: usize,
}

impl TypedCoreFn {
    /// The function's global name.
    #[must_use]
    pub const fn name(&self) -> Sym {
        self.name
    }

    /// Typed parameters in calling-convention order.
    #[must_use]
    pub fn params(&self) -> &[TypedBinder] {
        &self.params
    }

    /// The checked function body.
    #[must_use]
    pub const fn body(&self) -> &TypedComp {
        &self.body
    }

    /// The independently checkable function signature.
    #[must_use]
    pub const fn sig(&self) -> &CoreFnSig {
        &self.sig
    }

    /// Leading dictionary-parameter count.
    #[must_use]
    pub const fn dict_arity(&self) -> usize {
        self.dict_arity
    }

    pub(super) const fn new(
        name: Sym,
        params: Vec<TypedBinder>,
        body: TypedComp,
        sig: CoreFnSig,
        dict_arity: usize,
    ) -> Self {
        Self {
            name,
            params,
            body,
            sig,
            dict_arity,
        }
    }

    fn erase(self) -> CoreFn {
        CoreFn {
            name: self.name,
            params: self.params.into_iter().map(|binder| binder.name).collect(),
            body: self.body.erase(),
            dict_arity: self.dict_arity,
        }
    }
}

/// Marker for checked elaboration output before effect lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Elaborated {}

/// Marker for typed Core after scope-directed arena lowering.
///
/// A transient phase between elaboration and effect lowering: source effect
/// nodes are still present (the `alloc` this pass performs is discharged by the
/// enclosing handler further down the cascade), but `InitAt` is now legal. It
/// exists so arena lowering is a truthful transition rather than a licence to
/// admit a post-lowering node in ordinary elaborated Core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArenaPrepared {}

/// Marker for typed Core after general effect lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectLowered {}

/// Marker for typed Core after reference-count insertion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Owned {}

/// Marker for typed Core after in-place reuse lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReuseLowered {}

/// Whole-program typed Core at phase `P`.
///
/// The phase marker prevents routing errors while the private node builders and
/// independent verifier prevent local type/effect witness drift.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedCore<P> {
    fns: Vec<TypedCoreFn>,
    phase: PhantomData<fn() -> P>,
}

impl<P> TypedCore<P> {
    /// Functions in deterministic program order.
    #[must_use]
    pub fn functions(&self) -> &[TypedCoreFn] {
        &self.fns
    }

    pub(super) const fn new(fns: Vec<TypedCoreFn>) -> Self {
        Self {
            fns,
            phase: PhantomData,
        }
    }

    /// Consume all type/effect witnesses, yielding the existing executable
    /// Core shape byte-for-byte. This is the sole semantic erasure operation at
    /// the typed-prefix boundary.
    #[must_use]
    pub fn erase(self) -> Core {
        Core {
            fns: self.fns.into_iter().map(TypedCoreFn::erase).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::core::hash::hash_program;

    use super::*;

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn literal(ty: Type) -> TypedValue {
        TypedValue::new(source(ty), TypedValueKind::Int(42))
    }

    fn program(witness: Type) -> TypedCore<Elaborated> {
        let value = literal(witness.clone());
        let body = TypedComp::new(pure(source(witness.clone())), TypedCompKind::Return(value));
        TypedCore::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(witness))),
            0,
        )])
    }

    #[test]
    fn erasure_is_annotation_and_hash_neutral() {
        // Deliberately bypass verification and vary only witness data. A Bool
        // witness on an integer literal is invalid, while content identity must
        // remain a function of erased semantics alone.
        let int = program(Type::Int).erase();
        let bool_witness = program(Type::Bool).erase();
        assert_eq!(int, bool_witness);
        assert_eq!(
            hash_program(&int, &BTreeMap::new()),
            hash_program(&bool_witness, &BTreeMap::new())
        );
    }

    #[test]
    fn binder_and_pattern_types_erase_without_moving_structure() {
        let binder = TypedBinder::new(Sym::new("x"), source(Type::Int));
        assert_eq!(
            TypedPattern::Ctor {
                name: Sym::new("Some"),
                instantiation: Vec::new(),
                fields: vec![Some(binder)],
            }
            .erase(),
            CorePat::Ctor(Sym::new("Some"), vec![Some(Sym::new("x"))])
        );
    }

    #[test]
    fn typed_handler_rejects_duplicate_operations_before_erasure() {
        let resume = || TypedBinder::new(Sym::new("k"), source(Type::Unit));
        let body = || {
            TypedComp::new(
                pure(source(Type::Unit)),
                TypedCompKind::Return(TypedValue::new(source(Type::Unit), TypedValueKind::Unit)),
            )
        };
        let arm = || TypedHandleOp::new(Sym::new("get"), Vec::new(), Vec::new(), resume(), body());
        assert_eq!(TypedHandler::new(vec![arm(), arm()]), Err(Sym::new("get")));
    }
}
