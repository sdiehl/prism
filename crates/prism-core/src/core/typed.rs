//! Typed CBPV Core, the witness-carrying semantic spine.
//!
//! The frontend constructs this representation from checked declarations, runs
//! an independent proof checker, and erases it at an explicit compatibility
//! boundary. [`super::Core`] remains the executable representation consumed by
//! passes outside the verified typed prefix.

mod authority;
mod build;
mod cse;
pub mod effect_lower;
mod exact_size;
mod facts;
mod fuse;
mod inline;
mod newtypes;
mod rc;
mod reuse;
mod simplify;
pub mod specialize;
mod specialize_support;
pub mod summary;
pub(crate) mod traverse;
pub mod verify;
pub mod violation;

pub use authority::{audit, verify, TypedCore, UncheckedTypedCore};
pub use build::{build_typed, build_verify_env, core_fn_sig, dict_type};
// The raw typed passes, exposed for the driver's ordered stage runner (which
// owns verification boundaries and the SCC fixed-point cache).
pub use cse::cse;
pub use exact_size::{exact_size, ExactSizeStats};
pub use fuse::fuse;
pub use inline::inline;
pub use newtypes::erase_newtypes;
pub use simplify::simplify;
// Exposed for typed-lowering compatibility tests. The production route accepts
// only strategies whose erased result is exact at the compatibility boundary.
pub use effect_lower::abi::LoweredReprProof;
pub use effect_lower::decline::Decline;
pub use effect_lower::explain::explain as explain_effect_tiers;
pub use effect_lower::{
    lower_effects, lower_effects_with_options, prepare as prepare_effects,
    prepare_with_options as prepare_effects_with_options, EffectPlan, Prepared, TypedLowering,
};
pub use rc::insert_rc;
pub use reuse::reuse;
pub use verify::{
    instantiate_constructor, instantiate_fn, instantiate_operation, instantiate_value_scheme,
    scheme_to_fn_sig,
};
pub use verify::{ConstructorSig, CoreViolation, OperationSig, TypedCorePhase, VerifyEnv};

use std::collections::BTreeSet;
use std::fmt;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;
use prism_common::sym::Sym;

use self::verify::{
    discard_comp_sig, discard_core_fn_sig, discard_core_instantiation, discard_core_type,
    discard_type,
};
pub(crate) use super::work::on_core_stack;
use super::{builtins::Builtin, builtins::FloatOp};
use super::{CheckedHandler, Comp, CoreFn, CoreOp, CorePat, HandleOp, IoOp, NegLane, Value};

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

    #[must_use]
    pub const fn new(result: CoreType, effects: EffRow) -> Self {
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

    #[must_use]
    pub const fn new(
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

// Source-shaped renderings for the witness types.
//
// These exist because a failed judgment is read by a person. `Debug` on these
// types prints the constructor spelling of an internal representation
// (`Thunk(CompSig { result: Source(Fun([...], Empty, ...)), .. })`), which names
// the compiler's data structures rather than the type the program wrote, and it
// is what a verifier violation used to put in front of a user. Every rendering
// below bottoms out in `Type::show`/`EffRow::show`, the same printers the
// checker's own diagnostics use, so one type reads the same way wherever it is
// reported.

impl fmt::Display for CoreType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(ty) => f.write_str(&ty.show()),
            Self::Thunk(signature) => write!(f, "Thunk({signature})"),
            Self::Function(signature) => write!(f, "{signature}"),
            Self::Ref(ty) => write!(f, "Ref({ty})"),
            Self::ReuseToken(ty) => write!(f, "Reuse({ty})"),
            Self::Lowered(ty) => write!(f, "{ty}"),
        }
    }
}

impl fmt::Display for LoweredType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Word => f.write_str("Word"),
            Self::Eff(row) => write!(f, "Eff({})", row.show()),
            Self::Queue(row) => write!(f, "Queue({})", row.show()),
            Self::QueueView(row) => write!(f, "QueueView({})", row.show()),
        }
    }
}

impl fmt::Display for CompSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ! {}", self.result, self.effects.show())
    }
}

impl fmt::Display for CoreQuantifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(name) | Self::Row(name) => write!(f, "{name}"),
        }
    }
}

impl fmt::Display for CoreFnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.quantifiers.is_empty() {
            write!(f, "forall")?;
            for quantifier in &self.quantifiers {
                write!(f, " {quantifier}")?;
            }
            write!(f, ". ")?;
        }
        f.write_str("(")?;
        for (index, param) in self.params.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{param}")?;
        }
        write!(f, ") -> {}", self.body)
    }
}

impl fmt::Display for CoreInstantiation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(ty) => f.write_str(&ty.show()),
            Self::Row(row) => f.write_str(&row.show()),
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

    #[must_use]
    pub const fn new(name: Sym, ty: CoreType) -> Self {
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
            name: Sym::new(prism_syntax::names::RC_SEQUENCE_BINDER),
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

    fn into_name(self) -> Sym {
        let Self {
            name,
            ty,
            erasure: _,
        } = self;
        discard_core_type(ty);
        name
    }

    fn into_erased_name(self) -> Sym {
        let name = self.erase_name();
        discard_core_type(self.ty);
        name
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
            Self::Var(binder) => CorePat::Var(binder.into_name()),
            Self::Ctor {
                name,
                instantiation,
                fields,
            } => {
                discard_instantiations(instantiation);
                CorePat::Ctor(
                    name,
                    fields
                        .into_iter()
                        .map(|binder| binder.map(TypedBinder::into_name))
                        .collect(),
                )
            }
            Self::Tuple(fields) => CorePat::Tuple(
                fields
                    .into_iter()
                    .map(|binder| binder.map(TypedBinder::into_name))
                    .collect(),
            ),
        }
    }
}

/// A typed Core value.
///
/// Fields are private so a built value is read-only, but `new` is open:
/// construction does not check that a [`TypedValueKind`] matches its witness
/// type. The pairing is checked after the fact by the typed-Core verifier,
/// which the test gates run over every pass output.
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

    #[must_use]
    pub const fn new(ty: CoreType, kind: TypedValueKind) -> Self {
        Self { ty, kind }
    }

    /// The binding this value reads, if it reads one.
    ///
    /// Representation wrappers change how a reference is typed, never which
    /// reference it is, so they are transparent here. Anything else builds a
    /// new value rather than reading an existing binding and has no name to
    /// give. Reference counting asks this to find the owner an operation acts
    /// on, and the verifier asks it to refuse an operation that acts on none.
    #[must_use]
    pub fn referenced_binding(&self) -> Option<Sym> {
        let mut value = self;
        loop {
            match &value.kind {
                TypedValueKind::Var { name, .. } => return Some(*name),
                TypedValueKind::Reinterpret(inner)
                | TypedValueKind::LoweredRepr {
                    value: inner,
                    proof: _,
                }
                | TypedValueKind::NewtypeRepr { value: inner, .. } => value = inner,
                _ => return None,
            }
        }
    }

    fn erase(self) -> Value {
        let ErasedNode::Value(value) = erase_node(EraseFrame::Value(self)) else {
            unreachable!("a typed value erases to a raw value")
        };
        value
    }
}

fn discard_instantiations(instantiations: Vec<CoreInstantiation>) {
    for instantiation in instantiations {
        discard_core_instantiation(instantiation);
    }
}

fn discard_label(label: Label) {
    for argument in label.args {
        discard_type(argument);
    }
}

fn discard_forward(forward: TypedForward) {
    let TypedForward {
        operation: _,
        effect,
    } = forward;
    discard_label(effect);
}

fn erase_handle_op(arm: TypedHandleOp) -> HandleOp {
    let TypedHandleOp {
        name,
        instantiation,
        params,
        resume,
        body,
    } = arm;
    discard_instantiations(instantiation);
    HandleOp {
        name,
        params: params.into_iter().map(TypedBinder::into_name).collect(),
        resume: resume.into_name(),
        body: body.erase(),
    }
}

fn erase_handler(handler: TypedHandler) -> CheckedHandler {
    let TypedHandler { arms, forwarded } = handler;
    for forward in forwarded {
        discard_forward(forward);
    }
    CheckedHandler::new(arms.into_iter().map(erase_handle_op).collect())
        .expect("typed handler uniqueness survives erasure")
}

fn pop_value(results: &mut Vec<ErasedNode>) -> Value {
    let Some(ErasedNode::Value(value)) = results.pop() else {
        unreachable!("value-erasure frames preserve result kinds")
    };
    value
}

fn pop_comp(results: &mut Vec<ErasedNode>) -> Comp {
    let Some(ErasedNode::Comp(comp)) = results.pop() else {
        unreachable!("computation-erasure frames preserve result kinds")
    };
    comp
}

fn pop_values(results: &mut Vec<ErasedNode>, count: usize) -> Vec<Value> {
    let start = results.len() - count;
    results
        .drain(start..)
        .map(|node| {
            let ErasedNode::Value(value) = node else {
                unreachable!("value lists contain only erased values")
            };
            value
        })
        .collect()
}

fn pop_comps(results: &mut Vec<ErasedNode>, count: usize) -> Vec<Comp> {
    let start = results.len() - count;
    results
        .drain(start..)
        .map(|node| {
            let ErasedNode::Comp(comp) = node else {
                unreachable!("computation lists contain only erased computations")
            };
            comp
        })
        .collect()
}

fn push_values(work: &mut Vec<EraseFrame>, values: Vec<TypedValue>) {
    work.extend(values.into_iter().rev().map(EraseFrame::Value));
}

fn erase_node(root: EraseFrame) -> ErasedNode {
    let mut work = vec![root];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        erase_frame(frame, &mut work, &mut results);
    }
    let result = results.pop().expect("erasure produces one raw node");
    debug_assert!(results.is_empty());
    result
}

#[allow(clippy::too_many_lines)]
fn erase_frame(frame: EraseFrame, work: &mut Vec<EraseFrame>, results: &mut Vec<ErasedNode>) {
    match frame {
        EraseFrame::Value(value) => erase_value_frame(value, work, results),
        EraseFrame::Comp(comp) => erase_comp_frame(*comp, work),
        EraseFrame::FinishValue(finish) => finish_value(finish, results),
        EraseFrame::FinishComp(finish) => finish_comp(finish, results),
    }
}

fn erase_value_frame(value: TypedValue, work: &mut Vec<EraseFrame>, results: &mut Vec<ErasedNode>) {
    let TypedValue { ty, kind } = value;
    discard_core_type(ty);
    match kind {
        TypedValueKind::Var {
            name,
            instantiation,
        } => {
            discard_instantiations(instantiation);
            results.push(ErasedNode::Value(Value::Var(name)));
        }
        TypedValueKind::Int(value) => results.push(ErasedNode::Value(Value::Int(value))),
        TypedValueKind::I64(value) => results.push(ErasedNode::Value(Value::I64(value))),
        TypedValueKind::U64(value) => results.push(ErasedNode::Value(Value::U64(value))),
        TypedValueKind::Float(value) => results.push(ErasedNode::Value(Value::Float(value))),
        TypedValueKind::Bool(value) => results.push(ErasedNode::Value(Value::Bool(value))),
        TypedValueKind::Unit => results.push(ErasedNode::Value(Value::Unit)),
        TypedValueKind::Str(value) => results.push(ErasedNode::Value(Value::Str(value))),
        TypedValueKind::Reinterpret(value) | TypedValueKind::LoweredRepr { value, proof: _ } => {
            work.push(EraseFrame::Value(*value));
        }
        TypedValueKind::NewtypeRepr {
            constructor: _,
            instantiation,
            value,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::Value(*value));
        }
        TypedValueKind::Thunk(body) => {
            work.push(EraseFrame::FinishValue(ValueFinish::Thunk));
            work.push(EraseFrame::Comp(body));
        }
        TypedValueKind::Ctor {
            name,
            tag,
            instantiation,
            fields,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::FinishValue(ValueFinish::Ctor {
                name,
                tag,
                fields: fields.len(),
            }));
            push_values(work, fields);
        }
        TypedValueKind::Tuple(fields) => {
            work.push(EraseFrame::FinishValue(ValueFinish::Tuple(fields.len())));
            push_values(work, fields);
        }
        TypedValueKind::UnboxedTuple(fields) => {
            work.push(EraseFrame::FinishValue(ValueFinish::UnboxedTuple(
                fields.len(),
            )));
            push_values(work, fields);
        }
        TypedValueKind::UnboxedRecord(fields) => {
            let (names, fields): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
            work.push(EraseFrame::FinishValue(ValueFinish::UnboxedRecord(names)));
            push_values(work, fields);
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

impl TypedValueKind {
    /// The canonical source type of a scalar literal, or `None` for a value
    /// with no literal encoding (variables, structures, thunks).
    ///
    /// Seen through the representation-preserving wrapper nodes: a wrapped
    /// literal keeps its scalar encoding by the wrappers' own contract, so
    /// the answer is the underlying literal's type. Consumers pass it to the
    /// representation authority (`types::scalar_plan`) rather than deciding
    /// an encoding here. Mirrors `Value::literal_scalar_type` post-erasure.
    #[must_use]
    pub fn literal_scalar_type(&self) -> Option<Type> {
        let mut kind = self;
        loop {
            match kind {
                Self::Int(_) => return Some(Type::Int),
                Self::I64(_) => return Some(Type::I64),
                Self::U64(_) => return Some(Type::U64),
                Self::Float(_) => return Some(Type::Float),
                Self::Bool(_) => return Some(Type::Bool),
                Self::Unit => return Some(Type::Unit),
                Self::Str(_) => return Some(Type::Str),
                Self::Reinterpret(inner)
                | Self::LoweredRepr {
                    value: inner,
                    proof: _,
                }
                | Self::NewtypeRepr { value: inner, .. } => kind = &inner.kind,
                _ => return None,
            }
        }
    }
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

    #[must_use]
    pub const fn new(
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

    #[must_use]
    pub const fn new(operation: Sym, effect: Label) -> Self {
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

    /// A handler over `arms`, which must name each operation at most once.
    ///
    /// # Errors
    /// The duplicated operation name, when two arms handle the same operation.
    pub fn new(arms: Vec<TypedHandleOp>) -> Result<Self, Sym> {
        let mut names = BTreeSet::new();
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

    pub(in crate::core::typed) fn with_forwarded(
        mut self,
        mut forwarded: Vec<TypedForward>,
    ) -> Self {
        forwarded.sort();
        forwarded.dedup();
        self.forwarded = forwarded;
        self
    }

    fn erase(self) -> CheckedHandler {
        erase_handler(self)
    }
}

/// A typed Core computation.
///
/// Fields are private so a built node is read-only, but `new` is open:
/// construction does not check the result and effect witness against the node.
/// The pairing is checked after the fact by the typed-Core verifier, which the
/// test gates run over every pass output.
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

    #[must_use]
    pub const fn new(sig: CompSig, kind: TypedCompKind) -> Self {
        Self { sig, kind }
    }

    fn erase(self) -> Comp {
        let ErasedNode::Comp(comp) = erase_node(EraseFrame::Comp(Box::new(self))) else {
            unreachable!("a typed computation erases to a raw computation")
        };
        comp
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

enum EraseFrame {
    Value(TypedValue),
    // Boxed so a frame stays small; every push site already holds the box
    // its node kind carried, so no allocation is added.
    Comp(Box<TypedComp>),
    FinishValue(ValueFinish),
    FinishComp(CompFinish),
}

enum ValueFinish {
    Thunk,
    Ctor {
        name: Sym,
        tag: usize,
        fields: usize,
    },
    Tuple(usize),
    UnboxedTuple(usize),
    UnboxedRecord(Vec<Sym>),
}

enum CompFinish {
    Return,
    Bind(Sym),
    Force,
    Lam(Vec<Sym>),
    App(usize),
    If,
    Prim(CoreOp),
    Call(Sym, usize),
    Io(IoOp, usize),
    Error,
    Case(Vec<CorePat>),
    FloatBuiltin(FloatOp),
    Neg(NegLane),
    UnboxedProject(Sym),
    Do(Sym, usize),
    Handle {
        return_var: Option<Sym>,
        has_return: bool,
        ops: CheckedHandler,
    },
    Mask(Vec<Sym>),
    StrBuiltin(Builtin, usize),
    Dup,
    Drop,
    WithReuse(Sym),
    Reuse(Sym),
    InitAt,
    RefNew,
    RefGet,
    RefSet,
}

enum ErasedNode {
    Value(Value),
    Comp(Comp),
}

#[allow(clippy::too_many_lines)]
fn erase_comp_frame(comp: TypedComp, work: &mut Vec<EraseFrame>) {
    let TypedComp { sig, kind } = comp;
    discard_comp_sig(sig);
    match kind {
        TypedCompKind::Return(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Return));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Bind(first, binder, rest) => {
            work.push(EraseFrame::FinishComp(CompFinish::Bind(
                binder.into_erased_name(),
            )));
            work.push(EraseFrame::Comp(rest));
            work.push(EraseFrame::Comp(first));
        }
        TypedCompKind::Force(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Force));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Lam(params, body) => {
            work.push(EraseFrame::FinishComp(CompFinish::Lam(
                params.into_iter().map(TypedBinder::into_name).collect(),
            )));
            work.push(EraseFrame::Comp(body));
        }
        TypedCompKind::App {
            callee,
            instantiation,
            args,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::FinishComp(CompFinish::App(args.len())));
            push_values(work, args);
            work.push(EraseFrame::Comp(callee));
        }
        TypedCompKind::If(condition, yes, no) => {
            work.push(EraseFrame::FinishComp(CompFinish::If));
            work.push(EraseFrame::Comp(no));
            work.push(EraseFrame::Comp(yes));
            work.push(EraseFrame::Value(condition));
        }
        TypedCompKind::Prim(op, left, right) => {
            work.push(EraseFrame::FinishComp(CompFinish::Prim(op)));
            work.push(EraseFrame::Value(right));
            work.push(EraseFrame::Value(left));
        }
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::FinishComp(CompFinish::Call(callee, args.len())));
            push_values(work, args);
        }
        TypedCompKind::Io(op, args) => {
            work.push(EraseFrame::FinishComp(CompFinish::Io(op, args.len())));
            push_values(work, args);
        }
        TypedCompKind::Error(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Error));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Case(scrutinee, arms) => {
            let (patterns, bodies): (Vec<_>, Vec<_>) = arms
                .into_iter()
                .map(|(pattern, body)| (pattern.erase(), body))
                .unzip();
            work.push(EraseFrame::FinishComp(CompFinish::Case(patterns)));
            work.extend(
                bodies
                    .into_iter()
                    .rev()
                    .map(|body| EraseFrame::Comp(Box::new(body))),
            );
            work.push(EraseFrame::Value(scrutinee));
        }
        TypedCompKind::FloatBuiltin(op, value) => {
            work.push(EraseFrame::FinishComp(CompFinish::FloatBuiltin(op)));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Neg(lane, value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Neg(lane)));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::UnboxedProject(value, field) => {
            work.push(EraseFrame::FinishComp(CompFinish::UnboxedProject(field)));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Do {
            operation,
            instantiation,
            args,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::FinishComp(CompFinish::Do(
                operation,
                args.len(),
            )));
            push_values(work, args);
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            let has_return = return_body.is_some();
            work.push(EraseFrame::FinishComp(CompFinish::Handle {
                return_var: return_binder.map(TypedBinder::into_name),
                has_return,
                ops: ops.erase(),
            }));
            if let Some(return_body) = return_body {
                work.push(EraseFrame::Comp(return_body));
            }
            work.push(EraseFrame::Comp(body));
        }
        TypedCompKind::Mask(effects, body) => {
            work.push(EraseFrame::FinishComp(CompFinish::Mask(effects)));
            work.push(EraseFrame::Comp(body));
        }
        TypedCompKind::StrBuiltin {
            op,
            instantiation,
            args,
        } => {
            discard_instantiations(instantiation);
            work.push(EraseFrame::FinishComp(CompFinish::StrBuiltin(
                op,
                args.len(),
            )));
            push_values(work, args);
        }
        TypedCompKind::Dup(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Dup));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::Drop(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Drop));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::WithReuse { token, freed, body } => {
            work.push(EraseFrame::FinishComp(CompFinish::WithReuse(
                token.into_name(),
            )));
            work.push(EraseFrame::Comp(body));
            work.push(EraseFrame::Value(freed));
        }
        TypedCompKind::Reuse(token, value) => {
            work.push(EraseFrame::FinishComp(CompFinish::Reuse(token.into_name())));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::InitAt(cell, constructor) => {
            work.push(EraseFrame::FinishComp(CompFinish::InitAt));
            work.push(EraseFrame::Value(constructor));
            work.push(EraseFrame::Value(cell));
        }
        TypedCompKind::RefNew(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::RefNew));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::RefGet(value) => {
            work.push(EraseFrame::FinishComp(CompFinish::RefGet));
            work.push(EraseFrame::Value(value));
        }
        TypedCompKind::RefSet(cell, value) => {
            work.push(EraseFrame::FinishComp(CompFinish::RefSet));
            work.push(EraseFrame::Value(value));
            work.push(EraseFrame::Value(cell));
        }
    }
}

fn finish_value(finish: ValueFinish, results: &mut Vec<ErasedNode>) {
    let value = match finish {
        ValueFinish::Thunk => Value::Thunk(Box::new(pop_comp(results))),
        ValueFinish::Ctor { name, tag, fields } => {
            Value::Ctor(name, tag, pop_values(results, fields))
        }
        ValueFinish::Tuple(fields) => Value::Tuple(pop_values(results, fields)),
        ValueFinish::UnboxedTuple(fields) => Value::UnboxedTuple(pop_values(results, fields)),
        ValueFinish::UnboxedRecord(names) => {
            let fields = pop_values(results, names.len());
            Value::UnboxedRecord(names.into_iter().zip(fields).collect())
        }
    };
    results.push(ErasedNode::Value(value));
}

#[allow(clippy::too_many_lines)]
fn finish_comp(finish: CompFinish, results: &mut Vec<ErasedNode>) {
    let comp = match finish {
        CompFinish::Return => Comp::Return(pop_value(results)),
        CompFinish::Bind(binder) => {
            let rest = pop_comp(results);
            let first = pop_comp(results);
            Comp::Bind(Box::new(first), binder, Box::new(rest))
        }
        CompFinish::Force => Comp::Force(pop_value(results)),
        CompFinish::Lam(params) => Comp::Lam(params, Box::new(pop_comp(results))),
        CompFinish::App(argument_count) => {
            let arguments = pop_values(results, argument_count);
            let callee = pop_comp(results);
            Comp::App(Box::new(callee), arguments)
        }
        CompFinish::If => {
            let no = pop_comp(results);
            let yes = pop_comp(results);
            let condition = pop_value(results);
            Comp::If(condition, Box::new(yes), Box::new(no))
        }
        CompFinish::Prim(op) => {
            let right = pop_value(results);
            let left = pop_value(results);
            Comp::Prim(op, left, right)
        }
        CompFinish::Call(callee, argument_count) => {
            Comp::Call(callee, pop_values(results, argument_count))
        }
        CompFinish::Io(op, argument_count) => Comp::Io(op, pop_values(results, argument_count)),
        CompFinish::Error => Comp::Error(pop_value(results)),
        CompFinish::Case(patterns) => {
            let bodies = pop_comps(results, patterns.len());
            let scrutinee = pop_value(results);
            Comp::Case(scrutinee, patterns.into_iter().zip(bodies).collect())
        }
        CompFinish::FloatBuiltin(op) => Comp::FloatBuiltin(op, pop_value(results)),
        CompFinish::Neg(lane) => Comp::Neg(lane, pop_value(results)),
        CompFinish::UnboxedProject(field) => Comp::UnboxedProject(pop_value(results), field),
        CompFinish::Do(operation, argument_count) => {
            Comp::Do(operation, pop_values(results, argument_count))
        }
        CompFinish::Handle {
            return_var,
            has_return,
            ops,
        } => {
            let return_body = has_return.then(|| Box::new(pop_comp(results)));
            let body = Box::new(pop_comp(results));
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            }
        }
        CompFinish::Mask(effects) => Comp::Mask(effects, Box::new(pop_comp(results))),
        CompFinish::StrBuiltin(op, argument_count) => {
            Comp::StrBuiltin(op, pop_values(results, argument_count))
        }
        CompFinish::Dup => Comp::Dup(pop_value(results)),
        CompFinish::Drop => Comp::Drop(pop_value(results)),
        CompFinish::WithReuse(token) => {
            let body = Box::new(pop_comp(results));
            let freed = pop_value(results);
            Comp::WithReuse { token, freed, body }
        }
        CompFinish::Reuse(token) => Comp::Reuse(token, pop_value(results)),
        CompFinish::InitAt => {
            let constructor = pop_value(results);
            let cell = pop_value(results);
            Comp::InitAt(cell, constructor)
        }
        CompFinish::RefNew => Comp::RefNew(pop_value(results)),
        CompFinish::RefGet => Comp::RefGet(pop_value(results)),
        CompFinish::RefSet => {
            let value = pop_value(results);
            let cell = pop_value(results);
            Comp::RefSet(cell, value)
        }
    };
    results.push(ErasedNode::Comp(comp));
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

    #[must_use]
    pub const fn new(
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
        let Self {
            name,
            params,
            body,
            sig,
            dict_arity,
        } = self;
        discard_core_fn_sig(sig);
        CoreFn {
            name,
            params: params.into_iter().map(TypedBinder::into_name).collect(),
            body: body.erase(),
            dict_arity,
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

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, mem, thread};

    use crate::core::hash::hash_program;
    use crate::core::Core;

    use super::*;

    const DEEP_ERASURE_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn literal(ty: Type) -> TypedValue {
        TypedValue::new(source(ty), TypedValueKind::Int(42))
    }

    fn erased_program(witness: Type) -> Core {
        let value = literal(witness.clone());
        let body = TypedComp::new(pure(source(witness.clone())), TypedCompKind::Return(value));
        Core {
            fns: vec![TypedCoreFn::new(
                Sym::new("main"),
                Vec::new(),
                body,
                CoreFnSig::new(Vec::new(), Vec::new(), pure(source(witness))),
                0,
            )
            .erase()],
        }
    }

    #[test]
    fn erasure_is_annotation_and_hash_neutral() {
        // Deliberately bypass verification and vary only witness data. A Bool
        // witness on an integer literal is invalid, while content identity must
        // remain a function of erased semantics alone.
        let int = erased_program(Type::Int);
        let bool_witness = erased_program(Type::Bool);
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

    #[test]
    fn erasure_handles_deep_terms_values_and_witnesses_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-typed-erasure".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut witness = Type::Int;
                for _ in 0..DEEP_ERASURE_DEPTH {
                    witness = Type::OrNull(Box::new(witness));
                }
                let mut value = TypedValue::new(CoreType::Source(witness), TypedValueKind::Int(0));
                for _ in 0..DEEP_ERASURE_DEPTH {
                    value = TypedValue::new(
                        source(Type::Int),
                        TypedValueKind::Reinterpret(Box::new(value)),
                    );
                }

                let mut body =
                    TypedComp::new(pure(source(Type::Int)), TypedCompKind::Return(value));
                for _ in 0..DEEP_ERASURE_DEPTH {
                    let first = TypedComp::new(
                        pure(source(Type::Unit)),
                        TypedCompKind::Return(TypedValue::new(
                            source(Type::Unit),
                            TypedValueKind::Unit,
                        )),
                    );
                    body = TypedComp::new(
                        pure(source(Type::Int)),
                        TypedCompKind::Bind(
                            Box::new(first),
                            TypedBinder::new(Sym::new("_step"), source(Type::Unit)),
                            Box::new(body),
                        ),
                    );
                }

                let function = TypedCoreFn::new(
                    Sym::new("deep_erasure"),
                    Vec::new(),
                    body,
                    CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
                    0,
                );
                let erased = function.erase();
                let mut cursor = &erased.body;
                for _ in 0..DEEP_ERASURE_DEPTH {
                    let Comp::Bind(first, binder, rest) = cursor else {
                        panic!("erasure changed the deep bind spine");
                    };
                    assert!(matches!(first.as_ref(), Comp::Return(Value::Unit)));
                    assert_eq!(binder.as_str(), "_step");
                    cursor = rest;
                }
                assert!(matches!(cursor, Comp::Return(Value::Int(0))));
                mem::forget(erased);
            })
            .expect("spawn deep typed erasure test")
            .join()
            .expect("deep typed erasure test panicked");
    }
}
