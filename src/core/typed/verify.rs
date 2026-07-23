//! Independent proof checker for witness-carrying Core.
//!
//! This module deliberately does not call inference or unification. Every
//! polymorphic use carries an explicit instantiation; checking substitutes that
//! evidence into a declared scheme and compares the stored witnesses exactly.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::names::{self, ALLOC_OP, IO_EFFECT};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label};
use crate::types::{repr_of_type, Type};

// Red zone / segment size for the verifier's per-node recursion, matching the
// builder guards in `core/typed/build.rs`.
const VERIFY_MIN_STACK: usize = 4 * 1024 * 1024;
const VERIFY_GROW_STACK: usize = 8 * 1024 * 1024;

use super::build::lower_value_type;
use super::{
    ArenaPrepared, BinderErasure, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType,
    EffectLowered, Elaborated, LoweredType, Owned, ReuseLowered, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};
use crate::core::builtins::Builtin;
use crate::core::{CoreOp, IoOp, NegLane};

/// The declared shape of a data constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorSig {
    quantifiers: Vec<CoreQuantifier>,
    tag: usize,
    fields: Vec<CoreType>,
    result: CoreType,
}

impl ConstructorSig {
    pub(in crate::core) const fn new(
        quantifiers: Vec<CoreQuantifier>,
        tag: usize,
        fields: Vec<CoreType>,
        result: CoreType,
    ) -> Self {
        Self {
            quantifiers,
            tag,
            fields,
            result,
        }
    }

    pub(in crate::core) fn quantifiers(&self) -> &[CoreQuantifier] {
        &self.quantifiers
    }
}

/// The declared signature and owning effect of an operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationSig {
    quantifiers: Vec<CoreQuantifier>,
    params: Vec<CoreType>,
    result: CoreType,
    effect: Label,
}

impl OperationSig {
    pub(in crate::core) const fn new(
        quantifiers: Vec<CoreQuantifier>,
        params: Vec<CoreType>,
        result: CoreType,
        effect: Label,
    ) -> Self {
        Self {
            quantifiers,
            params,
            result,
            effect,
        }
    }

    pub(in crate::core) fn quantifiers(&self) -> &[CoreQuantifier] {
        &self.quantifiers
    }

    pub(in crate::core) fn params(&self) -> &[CoreType] {
        &self.params
    }

    pub(in crate::core) const fn result(&self) -> &CoreType {
        &self.result
    }

    pub(in crate::core) const fn effect(&self) -> &Label {
        &self.effect
    }
}

/// Declarations needed to check Core nodes independently of the producer.
#[derive(Clone, Debug, Default)]
pub struct VerifyEnv {
    constructors: BTreeMap<Sym, ConstructorSig>,
    newtype_constructors: BTreeSet<Sym>,
    operations: BTreeMap<Sym, OperationSig>,
    builtin_overrides: BTreeMap<u64, CoreFnSig>,
}

impl VerifyEnv {
    /// An empty environment, suitable for Core containing only functions and
    /// intrinsic nodes.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            constructors: BTreeMap::new(),
            newtype_constructors: BTreeSet::new(),
            operations: BTreeMap::new(),
            builtin_overrides: BTreeMap::new(),
        }
    }

    pub(in crate::core) fn insert_constructor(&mut self, name: Sym, sig: ConstructorSig) {
        self.constructors.insert(name, sig);
    }

    pub(in crate::core) fn mark_newtype_constructor(&mut self, name: Sym) {
        self.newtype_constructors.insert(name);
    }

    pub(in crate::core) fn insert_operation(&mut self, name: Sym, sig: OperationSig) {
        self.operations.insert(name, sig);
    }

    pub(in crate::core) fn insert_builtin_override(&mut self, op: Builtin, sig: CoreFnSig) {
        self.builtin_overrides.insert(op.wire(), sig);
    }

    pub(in crate::core) fn constructor(&self, name: Sym) -> Option<&ConstructorSig> {
        self.constructors.get(&name)
    }

    pub(in crate::core) fn operation(&self, name: Sym) -> Option<&OperationSig> {
        self.operations.get(&name)
    }

    pub(in crate::core) const fn operations(&self) -> &BTreeMap<Sym, OperationSig> {
        &self.operations
    }

    pub(in crate::core) fn builtin_override(&self, op: Builtin) -> Option<&CoreFnSig> {
        self.builtin_overrides.get(&op.wire())
    }
}

/// One failed typed-Core judgment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreViolation {
    function: Sym,
    path: String,
    message: String,
}

impl CoreViolation {
    /// Function containing the invalid node.
    #[must_use]
    pub const fn function(&self) -> Sym {
        self.function
    }

    /// Stable structural path from the function body to the invalid witness.
    #[must_use]
    pub fn path(&self) -> &str {
        &self.path
    }

    /// Human-readable failed judgment.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for CoreViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}: {}", self.function, self.path, self.message)
    }
}

impl std::error::Error for CoreViolation {}

mod sealed {
    pub trait Sealed {}
}

/// A typed-Core stage with a fixed legal node vocabulary.
pub trait TypedCorePhase: sealed::Sealed {
    #[doc(hidden)]
    const ALLOW_EFFECT_NODES: bool;
    #[doc(hidden)]
    const ALLOW_INIT_AT_NODES: bool;
    #[doc(hidden)]
    const ALLOW_REF_NODES: bool;
    #[doc(hidden)]
    const ALLOW_RC_NODES: bool;
    #[doc(hidden)]
    const ALLOW_REUSE_NODES: bool;
    #[doc(hidden)]
    const ALLOW_LOWERED_ABI: bool;
    #[doc(hidden)]
    const NAME: &'static str;
}

macro_rules! phase {
    ($phase:ty, $name:literal, $effect:literal, $init_at:literal, $refs:literal, $rc:literal, $reuse:literal, $lowered:literal) => {
        impl sealed::Sealed for $phase {}
        impl TypedCorePhase for $phase {
            const ALLOW_EFFECT_NODES: bool = $effect;
            const ALLOW_INIT_AT_NODES: bool = $init_at;
            const ALLOW_REF_NODES: bool = $refs;
            const ALLOW_RC_NODES: bool = $rc;
            const ALLOW_REUSE_NODES: bool = $reuse;
            const ALLOW_LOWERED_ABI: bool = $lowered;
            const NAME: &'static str = $name;
        }
    };
}

phase!(
    Elaborated,
    "elaborated",
    true,
    false,
    false,
    false,
    false,
    false
);
phase!(
    ArenaPrepared,
    "arena-prepared",
    true,
    true,
    false,
    false,
    false,
    false
);
phase!(
    EffectLowered,
    "effect-lowered",
    false,
    true,
    true,
    false,
    false,
    true
);
phase!(Owned, "owned", false, true, true, true, false, true);
phase!(
    ReuseLowered,
    "reuse-lowered",
    false,
    true,
    true,
    true,
    true,
    true
);

/// Check all stored Core judgments without inference or unification.
///
/// # Errors
/// Returns every independently observed violation. Errors at a parent whose
/// premise is already invalid may be omitted to avoid cascading diagnostics.
pub fn verify<P: TypedCorePhase>(
    core: &TypedCore<P>,
    env: &VerifyEnv,
) -> Result<(), Vec<CoreViolation>> {
    let mut globals = BTreeMap::new();
    let mut duplicate_globals = BTreeSet::new();
    for function in core.functions() {
        if globals
            .insert(function.name(), function.sig().clone())
            .is_some()
        {
            duplicate_globals.insert(function.name());
        }
    }

    let mut violations = Vec::new();
    for function in core.functions() {
        let mut checker = Checker::<P>::new(function.name(), env, &globals);
        if duplicate_globals.contains(&function.name()) {
            checker.fail("duplicate global function identity");
        }
        checker.function(function);
        violations.extend(checker.violations);
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

struct Checker<'a, P> {
    function: Sym,
    env: &'a VerifyEnv,
    globals: &'a BTreeMap<Sym, CoreFnSig>,
    locals: BTreeMap<Sym, Vec<CoreType>>,
    token_uses: BTreeMap<Sym, Vec<u8>>,
    token_capacities: BTreeMap<Sym, Vec<usize>>,
    reuse_shells: BTreeMap<Sym, Vec<ReuseShell>>,
    allowed_types: BTreeSet<Sym>,
    allowed_rows: BTreeSet<Sym>,
    path: Vec<String>,
    violations: Vec<CoreViolation>,
    phase: std::marker::PhantomData<P>,
}

impl<'a, P: TypedCorePhase> Checker<'a, P> {
    fn new(function: Sym, env: &'a VerifyEnv, globals: &'a BTreeMap<Sym, CoreFnSig>) -> Self {
        Self {
            function,
            env,
            globals,
            locals: BTreeMap::new(),
            token_uses: BTreeMap::new(),
            token_capacities: BTreeMap::new(),
            reuse_shells: BTreeMap::new(),
            allowed_types: BTreeSet::new(),
            allowed_rows: BTreeSet::new(),
            path: vec!["body".into()],
            violations: Vec::new(),
            phase: std::marker::PhantomData,
        }
    }

    fn fail(&mut self, message: impl Into<String>) {
        self.violations.push(CoreViolation {
            function: self.function,
            path: self.path.join("."),
            message: message.into(),
        });
    }

    fn at(&mut self, segment: impl Into<String>, f: impl FnOnce(&mut Self)) {
        self.path.push(segment.into());
        f(self);
        self.path.pop();
    }

    fn function(&mut self, function: &TypedCoreFn) {
        for quantifier in function.sig().quantifiers() {
            match quantifier {
                CoreQuantifier::Type(name) => {
                    if self.allowed_rows.contains(name) || !self.allowed_types.insert(*name) {
                        self.fail(format!("duplicate type quantifier {name}"));
                    }
                }
                CoreQuantifier::Row(name) => {
                    if self.allowed_types.contains(name) || !self.allowed_rows.insert(*name) {
                        self.fail(format!("duplicate row quantifier {name}"));
                    }
                }
            }
        }
        self.check_fn_sig(function.sig());

        if function.dict_arity() > function.params().len() {
            self.fail(format!(
                "dictionary arity {} exceeds parameter arity {}",
                function.dict_arity(),
                function.params().len()
            ));
        }
        if function.params().len() != function.sig().params().len() {
            self.fail(format!(
                "parameter arity {} does not match signature arity {}",
                function.params().len(),
                function.sig().params().len()
            ));
        }
        let mut parameter_names = BTreeSet::new();
        for (index, parameter) in function.params().iter().enumerate() {
            self.at(format!("param[{index}]"), |this| {
                if let Some(expected) = function.sig().params().get(index) {
                    this.expect_type(parameter.ty(), expected, "parameter witness");
                }
                if !parameter_names.insert(parameter.name()) {
                    this.fail(format!(
                        "binder identity {} is duplicated in the parameter list",
                        parameter.name()
                    ));
                }
                this.bind(parameter);
            });
        }

        self.comp(function.body());
        self.expect_subtype_sig(
            function.body().sig(),
            function.sig().body(),
            "function body",
        );
    }

    fn bind(&mut self, binder: &TypedBinder) {
        if binder.erasure == BinderErasure::RcSequence {
            self.fail("RC sequence witness used outside an administrative dup/drop bind");
        }
        if binder.name() == Sym::new(names::RC_SEQUENCE_BINDER) {
            self.fail("reserved RC sequence identity lacks its erasure witness");
        }
        self.check_core_type(binder.ty());
        self.locals
            .entry(binder.name())
            .or_default()
            .push(binder.ty().clone());
    }

    fn unbind(&mut self, name: Sym) {
        if let Some(stack) = self.locals.get_mut(&name) {
            stack.pop();
            if stack.is_empty() {
                self.locals.remove(&name);
            }
        }
    }

    fn local(&self, name: Sym) -> Option<CoreType> {
        self.locals
            .get(&name)
            .and_then(|stack| stack.last())
            .cloned()
    }

    fn scoped_binders(&mut self, binders: &[&TypedBinder], f: impl FnOnce(&mut Self)) {
        let mut names = BTreeSet::new();
        for binder in binders {
            if !names.insert(binder.name()) {
                self.fail(format!(
                    "binder identity {} is duplicated in one binding group",
                    binder.name()
                ));
            }
            self.bind(binder);
        }
        f(self);
        for binder in binders.iter().rev() {
            self.unbind(binder.name());
        }
    }

    fn value(&mut self, value: &TypedValue) {
        self.check_core_type(value.ty());
        match value.kind() {
            TypedValueKind::Var {
                name,
                instantiation,
            } => {
                if let Some(local) = self.local(*name) {
                    self.check_instantiation(instantiation);
                    let instantiated = if instantiation.is_empty() && value.ty() == &local {
                        Ok(local.clone())
                    } else {
                        instantiate_value_scheme(&local, instantiation)
                    };
                    match instantiated {
                        Ok(instantiated) => {
                            self.expect_type(
                                value.ty(),
                                &instantiated,
                                &format!("local reference `{name}`"),
                            );
                        }
                        Err(message) => {
                            self.fail(format!("invalid local {name} instantiation: {message}"));
                        }
                    }
                    if matches!(local, CoreType::ReuseToken(_)) {
                        self.fail(format!(
                            "reuse token {name} escapes its dedicated reuse operand"
                        ));
                    }
                } else if let Some(global) = self.globals.get(name).cloned() {
                    if let Some(sig) = self.instantiate_fn(&global, instantiation, "global") {
                        self.expect_type(
                            value.ty(),
                            &CoreType::Function(Box::new(sig)),
                            "global function reference",
                        );
                    }
                } else {
                    self.fail(format!("reference {name} is neither local nor global"));
                }
            }
            TypedValueKind::Int(_) => {
                if !matches!(value.ty(), CoreType::Source(Type::Int | Type::Char)) {
                    self.fail(format!("integer literal has witness {:?}", value.ty()));
                }
            }
            TypedValueKind::I64(_) => self.expect_source(value.ty(), &Type::I64, "i64 literal"),
            TypedValueKind::U64(_) => self.expect_source(value.ty(), &Type::U64, "u64 literal"),
            TypedValueKind::Float(_) => {
                self.expect_source(value.ty(), &Type::Float, "float literal");
            }
            TypedValueKind::Bool(_) => self.expect_source(value.ty(), &Type::Bool, "bool literal"),
            TypedValueKind::Unit => self.expect_source(value.ty(), &Type::Unit, "unit literal"),
            TypedValueKind::Str(_) => self.expect_source(value.ty(), &Type::Str, "string literal"),
            TypedValueKind::Reinterpret(inner) => {
                self.at("reinterpret", |this| this.value(inner));
                if !representation_preserving(inner.ty(), value.ty()) {
                    self.fail(format!(
                        "illegal representation-preserving coercion {:?} to {:?}",
                        inner.ty(),
                        value.ty()
                    ));
                }
            }
            TypedValueKind::LoweredRepr {
                value: inner,
                proof,
            } => {
                self.at("lowered-repr", |this| this.value(inner));
                if !P::ALLOW_LOWERED_ABI {
                    self.fail(format!(
                        "lowered representation evidence is not legal in {} Core",
                        P::NAME
                    ));
                }
                if !proof.validates(inner.ty(), value.ty()) {
                    self.fail(format!(
                        "illegal lowered representation conversion {:?} to {:?}",
                        inner.ty(),
                        value.ty()
                    ));
                }
            }
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value: inner,
            } => {
                self.at("newtype-repr", |this| this.value(inner));
                if !self.env.newtype_constructors.contains(constructor) {
                    self.fail(format!(
                        "representation coercion names non-newtype constructor {constructor}"
                    ));
                    return;
                }
                let Some(declared) = self.env.constructors.get(constructor).cloned() else {
                    self.fail(format!(
                        "representation coercion names unknown constructor {constructor}"
                    ));
                    return;
                };
                let Some(instantiated) = self.instantiate_constructor(&declared, instantiation)
                else {
                    return;
                };
                let [field] = instantiated.fields.as_slice() else {
                    self.fail(format!(
                        "newtype constructor {constructor} has {} fields rather than one",
                        instantiated.fields.len()
                    ));
                    return;
                };
                let construction = inner.ty() == field && value.ty() == &instantiated.result;
                let projection = inner.ty() == &instantiated.result && value.ty() == field;
                if !construction && !projection {
                    self.fail(format!(
                        "newtype representation coercion for {constructor} does not connect field {field:?} and result {:?}: inner {:?}, outer {:?}",
                        instantiated.result,
                        inner.ty(),
                        value.ty()
                    ));
                }
            }
            TypedValueKind::Thunk(body) => {
                let token_state = self.token_uses.clone();
                let shell_state = self.reuse_shells.clone();
                let quantifiers = match body.sig().result() {
                    CoreType::Function(signature) => signature.quantifiers().to_vec(),
                    _ => Vec::new(),
                };
                self.scoped_quantifiers(&quantifiers, |this| {
                    this.at("thunk", |this| this.comp(body));
                });
                if self.token_uses != token_state {
                    self.fail("a suspended computation consumes an enclosing reuse token");
                }
                if self.reuse_shells != shell_state {
                    self.fail("a suspended computation frees an enclosing reuse shell");
                }
                self.token_uses = token_state;
                self.reuse_shells = shell_state;
                self.expect_type(
                    value.ty(),
                    &CoreType::Thunk(Box::new(body.sig().clone())),
                    "thunk witness",
                );
            }
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => self.constructor_value(*name, *tag, instantiation, fields, value.ty()),
            TypedValueKind::Tuple(fields) => {
                self.product_value(fields, value.ty(), ProductKind::Tuple);
            }
            TypedValueKind::UnboxedTuple(fields) => {
                self.product_value(fields, value.ty(), ProductKind::UnboxedTuple);
            }
            TypedValueKind::UnboxedRecord(fields) => self.record_value(fields, value.ty()),
        }
    }

    fn constructor_value(
        &mut self,
        name: Sym,
        tag: usize,
        instantiation: &[CoreInstantiation],
        fields: &[TypedValue],
        witness: &CoreType,
    ) {
        let Some(declared) = self.env.constructors.get(&name).cloned() else {
            self.fail(format!("unknown constructor {name}"));
            fields.iter().enumerate().for_each(|(index, field)| {
                self.at(format!("field[{index}]"), |this| this.value(field));
            });
            return;
        };
        let Some(instantiated) = self.instantiate_constructor(&declared, instantiation) else {
            return;
        };
        if tag != instantiated.tag {
            self.fail(format!(
                "constructor {name} tag {tag} does not match declared tag {}",
                instantiated.tag
            ));
        }
        self.values(fields, &instantiated.fields, "constructor field");
        self.expect_type(witness, &instantiated.result, "constructor result");
    }

    fn product_value(&mut self, fields: &[TypedValue], witness: &CoreType, kind: ProductKind) {
        let expected = match witness {
            CoreType::Source(Type::Tuple(types)) if kind == ProductKind::Tuple => Some(types),
            CoreType::Source(Type::UnboxedTuple(types)) if kind == ProductKind::UnboxedTuple => {
                Some(types)
            }
            CoreType::Source(Type::UnboxedRecord(expected))
                if kind == ProductKind::UnboxedTuple =>
            {
                let types: Vec<_> = expected.iter().map(|(_, ty)| ty.clone()).collect();
                self.values(
                    fields,
                    &types.iter().map(lower_value_type).collect::<Vec<_>>(),
                    "product field",
                );
                return;
            }
            _ => None,
        };
        let expected = expected.cloned();
        if let Some(expected) = expected {
            let expected: Vec<_> = expected.iter().map(lower_value_type).collect();
            self.values(fields, &expected, "product field");
        } else {
            self.fail(format!("product shape does not match witness {witness:?}"));
            for (index, field) in fields.iter().enumerate() {
                self.at(format!("field[{index}]"), |this| this.value(field));
            }
        }
    }

    fn record_value(&mut self, fields: &[(Sym, TypedValue)], witness: &CoreType) {
        let Some(expected) = (match witness {
            CoreType::Source(Type::UnboxedRecord(fields)) => Some(fields.clone()),
            _ => None,
        }) else {
            self.fail(format!("unboxed record has non-record witness {witness:?}"));
            for (name, value) in fields {
                self.at(format!("field[{name}]"), |this| this.value(value));
            }
            return;
        };
        if fields.len() != expected.len() {
            self.fail(format!(
                "record field arity {} does not match witness arity {}",
                fields.len(),
                expected.len()
            ));
        }
        for (index, (name, value)) in fields.iter().enumerate() {
            self.at(format!("field[{name}]"), |this| {
                this.value(value);
                if let Some((expected_name, ty)) = expected.get(index) {
                    if name != expected_name {
                        this.fail(format!(
                            "record field {name} does not match witness field {expected_name}"
                        ));
                    }
                    this.expect_type(value.ty(), &lower_value_type(ty), "record field");
                }
            });
        }
    }

    fn comp(&mut self, comp: &TypedComp) {
        // The verifier recurses per typed node; grow stack segments inside the
        // recursion, same discipline as the builder it checks.
        stacker::maybe_grow(VERIFY_MIN_STACK, VERIFY_GROW_STACK, || {
            self.comp_inner(comp);
        });
    }

    #[allow(clippy::too_many_lines)]
    fn comp_inner(&mut self, comp: &TypedComp) {
        self.check_sig(comp.sig());
        match comp.kind() {
            TypedCompKind::Return(value) => {
                self.value(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(value.ty().clone(), EffRow::Empty),
                    "return",
                );
            }
            TypedCompKind::Bind(first, binder, rest) => {
                self.at("first", |this| this.comp(first));
                self.expect_type(binder.ty(), first.sig().result(), "bind binder");
                if binder.erasure == BinderErasure::RcSequence {
                    if !P::ALLOW_RC_NODES {
                        self.fail(format!(
                            "RC sequence witness is illegal in {} Core",
                            P::NAME
                        ));
                    }
                    if binder.name() != Sym::new(names::RC_SEQUENCE_BINDER) {
                        self.fail("RC sequence witness has the wrong reserved identity");
                    }
                    self.expect_type(
                        binder.ty(),
                        &CoreType::Source(Type::Unit),
                        "RC sequence witness",
                    );
                    if !matches!(first.kind(), TypedCompKind::Dup(_) | TypedCompKind::Drop(_)) {
                        self.fail("RC sequence witness does not sequence a dup or drop");
                    }
                    self.check_core_type(binder.ty());
                    self.at("rest", |this| this.comp(rest));
                } else {
                    self.at("rest", |this| {
                        this.scoped_binders(&[binder], |this| this.comp(rest));
                    });
                }
                if let Some(effects) = self.union_rows(
                    first.sig().effects(),
                    rest.sig().effects(),
                    "bind effect union",
                ) {
                    self.expect_subtype_type(comp.sig().result(), rest.sig().result(), "bind");
                    if !row_included(&effects, comp.sig().effects()) {
                        self.fail(format!(
                            "bind row mismatch: stored {}, does not include derived {}",
                            comp.sig().effects().show(),
                            effects.show()
                        ));
                    }
                }
            }
            TypedCompKind::Force(value) => {
                self.value(value);
                match value.ty() {
                    CoreType::Thunk(sig) => {
                        self.expect_subtype_sig(comp.sig(), sig, "force");
                    }
                    other => self.fail(format!("force operand is not a thunk: {other:?}")),
                }
            }
            TypedCompKind::Lam(params, body) => {
                let token_state = self.token_uses.clone();
                let shell_state = self.reuse_shells.clone();
                let Some(signature) = (match comp.sig().result() {
                    CoreType::Function(signature) => Some(signature.as_ref()),
                    other => {
                        self.fail(format!("lambda result is not a function: {other:?}"));
                        None
                    }
                }) else {
                    return;
                };
                self.expect_row(comp.sig().effects(), &EffRow::Empty, "lambda");
                if params.len() != signature.params().len() {
                    self.fail(format!(
                        "lambda parameter arity {} does not match witness arity {}",
                        params.len(),
                        signature.params().len()
                    ));
                }
                self.scoped_quantifiers(signature.quantifiers(), |this| {
                    for (parameter, expected) in params.iter().zip(signature.params()) {
                        this.expect_type(parameter.ty(), expected, "lambda parameter");
                    }
                    this.at("lambda", |this| {
                        let binders: Vec<_> = params.iter().collect();
                        this.scoped_binders(&binders, |this| this.comp(body));
                    });
                    this.expect_subtype_sig(body.sig(), signature.body(), "lambda body");
                });
                if self.token_uses != token_state {
                    self.fail("a function closure consumes an enclosing reuse token");
                }
                if self.reuse_shells != shell_state {
                    self.fail("a function closure frees an enclosing reuse shell");
                }
                self.token_uses = token_state;
                self.reuse_shells = shell_state;
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                self.at("callee", |this| this.comp(callee));
                let Some(signature) = (match callee.sig().result() {
                    CoreType::Function(sig) => {
                        self.instantiate_fn(sig, instantiation, "computed application")
                    }
                    other => {
                        self.fail(format!("application callee is not a function: {other:?}"));
                        None
                    }
                }) else {
                    return;
                };
                self.values(args, signature.params(), "application argument");
                if let Some(effects) = self.union_rows(
                    callee.sig().effects(),
                    signature.body().effects(),
                    "application effect union",
                ) {
                    self.expect_sig(
                        comp.sig(),
                        &CompSig::new(signature.body().result().clone(), effects),
                        "application",
                    );
                }
            }
            TypedCompKind::If(condition, yes, no) => {
                self.value(condition);
                self.expect_source(condition.ty(), &Type::Bool, "if condition");
                let token_state = self.token_uses.clone();
                let shell_state = self.reuse_shells.clone();
                self.at("yes", |this| this.comp(yes));
                let yes_tokens = self.token_uses.clone();
                let yes_shells = self.reuse_shells.clone();
                self.token_uses = token_state;
                self.reuse_shells = shell_state;
                self.at("no", |this| this.comp(no));
                let no_tokens = self.token_uses.clone();
                let no_shells = self.reuse_shells.clone();
                if yes_tokens != no_tokens {
                    self.fail("if branches consume different reuse-token credits");
                }
                self.token_uses = merge_token_states(&yes_tokens, &no_tokens);
                self.reuse_shells = merge_shell_states(&yes_shells, &no_shells);
                self.expect_type(yes.sig().result(), no.sig().result(), "if branch result");
                if let Some(effects) =
                    self.union_rows(yes.sig().effects(), no.sig().effects(), "if effect union")
                {
                    self.expect_sig(
                        comp.sig(),
                        &CompSig::new(yes.sig().result().clone(), effects),
                        "if",
                    );
                }
            }
            TypedCompKind::Prim(op, lhs, rhs) => self.primitive(comp, *op, lhs, rhs),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let Some(declared) = self.globals.get(callee).cloned() else {
                    self.fail(format!("call targets unknown function {callee}"));
                    self.values(args, &[], "call argument");
                    return;
                };
                let Some(signature) = self.instantiate_fn(&declared, instantiation, "call") else {
                    return;
                };
                self.values(args, signature.params(), "call argument");
                self.expect_sig(comp.sig(), signature.body(), "direct call");
            }
            TypedCompKind::Io(op, args) => self.io(comp, *op, args),
            TypedCompKind::Error(value) => {
                self.value(value);
                if !matches!(value.ty(), CoreType::Source(Type::Int | Type::Str)) {
                    self.fail(format!(
                        "error argument has unsupported witness {:?}",
                        value.ty()
                    ));
                }
                // `Core::Error` is an aborting runtime trap, not the source
                // `Exn` effect. Its result and row witnesses are unreachable
                // and therefore inherited from the surrounding computation.
            }
            TypedCompKind::Case(scrutinee, arms) => self.case(comp, scrutinee, arms),
            TypedCompKind::FloatBuiltin(op, value) => {
                self.value(value);
                if let Some(signature) = self.registry_signature(op.signature(), "float builtin") {
                    self.values(
                        std::slice::from_ref(value),
                        signature.params(),
                        "float argument",
                    );
                    self.expect_sig(comp.sig(), signature.body(), "float builtin");
                }
            }
            TypedCompKind::Neg(lane, value) => {
                self.value(value);
                let ty = match lane {
                    NegLane::Int => Type::Int,
                    NegLane::I64 => Type::I64,
                    NegLane::Float => Type::Float,
                };
                self.expect_source(value.ty(), &ty, "negation operand");
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(ty), EffRow::Empty),
                    "negation",
                );
            }
            TypedCompKind::UnboxedProject(value, field) => {
                self.value(value);
                let Some(field_ty) = (match value.ty() {
                    CoreType::Source(Type::UnboxedRecord(fields)) => fields
                        .iter()
                        .find_map(|(name, ty)| (name == field).then(|| ty.clone())),
                    _ => None,
                }) else {
                    self.fail(format!(
                        "field {field} is absent from unboxed-record operand {:?}",
                        value.ty()
                    ));
                    return;
                };
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(lower_value_type(&field_ty), EffRow::Empty),
                    "unboxed projection",
                );
            }
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => self.operation(comp, *operation, instantiation, args),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => self.handle(
                comp,
                body,
                return_binder.as_ref(),
                return_body.as_deref(),
                ops,
            ),
            TypedCompKind::Mask(effects, body) => {
                self.require_effect_node("mask");
                self.at("masked", |this| this.comp(body));
                let residual = subtract_names(body.sig().effects(), effects);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(body.sig().result().clone(), residual),
                    "mask",
                );
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => self.builtin(comp, *op, instantiation, args),
            TypedCompKind::Dup(value) => {
                self.require_rc_node("dup");
                self.value(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    "dup",
                );
            }
            TypedCompKind::Drop(value) => {
                self.require_rc_node("drop");
                self.value(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    "drop",
                );
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                self.require_reuse_node("with-reuse");
                self.value(freed);
                self.expect_type(
                    token.ty(),
                    &CoreType::ReuseToken(Box::new(freed.ty().clone())),
                    "reuse-token binder",
                );
                let capacity = match self.claim_reuse_shell(freed) {
                    Ok(capacity) => capacity,
                    Err(message) => {
                        self.fail(message);
                        0
                    }
                };
                self.token_uses.entry(token.name()).or_default().push(1);
                self.token_capacities
                    .entry(token.name())
                    .or_default()
                    .push(capacity);
                self.at("reuse-body", |this| {
                    this.scoped_binders(&[token], |this| this.comp(body));
                });
                let credit = pop_scoped(&mut self.token_uses, token.name()).unwrap_or(1);
                pop_scoped(&mut self.token_capacities, token.name());
                if credit != 0 {
                    self.fail(format!(
                        "reuse token {} is not consumed exactly once on every path",
                        token.name()
                    ));
                }
                self.expect_sig(comp.sig(), body.sig(), "with-reuse");
            }
            TypedCompKind::Reuse(token, value) => {
                self.require_reuse_node("reuse");
                self.value(value);
                let rebuild_arity = match value.kind() {
                    TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => {
                        Some(fields.len())
                    }
                    _ => {
                        self.fail("reuse rebuild is not a constructor or boxed tuple");
                        None
                    }
                };
                let local = self.local(token.name());
                match local {
                    Some(local) => {
                        self.expect_type(token.ty(), &local, "reuse token reference");
                        if let (Some(arity), Some(capacity)) = (
                            rebuild_arity,
                            self.token_capacities
                                .get(&token.name())
                                .and_then(|capacities| capacities.last())
                                .copied(),
                        ) {
                            if arity > capacity {
                                self.fail(format!(
                                    "reuse rebuild arity {arity} exceeds shell capacity {capacity}"
                                ));
                            }
                        }
                        if let Some(credit) = self
                            .token_uses
                            .get_mut(&token.name())
                            .and_then(|credits| credits.last_mut())
                        {
                            if *credit == 1 {
                                *credit = 0;
                            } else {
                                self.fail(format!(
                                    "reuse token {} is consumed more than once on one path",
                                    token.name()
                                ));
                            }
                        } else {
                            self.fail(format!("{} is not an active reuse token", token.name()));
                        }
                    }
                    None => self.fail(format!("reuse token {} is out of scope", token.name())),
                }
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(value.ty().clone(), EffRow::Empty),
                    "reuse",
                );
            }
            TypedCompKind::InitAt(cell, ctor) => {
                self.require_init_at_node("init-at");
                self.value(cell);
                self.value(ctor);
                // The cell is whatever the checked `alloc` operation hands out,
                // read from the environment rather than named here: the node is
                // a proof that this allocator's cell now holds this
                // constructor, so the two must agree by declaration.
                match self.env.operation(Sym::new(ALLOC_OP)) {
                    Some(alloc) => {
                        let expected = alloc.result().clone();
                        self.expect_type(cell.ty(), &expected, "init-at cell");
                    }
                    None => self.fail("init-at without a declared alloc operation"),
                }
                if !matches!(
                    ctor.kind(),
                    TypedValueKind::Ctor { .. } | TypedValueKind::Tuple(_)
                ) {
                    self.fail("init-at payload is not a constructor or boxed tuple");
                }
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(ctor.ty().clone(), EffRow::Empty),
                    "init-at",
                );
            }
            TypedCompKind::RefNew(value) => {
                self.require_ref_node("ref-new");
                self.value(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Ref(Box::new(value.ty().clone())), EffRow::Empty),
                    "ref-new",
                );
            }
            TypedCompKind::RefGet(value) => {
                self.require_ref_node("ref-get");
                self.value(value);
                match value.ty() {
                    CoreType::Ref(inner) => self.expect_sig(
                        comp.sig(),
                        &CompSig::new(inner.as_ref().clone(), EffRow::Empty),
                        "ref-get",
                    ),
                    other => self.fail(format!("ref-get operand is not a reference: {other:?}")),
                }
            }
            TypedCompKind::RefSet(cell, value) => {
                self.require_ref_node("ref-set");
                self.value(cell);
                self.value(value);
                match cell.ty() {
                    CoreType::Ref(inner) => {
                        self.expect_type(value.ty(), inner, "ref-set value");
                    }
                    other => self.fail(format!("ref-set target is not a reference: {other:?}")),
                }
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    "ref-set",
                );
            }
        }
    }

    fn primitive(&mut self, comp: &TypedComp, op: CoreOp, lhs: &TypedValue, rhs: &TypedValue) {
        use CoreOp::{
            Add, Addf, Div, Divf, Eq, Eqf, Ge, Gef, Gt, Gtf, Le, Lef, Lt, Ltf, Mul, Mulf, Ne, Nef,
            Rem, Sub, Subf,
        };
        self.value(lhs);
        self.value(rhs);
        let (operand, result) = match op {
            Add | Sub | Mul | Div | Rem => (CoreType::Source(Type::Int), Type::Int),
            Addf | Subf | Mulf | Divf => (CoreType::Source(Type::Float), Type::Float),
            Eqf | Nef | Ltf | Lef | Gtf | Gef => (CoreType::Source(Type::Float), Type::Bool),
            Eq | Ne | Lt | Le | Gt | Ge => {
                if lhs.ty() != rhs.ty()
                    || !matches!(
                        lhs.ty(),
                        CoreType::Source(Type::Int | Type::Bool | Type::Char)
                    )
                {
                    self.fail(format!(
                        "integer-lane comparison has operands {:?} and {:?}",
                        lhs.ty(),
                        rhs.ty()
                    ));
                }
                (lhs.ty().clone(), Type::Bool)
            }
        };
        self.expect_type(lhs.ty(), &operand, "primitive lhs");
        self.expect_type(rhs.ty(), &operand, "primitive rhs");
        self.expect_sig(
            comp.sig(),
            &CompSig::new(CoreType::Source(result), EffRow::Empty),
            "primitive",
        );
    }

    fn io(&mut self, comp: &TypedComp, op: IoOp, args: &[TypedValue]) {
        if args.len() != op.arity() {
            self.fail(format!(
                "I/O argument arity {} does not match expected arity {}",
                args.len(),
                op.arity()
            ));
        }
        for (index, argument) in args.iter().enumerate() {
            self.at(format!("arg[{index}]"), |this| this.value(argument));
        }
        if let Some(argument) = args.first() {
            match op {
                // The raw printer is the lowering of `forall a. (a) -> Unit`;
                // concrete Float/String sites use their specialized nodes while
                // a rigid polymorphic value legitimately remains arbitrary.
                IoOp::PrintF => {
                    self.expect_source(argument.ty(), &Type::Float, "float print argument");
                }
                IoOp::PrintS => {
                    self.expect_source(argument.ty(), &Type::Str, "string print argument");
                }
                IoOp::Srand => {
                    self.expect_source(argument.ty(), &Type::Int, "random seed argument");
                }
                IoOp::Print | IoOp::PrintNl | IoOp::ReadInt | IoOp::ReadLine | IoOp::Rand => {}
            }
        }
        let result = match op {
            IoOp::ReadInt | IoOp::Rand => Type::Int,
            IoOp::ReadLine => Type::Str,
            IoOp::Print | IoOp::PrintF | IoOp::PrintS | IoOp::PrintNl | IoOp::Srand => Type::Unit,
        };
        self.expect_sig(
            comp.sig(),
            &CompSig::new(CoreType::Source(result), EffRow::singleton(IO_EFFECT)),
            "I/O operation",
        );
    }

    fn case(
        &mut self,
        comp: &TypedComp,
        scrutinee: &TypedValue,
        arms: &[(TypedPattern, TypedComp)],
    ) {
        self.value(scrutinee);
        if arms.is_empty() {
            self.fail("case has no arms");
            return;
        }
        let mut effects = EffRow::Empty;
        let token_state = self.token_uses.clone();
        let shell_state = self.reuse_shells.clone();
        let mut merged_tokens = None;
        let mut merged_shells = None;
        for (index, (pattern, body)) in arms.iter().enumerate() {
            self.token_uses = token_state.clone();
            self.reuse_shells = shell_state.clone();
            self.at(format!("arm[{index}]"), |this| {
                let binders = this.pattern(pattern, scrutinee.ty());
                let shell = this.case_reuse_shell(scrutinee, pattern);
                let pushes_shell = shell.as_ref().is_some_and(|(name, shell)| {
                    !this.reuse_shells.get(name).is_some_and(|shells| {
                        shells
                            .last()
                            .is_some_and(|active| active.binding_depth == shell.binding_depth)
                    })
                });
                if pushes_shell {
                    if let Some((name, shell)) = &shell {
                        this.reuse_shells
                            .entry(*name)
                            .or_default()
                            .push(shell.clone());
                    }
                }
                let refs: Vec<_> = binders.iter().collect();
                this.scoped_binders(&refs, |this| this.comp(body));
                if pushes_shell {
                    if let Some((name, _)) = shell {
                        pop_scoped(&mut this.reuse_shells, name);
                    }
                }
                this.expect_subtype_type(
                    body.sig().result(),
                    comp.sig().result(),
                    "case arm result",
                );
            });
            let arm_tokens = self.token_uses.clone();
            let arm_shells = self.reuse_shells.clone();
            if let Some(previous) = &merged_tokens {
                if previous != &arm_tokens {
                    self.fail("case arms consume different reuse-token credits");
                }
                merged_tokens = Some(merge_token_states(previous, &arm_tokens));
            } else {
                merged_tokens = Some(arm_tokens);
            }
            merged_shells = Some(match &merged_shells {
                Some(previous) => merge_shell_states(previous, &arm_shells),
                None => arm_shells,
            });
            if let Some(union) =
                self.union_rows(&effects, body.sig().effects(), "case effect union")
            {
                effects = union;
            }
        }
        self.token_uses = merged_tokens.unwrap_or(token_state);
        self.reuse_shells = merged_shells.unwrap_or(shell_state);
        self.expect_row(comp.sig().effects(), &effects, "case effects");
    }

    fn case_reuse_shell(
        &self,
        scrutinee: &TypedValue,
        pattern: &TypedPattern,
    ) -> Option<(Sym, ReuseShell)> {
        // A constructor arm supplies boxed-shell authority even when its
        // scrutinee belongs to the lowered effect representation. Tuple syntax
        // also covers unboxed products, so only a source boxed tuple qualifies.
        let capacity = match (pattern, scrutinee.ty()) {
            (TypedPattern::Ctor { fields, .. }, _)
            | (TypedPattern::Tuple(fields), CoreType::Source(Type::Tuple(_))) => fields.len(),
            _ => return None,
        };
        let TypedValueKind::Var { name, .. } = scrutinee.kind() else {
            return None;
        };
        let binding_depth = self.locals.get(name)?.len();
        Some((
            *name,
            ReuseShell {
                scrutinee: scrutinee.clone(),
                binding_depth,
                capacity,
                remaining: 1,
            },
        ))
    }

    fn claim_reuse_shell(&mut self, freed: &TypedValue) -> Result<usize, &'static str> {
        let TypedValueKind::Var { name, .. } = freed.kind() else {
            return Err("with-reuse does not free the active boxed case scrutinee");
        };
        let binding_depth = self.locals.get(name).map_or(0, Vec::len);
        let Some(shell) = self
            .reuse_shells
            .get_mut(name)
            .and_then(|shells| shells.last_mut())
            .filter(|shell| shell.scrutinee == *freed && shell.binding_depth == binding_depth)
        else {
            return Err("with-reuse does not free the active boxed case scrutinee");
        };
        if shell.remaining == 0 {
            return Err("the active boxed case scrutinee is freed more than once on one path");
        }
        shell.remaining = 0;
        Ok(shell.capacity)
    }

    fn pattern(&mut self, pattern: &TypedPattern, scrutinee: &CoreType) -> Vec<TypedBinder> {
        match pattern {
            TypedPattern::Wild => Vec::new(),
            TypedPattern::Var(binder) => {
                self.expect_type(binder.ty(), scrutinee, "pattern binder");
                vec![binder.clone()]
            }
            TypedPattern::Tuple(fields) => {
                let expected = match scrutinee {
                    CoreType::Source(Type::Tuple(types) | Type::UnboxedTuple(types)) => {
                        Some(types.clone())
                    }
                    CoreType::Source(Type::UnboxedRecord(fields)) => {
                        Some(fields.iter().map(|(_, ty)| ty.clone()).collect())
                    }
                    _ => None,
                };
                let Some(expected) = expected else {
                    self.fail(format!(
                        "tuple pattern has non-product scrutinee {scrutinee:?}"
                    ));
                    return fields.iter().filter_map(Clone::clone).collect();
                };
                self.pattern_fields(fields, &expected)
            }
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => {
                let Some(declared) = self.env.constructors.get(name).cloned() else {
                    self.fail(format!("pattern names unknown constructor {name}"));
                    return fields.iter().filter_map(Clone::clone).collect();
                };
                let Some(instantiated) = self.instantiate_constructor(&declared, instantiation)
                else {
                    return fields.iter().filter_map(Clone::clone).collect();
                };
                self.expect_type(
                    scrutinee,
                    &instantiated.result,
                    "constructor pattern result",
                );
                if fields.len() != instantiated.fields.len() {
                    self.fail(format!(
                        "constructor pattern arity {} does not match declared arity {}",
                        fields.len(),
                        instantiated.fields.len()
                    ));
                }
                let mut binders = Vec::new();
                for (index, binder) in fields.iter().enumerate() {
                    if let Some(binder) = binder {
                        if let Some(expected) = instantiated.fields.get(index) {
                            self.expect_type(binder.ty(), expected, "constructor pattern field");
                        }
                        binders.push(binder.clone());
                    }
                }
                binders
            }
        }
    }

    fn pattern_fields(
        &mut self,
        fields: &[Option<TypedBinder>],
        expected: &[Type],
    ) -> Vec<TypedBinder> {
        if fields.len() != expected.len() {
            self.fail(format!(
                "tuple pattern arity {} does not match scrutinee arity {}",
                fields.len(),
                expected.len()
            ));
        }
        fields
            .iter()
            .enumerate()
            .filter_map(|(index, binder)| {
                binder.as_ref().map(|binder| {
                    if let Some(expected) = expected.get(index) {
                        self.expect_type(
                            binder.ty(),
                            &lower_value_type(expected),
                            "tuple pattern field",
                        );
                    }
                    binder.clone()
                })
            })
            .collect()
    }

    fn operation(
        &mut self,
        comp: &TypedComp,
        name: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
    ) {
        self.require_effect_node("operation");
        let Some(declared) = self.env.operations.get(&name).cloned() else {
            self.fail(format!("unknown effect operation {name}"));
            return;
        };
        let Some(instantiated) = self.instantiate_operation(&declared, instantiation) else {
            return;
        };
        self.values(args, &instantiated.params, "operation argument");
        self.expect_sig(
            comp.sig(),
            &CompSig::new(
                instantiated.result,
                EffRow::canonical([instantiated.effect], EffRow::Empty),
            ),
            "effect operation",
        );
    }

    fn handle(
        &mut self,
        comp: &TypedComp,
        body: &TypedComp,
        return_binder: Option<&TypedBinder>,
        return_body: Option<&TypedComp>,
        handler: &TypedHandler,
    ) {
        self.require_effect_node("handler");
        self.at("handled", |this| this.comp(body));
        let arms = handler.arms();
        if return_binder.is_some() != return_body.is_some() {
            self.fail("handler return binder and return body must appear together");
        }

        let mut clause_effects =
            if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
                self.expect_type(binder.ty(), body.sig().result(), "handler return binder");
                self.at("return", |this| {
                    this.scoped_binders(&[binder], |this| this.comp(return_body));
                });
                self.expect_subtype_type(
                    return_body.sig().result(),
                    comp.sig().result(),
                    "handler return result",
                );
                return_body.sig().effects().clone()
            } else {
                self.expect_type(
                    body.sig().result(),
                    comp.sig().result(),
                    "handler identity return",
                );
                EffRow::Empty
            };

        let mut instantiated_arms = BTreeMap::new();
        for (index, arm) in arms.iter().enumerate() {
            self.at(format!("op[{}]", arm.name()), |this| {
                let Some(declared) = this.env.operations.get(&arm.name()).cloned() else {
                    this.fail(format!("handler names unknown operation {}", arm.name()));
                    return;
                };
                let Some(operation) = this.instantiate_operation(&declared, arm.instantiation())
                else {
                    return;
                };
                this.check_handler_arm(arm, &operation, comp.sig());
                instantiated_arms.insert(arm.name(), operation.effect.clone());
            });
            if let Some(union) = self.union_rows(
                &clause_effects,
                arm.body().sig().effects(),
                "handler clause effect union",
            ) {
                clause_effects = union;
            }
            let _ = index;
        }

        let expected_forwarding = self.residual_forwarding(&instantiated_arms);
        let stored_forwarding: Vec<_> = handler
            .forwarded()
            .iter()
            .map(|forward| (forward.operation(), forward.effect().clone()))
            .collect();
        if stored_forwarding != expected_forwarding {
            self.fail(format!(
                "handler residual-forwarding witness mismatch: derived {expected_forwarding:?}, stored {stored_forwarding:?}"
            ));
        }

        let discharged = self.exhaustively_handled_labels(body.sig().effects(), &instantiated_arms);
        let residual = subtract_labels(body.sig().effects(), &discharged);
        if let Some(effects) = self.union_rows(&residual, &clause_effects, "handler effect union") {
            if !row_included(&effects, comp.sig().effects()) {
                self.fail(format!(
                    "handler residual effects row mismatch: derived {}, stored upper bound {}",
                    effects.show(),
                    comp.sig().effects().show()
                ));
            }
        }
    }

    fn residual_forwarding(&self, arms: &BTreeMap<Sym, Label>) -> Vec<(Sym, Label)> {
        let effects: BTreeMap<Sym, Label> = arms
            .values()
            .map(|label| (label.name, label.clone()))
            .collect();
        self.env
            .operations
            .iter()
            .filter_map(|(operation, declared)| {
                effects
                    .get(&declared.effect.name)
                    .filter(|_| !arms.contains_key(operation))
                    .cloned()
                    .map(|effect| (*operation, effect))
            })
            .collect()
    }

    fn check_handler_arm(
        &mut self,
        arm: &TypedHandleOp,
        operation: &MonoOperation,
        outer: &CompSig,
    ) {
        if arm.params().len() != operation.params.len() {
            self.fail(format!(
                "operation arm arity {} does not match declared arity {}",
                arm.params().len(),
                operation.params.len()
            ));
        }
        for (binder, expected) in arm.params().iter().zip(&operation.params) {
            self.expect_type(binder.ty(), expected, "operation arm parameter");
        }
        let resume = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![operation.result.clone()],
                outer.clone(),
            ))),
            EffRow::Empty,
        )));
        self.expect_type(arm.resume().ty(), &resume, "operation resumption");
        let mut binders: Vec<_> = arm.params().iter().collect();
        binders.push(arm.resume());
        self.scoped_binders(&binders, |this| this.comp(arm.body()));
        self.expect_subtype_type(
            arm.body().sig().result(),
            outer.result(),
            "operation arm result",
        );
    }

    fn exhaustively_handled_labels(
        &self,
        body: &EffRow,
        arms: &BTreeMap<Sym, Label>,
    ) -> BTreeSet<Label> {
        body.labels()
            .into_iter()
            .filter(|label| {
                let declared: Vec<_> = self
                    .env
                    .operations
                    .iter()
                    .filter(|(_, operation)| operation.effect.name == label.name)
                    .map(|(name, _)| *name)
                    .collect();
                !declared.is_empty()
                    && declared
                        .iter()
                        .all(|name| arms.get(name).is_some_and(|handled| handled == *label))
            })
            .cloned()
            .collect()
    }

    fn builtin(
        &mut self,
        comp: &TypedComp,
        op: Builtin,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
    ) {
        let declared = if matches!(op, Builtin::I64Add | Builtin::I64Sub | Builtin::I64Mul)
            && comp.sig().result() == &CoreType::Source(Type::U64)
        {
            self.registry_signature("(U64, U64) -> U64", "unsigned shared-lane builtin")
        } else if let Some(signature) = op.signature() {
            self.registry_signature(signature, "builtin")
        } else {
            self.env
                .builtin_overrides
                .get(&op.wire())
                .cloned()
                .or_else(|| {
                    self.fail(format!(
                        "elaborator-only builtin {} has no verifier signature override",
                        op.name()
                    ));
                    None
                })
        };
        let Some(declared) = declared else {
            return;
        };
        let Some(signature) = self.instantiate_fn(&declared, instantiation, "builtin") else {
            return;
        };
        self.values(args, signature.params(), "builtin argument");
        self.expect_sig(comp.sig(), signature.body(), "builtin");
    }

    fn registry_signature(&mut self, text: &str, context: &str) -> Option<CoreFnSig> {
        match crate::tc::parse_checked_signature("typed-core verifier", text) {
            Ok(ty) => match scheme_to_fn_sig(ty) {
                Ok(signature) => Some(signature),
                Err(message) => {
                    self.fail(format!("invalid canonical {context} signature: {message}"));
                    None
                }
            },
            Err(error) => {
                self.fail(format!(
                    "cannot parse canonical {context} signature: {error}"
                ));
                None
            }
        }
    }

    fn values(&mut self, values: &[TypedValue], expected: &[CoreType], context: &str) {
        if values.len() != expected.len() {
            self.fail(format!(
                "{context} arity {} does not match expected arity {}",
                values.len(),
                expected.len()
            ));
        }
        for (index, value) in values.iter().enumerate() {
            self.at(format!("arg[{index}]"), |this| {
                this.value(value);
                if let Some(expected) = expected.get(index) {
                    this.expect_subtype_type(value.ty(), expected, context);
                }
            });
        }
    }

    fn instantiate_fn(
        &mut self,
        signature: &CoreFnSig,
        arguments: &[CoreInstantiation],
        context: &str,
    ) -> Option<CoreFnSig> {
        self.check_instantiation(arguments);
        match instantiate_fn(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(message) => {
                self.fail(format!("invalid {context} instantiation: {message}"));
                None
            }
        }
    }

    fn instantiate_constructor(
        &mut self,
        signature: &ConstructorSig,
        arguments: &[CoreInstantiation],
    ) -> Option<MonoConstructor> {
        self.check_instantiation(arguments);
        match instantiate_constructor(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(message) => {
                self.fail(format!("invalid constructor instantiation: {message}"));
                None
            }
        }
    }

    fn instantiate_operation(
        &mut self,
        signature: &OperationSig,
        arguments: &[CoreInstantiation],
    ) -> Option<MonoOperation> {
        self.check_instantiation(arguments);
        match instantiate_operation(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(message) => {
                self.fail(format!("invalid operation instantiation: {message}"));
                None
            }
        }
    }

    fn expect_source(&mut self, actual: &CoreType, expected: &Type, context: &str) {
        self.expect_type(actual, &CoreType::Source(expected.clone()), context);
    }

    fn check_instantiation(&mut self, arguments: &[CoreInstantiation]) {
        for argument in arguments {
            match argument {
                CoreInstantiation::Type(ty) => self.check_source_type(ty),
                CoreInstantiation::Row(row) => self.check_row(row),
            }
        }
    }

    fn expect_type(&mut self, actual: &CoreType, expected: &CoreType, context: &str) {
        if actual != expected {
            self.fail(format!(
                "{context} type mismatch: stored {actual:?}, expected {expected:?}"
            ));
        }
    }

    fn expect_subtype_type(&mut self, actual: &CoreType, expected: &CoreType, context: &str) {
        if !core_subtype(actual, expected) {
            self.fail(format!(
                "{context} type mismatch: stored {actual:?}, expected a subtype of {expected:?}"
            ));
        }
    }

    fn expect_row(&mut self, actual: &EffRow, expected: &EffRow, context: &str) {
        if actual != expected {
            self.fail(format!(
                "{context} row mismatch: stored {}, expected {}",
                actual.show(),
                expected.show()
            ));
        }
    }

    fn expect_sig(&mut self, actual: &CompSig, expected: &CompSig, context: &str) {
        self.expect_type(actual.result(), expected.result(), context);
        self.expect_row(actual.effects(), expected.effects(), context);
    }

    fn expect_subtype_sig(&mut self, actual: &CompSig, expected: &CompSig, context: &str) {
        self.expect_subtype_type(actual.result(), expected.result(), context);
        if !row_included(actual.effects(), expected.effects()) {
            self.fail(format!(
                "{context} row mismatch: stored {}, expected a subrow of {}",
                actual.effects().show(),
                expected.effects().show()
            ));
        }
    }

    fn scoped_quantifiers(&mut self, quantifiers: &[CoreQuantifier], f: impl FnOnce(&mut Self)) {
        let old_types = self.allowed_types.clone();
        let old_rows = self.allowed_rows.clone();
        for quantifier in quantifiers {
            match quantifier {
                CoreQuantifier::Type(name) => {
                    self.allowed_types.insert(*name);
                }
                CoreQuantifier::Row(name) => {
                    self.allowed_rows.insert(*name);
                }
            }
        }
        f(self);
        self.allowed_types = old_types;
        self.allowed_rows = old_rows;
    }

    fn union_rows(&mut self, left: &EffRow, right: &EffRow, context: &str) -> Option<EffRow> {
        match union_rows(left, right) {
            Ok(row) => Some(row),
            Err(message) => {
                self.fail(format!("{context}: {message}"));
                None
            }
        }
    }

    fn check_fn_sig(&mut self, signature: &CoreFnSig) {
        for parameter in signature.params() {
            self.check_core_type(parameter);
        }
        self.check_sig(signature.body());
    }

    fn check_sig(&mut self, signature: &CompSig) {
        self.check_core_type(signature.result());
        self.check_row(signature.effects());
    }

    fn check_core_type(&mut self, ty: &CoreType) {
        match ty {
            CoreType::Source(ty) => self.check_source_type(ty),
            CoreType::Thunk(signature) => self.check_sig(signature),
            CoreType::Function(signature) => {
                let old_types = self.allowed_types.clone();
                let old_rows = self.allowed_rows.clone();
                let mut local_types = BTreeSet::new();
                let mut local_rows = BTreeSet::new();
                for quantifier in signature.quantifiers() {
                    match quantifier {
                        CoreQuantifier::Type(name) => {
                            if local_rows.contains(name) || !local_types.insert(*name) {
                                self.fail(format!("duplicate nested type quantifier {name}"));
                            }
                            self.allowed_types.insert(*name);
                        }
                        CoreQuantifier::Row(name) => {
                            if local_types.contains(name) || !local_rows.insert(*name) {
                                self.fail(format!("duplicate nested row quantifier {name}"));
                            }
                            self.allowed_rows.insert(*name);
                        }
                    }
                }
                self.check_fn_sig(signature);
                self.allowed_types = old_types;
                self.allowed_rows = old_rows;
            }
            CoreType::Ref(inner) | CoreType::ReuseToken(inner) => self.check_core_type(inner),
            CoreType::Lowered(kind) => {
                if !P::ALLOW_LOWERED_ABI {
                    self.fail(format!("lowered ABI type is not legal in {} Core", P::NAME));
                }
                match kind {
                    LoweredType::Word => {}
                    LoweredType::Eff(row)
                    | LoweredType::Queue(row)
                    | LoweredType::QueueView(row) => self.check_row(row),
                }
            }
        }
    }

    fn check_source_type(&mut self, ty: &Type) {
        let mut existentials = BTreeSet::new();
        ty.free_exist(&mut existentials);
        if !existentials.is_empty() {
            self.fail(format!("unsolved type metavariables survive in {ty:?}"));
        }
        let mut row_existentials = BTreeSet::new();
        ty.free_exist_row(&mut row_existentials);
        if !row_existentials.is_empty() {
            self.fail(format!("unsolved row metavariables survive in {ty:?}"));
        }
        let mut type_variables = BTreeSet::new();
        ty.free_ty_vars(&mut type_variables);
        let unbound_types: Vec<_> = type_variables
            .difference(&self.allowed_types)
            .copied()
            .collect();
        for name in unbound_types {
            self.fail(format!("unbound rigid type variable {name} in {ty:?}"));
        }
        let mut row_variables = BTreeSet::new();
        ty.free_row_vars(&mut row_variables);
        let unbound_rows: Vec<_> = row_variables
            .difference(&self.allowed_rows)
            .copied()
            .collect();
        for name in unbound_rows {
            self.fail(format!("unbound rigid row variable {name} in {ty:?}"));
        }
        check_type_rows(ty, &mut |row| self.check_row(row));
    }

    fn check_row(&mut self, row: &EffRow) {
        if !row.is_canonical() {
            self.fail(format!("effect row is not canonical: {row:?}"));
        }
        let mut exists = BTreeSet::new();
        row.free_exist_row(&mut exists);
        if !exists.is_empty() {
            self.fail(format!(
                "unsolved effect-row metavariables survive in {row:?}"
            ));
        }
        if let EffRow::Var(name) = row.tail() {
            if !self.allowed_rows.contains(name) {
                self.fail(format!("unbound rigid effect-row variable {name}"));
            }
        }
        for label in row.labels() {
            for argument in &label.args {
                self.check_source_type(argument);
            }
        }
    }

    fn require_effect_node(&mut self, node: &str) {
        if !P::ALLOW_EFFECT_NODES {
            self.fail(format!("{node} node is illegal in {} Core", P::NAME));
        }
    }

    fn require_init_at_node(&mut self, node: &str) {
        if !P::ALLOW_INIT_AT_NODES {
            self.fail(format!("{node} node is illegal in {} Core", P::NAME));
        }
    }

    fn require_ref_node(&mut self, node: &str) {
        if !P::ALLOW_REF_NODES {
            self.fail(format!("{node} node is illegal in {} Core", P::NAME));
        }
    }

    fn require_rc_node(&mut self, node: &str) {
        if !P::ALLOW_RC_NODES {
            self.fail(format!("{node} node is illegal in {} Core", P::NAME));
        }
    }

    fn require_reuse_node(&mut self, node: &str) {
        if !P::ALLOW_REUSE_NODES {
            self.fail(format!("{node} node is illegal in {} Core", P::NAME));
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ReuseShell {
    scrutinee: TypedValue,
    binding_depth: usize,
    capacity: usize,
    remaining: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProductKind {
    Tuple,
    UnboxedTuple,
}

#[derive(Clone)]
pub(in crate::core) struct MonoConstructor {
    pub(in crate::core) tag: usize,
    pub(in crate::core) fields: Vec<CoreType>,
    pub(in crate::core) result: CoreType,
}

#[derive(Clone)]
pub(in crate::core) struct MonoOperation {
    pub(in crate::core) params: Vec<CoreType>,
    pub(in crate::core) result: CoreType,
    pub(in crate::core) effect: Label,
}

pub(in crate::core) fn scheme_to_fn_sig(mut ty: Type) -> Result<CoreFnSig, String> {
    let mut quantifiers = Vec::new();
    loop {
        match ty {
            Type::Forall(name, body) => {
                quantifiers.push(CoreQuantifier::Type(name));
                ty = *body;
            }
            Type::RowForall(name, body) => {
                quantifiers.push(CoreQuantifier::Row(name));
                ty = *body;
            }
            Type::Fun(params, effects, result) => {
                return Ok(CoreFnSig::new(
                    quantifiers,
                    params.iter().map(lower_value_type).collect(),
                    CompSig::new(lower_value_type(&result), effects),
                ));
            }
            other => return Err(format!("expected a function scheme, got {other:?}")),
        }
    }
}

pub(in crate::core) fn instantiate_fn(
    signature: &CoreFnSig,
    arguments: &[CoreInstantiation],
) -> Result<CoreFnSig, String> {
    require_instantiation(signature.quantifiers(), arguments)?;
    let params = signature
        .params()
        .iter()
        .map(|ty| substitute_core_type(ty, signature.quantifiers(), arguments))
        .collect();
    let body = substitute_sig(signature.body(), signature.quantifiers(), arguments);
    Ok(CoreFnSig::new(Vec::new(), params, body))
}

pub(in crate::core) fn instantiate_value_scheme(
    ty: &CoreType,
    arguments: &[CoreInstantiation],
) -> Result<CoreType, String> {
    match ty {
        CoreType::Function(signature) => instantiate_fn(signature, arguments)
            .map(|signature| CoreType::Function(Box::new(signature))),
        CoreType::Thunk(suspension) => {
            let CoreType::Function(signature) = suspension.result() else {
                require_instantiation(&[], arguments)?;
                return Ok(ty.clone());
            };
            let signature = instantiate_fn(signature, arguments)?;
            Ok(CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(signature)),
                suspension.effects().clone(),
            ))))
        }
        _ => {
            require_instantiation(&[], arguments)?;
            Ok(ty.clone())
        }
    }
}

pub(in crate::core) fn instantiate_constructor(
    signature: &ConstructorSig,
    arguments: &[CoreInstantiation],
) -> Result<MonoConstructor, String> {
    require_instantiation(&signature.quantifiers, arguments)?;
    Ok(MonoConstructor {
        tag: signature.tag,
        fields: signature
            .fields
            .iter()
            .map(|ty| substitute_core_type(ty, &signature.quantifiers, arguments))
            .collect(),
        result: substitute_core_type(&signature.result, &signature.quantifiers, arguments),
    })
}

pub(in crate::core) fn instantiate_operation(
    signature: &OperationSig,
    arguments: &[CoreInstantiation],
) -> Result<MonoOperation, String> {
    require_instantiation(&signature.quantifiers, arguments)?;
    Ok(MonoOperation {
        params: signature
            .params
            .iter()
            .map(|ty| substitute_core_type(ty, &signature.quantifiers, arguments))
            .collect(),
        result: substitute_core_type(&signature.result, &signature.quantifiers, arguments),
        effect: substitute_label(&signature.effect, &signature.quantifiers, arguments),
    })
}

fn require_instantiation(
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Result<(), String> {
    if quantifiers.len() != arguments.len() {
        return Err(format!(
            "argument count {} does not match quantifier count {}",
            arguments.len(),
            quantifiers.len()
        ));
    }
    for (index, (quantifier, argument)) in quantifiers.iter().zip(arguments).enumerate() {
        if !matches!(
            (quantifier, argument),
            (CoreQuantifier::Type(_), CoreInstantiation::Type(_))
                | (CoreQuantifier::Row(_), CoreInstantiation::Row(_))
        ) {
            return Err(format!("argument {index} has the wrong kind"));
        }
    }
    Ok(())
}

pub(in crate::core) fn substitute_core_type(
    ty: &CoreType,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreType {
    match ty {
        CoreType::Source(ty) => lower_value_type(&substitute_type(ty, quantifiers, arguments)),
        CoreType::Thunk(signature) => {
            CoreType::Thunk(Box::new(substitute_sig(signature, quantifiers, arguments)))
        }
        CoreType::Function(signature) => CoreType::Function(Box::new(substitute_fn_sig(
            signature,
            quantifiers,
            arguments,
        ))),
        CoreType::Ref(inner) => CoreType::Ref(Box::new(substitute_core_type(
            inner,
            quantifiers,
            arguments,
        ))),
        CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(substitute_core_type(
            inner,
            quantifiers,
            arguments,
        ))),
        CoreType::Lowered(kind) => CoreType::Lowered(match kind {
            LoweredType::Word => LoweredType::Word,
            LoweredType::Eff(row) => LoweredType::Eff(substitute_row(row, quantifiers, arguments)),
            LoweredType::Queue(row) => {
                LoweredType::Queue(substitute_row(row, quantifiers, arguments))
            }
            LoweredType::QueueView(row) => {
                LoweredType::QueueView(substitute_row(row, quantifiers, arguments))
            }
        }),
    }
}

pub(super) fn substitute_fn_sig(
    signature: &CoreFnSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CoreFnSig {
    // Drop substitutions shadowed by the signature's own quantifiers FIRST. A
    // shadowed outer quantifier is not substituted into this inner scope, so its
    // argument must not drive capture-avoidance: otherwise an inner rank-2 binder
    // that deliberately reuses an outer quantifier's name (a state-fusion
    // producer thunk) is spuriously renamed out of sync with its references.
    let shadowed: BTreeSet<_> = signature
        .quantifiers()
        .iter()
        .map(|quantifier| match quantifier {
            CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => *name,
        })
        .collect();
    let (quantifiers, arguments): (Vec<_>, Vec<_>) = quantifiers
        .iter()
        .zip(arguments)
        .filter(|(quantifier, _)| match quantifier {
            CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => !shadowed.contains(name),
        })
        .map(|(quantifier, argument)| (quantifier.clone(), argument.clone()))
        .unzip();

    let mut inserted_types = BTreeSet::new();
    let mut inserted_rows = BTreeSet::new();
    for argument in &arguments {
        match argument {
            CoreInstantiation::Type(ty) => {
                ty.free_ty_vars(&mut inserted_types);
                ty.free_row_vars(&mut inserted_rows);
            }
            CoreInstantiation::Row(row) => {
                if let EffRow::Var(name) = row.tail() {
                    inserted_rows.insert(*name);
                }
                for label in row.labels() {
                    for argument in &label.args {
                        argument.free_ty_vars(&mut inserted_types);
                        argument.free_row_vars(&mut inserted_rows);
                    }
                }
            }
        }
    }
    let mut signature = signature.clone();
    for index in 0..signature.quantifiers().len() {
        let quantifier = signature.quantifiers()[index].clone();
        let collision = match quantifier {
            CoreQuantifier::Type(name) => inserted_types.contains(&name),
            CoreQuantifier::Row(name) => inserted_rows.contains(&name),
        };
        if collision {
            let name = match quantifier {
                CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => name,
            };
            let mut suffix = 0;
            let fresh = loop {
                let candidate = Sym::from(format!("{name}$typedq{suffix}"));
                suffix += 1;
                if !inserted_types.contains(&candidate)
                    && !inserted_rows.contains(&candidate)
                    && !signature.quantifiers().iter().any(|quantifier| {
                        matches!(
                            quantifier,
                            CoreQuantifier::Type(bound) | CoreQuantifier::Row(bound)
                                if *bound == candidate
                        )
                    })
                {
                    break candidate;
                }
            };
            signature = rename_fn_quantifier(&signature, index, fresh);
        }
    }

    CoreFnSig::new(
        signature.quantifiers().to_vec(),
        signature
            .params()
            .iter()
            .map(|ty| substitute_core_type(ty, &quantifiers, &arguments))
            .collect(),
        substitute_sig(signature.body(), &quantifiers, &arguments),
    )
}

fn rename_fn_quantifier(signature: &CoreFnSig, index: usize, fresh: Sym) -> CoreFnSig {
    let old = signature.quantifiers()[index].clone();
    let mut quantifiers = signature.quantifiers().to_vec();
    quantifiers[index] = match old {
        CoreQuantifier::Type(_) => CoreQuantifier::Type(fresh),
        CoreQuantifier::Row(_) => CoreQuantifier::Row(fresh),
    };
    CoreFnSig::new(
        quantifiers,
        signature
            .params()
            .iter()
            .map(|ty| rename_bound_core(ty, &old, fresh))
            .collect(),
        CompSig::new(
            rename_bound_core(signature.body().result(), &old, fresh),
            rename_bound_row(signature.body().effects(), &old, fresh),
        ),
    )
}

pub(super) fn rename_bound_core(ty: &CoreType, old: &CoreQuantifier, fresh: Sym) -> CoreType {
    match ty {
        CoreType::Source(ty) => CoreType::Source(match old {
            CoreQuantifier::Type(name) => ty.subst_var(*name, &Type::Var(fresh)),
            CoreQuantifier::Row(name) => ty.subst_row_var(*name, &EffRow::Var(fresh)),
        }),
        CoreType::Thunk(signature) => CoreType::Thunk(Box::new(CompSig::new(
            rename_bound_core(signature.result(), old, fresh),
            rename_bound_row(signature.effects(), old, fresh),
        ))),
        CoreType::Function(signature) => {
            let shadowed = signature.quantifiers().iter().any(|quantifier| {
                matches!(
                    (old, quantifier),
                    (CoreQuantifier::Type(a), CoreQuantifier::Type(b))
                        | (CoreQuantifier::Row(a), CoreQuantifier::Row(b)) if a == b
                )
            });
            if shadowed {
                CoreType::Function(signature.clone())
            } else {
                CoreType::Function(Box::new(CoreFnSig::new(
                    signature.quantifiers().to_vec(),
                    signature
                        .params()
                        .iter()
                        .map(|ty| rename_bound_core(ty, old, fresh))
                        .collect(),
                    CompSig::new(
                        rename_bound_core(signature.body().result(), old, fresh),
                        rename_bound_row(signature.body().effects(), old, fresh),
                    ),
                )))
            }
        }
        CoreType::Ref(inner) => CoreType::Ref(Box::new(rename_bound_core(inner, old, fresh))),
        CoreType::ReuseToken(inner) => {
            CoreType::ReuseToken(Box::new(rename_bound_core(inner, old, fresh)))
        }
        CoreType::Lowered(kind) => CoreType::Lowered(match kind {
            LoweredType::Word => LoweredType::Word,
            LoweredType::Eff(row) => LoweredType::Eff(rename_bound_row(row, old, fresh)),
            LoweredType::Queue(row) => LoweredType::Queue(rename_bound_row(row, old, fresh)),
            LoweredType::QueueView(row) => {
                LoweredType::QueueView(rename_bound_row(row, old, fresh))
            }
        }),
    }
}

fn rename_bound_row(row: &EffRow, old: &CoreQuantifier, fresh: Sym) -> EffRow {
    match old {
        CoreQuantifier::Type(name) => row.map_args(&|ty| ty.subst_var(*name, &Type::Var(fresh))),
        CoreQuantifier::Row(name) => row.subst_row_var(*name, &EffRow::Var(fresh)),
    }
}

pub(super) fn substitute_sig(
    signature: &CompSig,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> CompSig {
    CompSig::new(
        substitute_core_type(signature.result(), quantifiers, arguments),
        substitute_row(signature.effects(), quantifiers, arguments),
    )
}

pub(super) fn substitute_type(
    ty: &Type,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Type {
    let (types, rows) = substitution_maps(quantifiers, arguments);
    let substituted = substitute_type_with(
        ty,
        &types,
        &rows,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
    );
    normalize_type_rows(&substituted)
}

pub(super) fn substitute_row(
    row: &EffRow,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> EffRow {
    let (types, rows) = substitution_maps(quantifiers, arguments);
    let substituted = substitute_row_with(
        row,
        &types,
        &rows,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
    );
    normalize_row(&substituted)
}

fn substitution_maps(
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> (BTreeMap<Sym, Type>, BTreeMap<Sym, EffRow>) {
    let mut types = BTreeMap::new();
    let mut rows = BTreeMap::new();
    for (quantifier, argument) in quantifiers.iter().zip(arguments) {
        match (quantifier, argument) {
            (CoreQuantifier::Type(name), CoreInstantiation::Type(argument)) => {
                types.insert(*name, argument.clone());
            }
            (CoreQuantifier::Row(name), CoreInstantiation::Row(argument)) => {
                rows.insert(*name, argument.clone());
            }
            _ => {}
        }
    }
    (types, rows)
}

fn substitute_type_with(
    ty: &Type,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    bound_types: &mut BTreeSet<Sym>,
    bound_rows: &mut BTreeSet<Sym>,
) -> Type {
    match ty {
        Type::Var(name) if !bound_types.contains(name) => {
            types.get(name).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::Forall(name, body) => {
            let inserted = bound_types.insert(*name);
            let body = substitute_type_with(body, types, rows, bound_types, bound_rows);
            if inserted {
                bound_types.remove(name);
            }
            Type::Forall(*name, Box::new(body))
        }
        Type::RowForall(name, body) => {
            let inserted = bound_rows.insert(*name);
            let body = substitute_type_with(body, types, rows, bound_types, bound_rows);
            if inserted {
                bound_rows.remove(name);
            }
            Type::RowForall(*name, Box::new(body))
        }
        Type::Fun(params, effects, result) => Type::Fun(
            params
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
            substitute_row_with(effects, types, rows, bound_types, bound_rows),
            Box::new(substitute_type_with(
                result,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
        ),
        Type::Con(name, arguments) => Type::Con(
            *name,
            arguments
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::App(head, argument) => Type::app(
            substitute_type_with(head, types, rows, bound_types, bound_rows),
            substitute_type_with(argument, types, rows, bound_types, bound_rows),
        ),
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::UnboxedTuple(fields) => Type::UnboxedTuple(
            fields
                .iter()
                .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                .collect(),
        ),
        Type::UnboxedRecord(fields) => Type::UnboxedRecord(
            fields
                .iter()
                .map(|(name, ty)| {
                    (
                        *name,
                        substitute_type_with(ty, types, rows, bound_types, bound_rows),
                    )
                })
                .collect(),
        ),
        Type::OrNull(inner) => Type::OrNull(Box::new(substitute_type_with(
            inner,
            types,
            rows,
            bound_types,
            bound_rows,
        ))),
        Type::Row(row) => Type::Row(substitute_row_with(
            row,
            types,
            rows,
            bound_types,
            bound_rows,
        )),
        Type::Coeffect(inner, row) => Type::Coeffect(
            Box::new(substitute_type_with(
                inner,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
            row.clone(),
        ),
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Var(_)
        | Type::Exist(_)
        | Type::Nat(_) => ty.clone(),
    }
}

fn substitute_row_with(
    row: &EffRow,
    types: &BTreeMap<Sym, Type>,
    rows: &BTreeMap<Sym, EffRow>,
    bound_types: &mut BTreeSet<Sym>,
    bound_rows: &mut BTreeSet<Sym>,
) -> EffRow {
    match row {
        EffRow::Var(name) if !bound_rows.contains(name) => {
            rows.get(name).cloned().unwrap_or_else(|| row.clone())
        }
        EffRow::Extend(label, rest) => EffRow::Extend(
            Label {
                name: label.name,
                args: label
                    .args
                    .iter()
                    .map(|ty| substitute_type_with(ty, types, rows, bound_types, bound_rows))
                    .collect(),
            },
            Box::new(substitute_row_with(
                rest,
                types,
                rows,
                bound_types,
                bound_rows,
            )),
        ),
        EffRow::Empty | EffRow::Var(_) | EffRow::Exist(_) => row.clone(),
    }
}

pub(super) fn substitute_label(
    label: &Label,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Label {
    Label {
        name: label.name,
        args: label
            .args
            .iter()
            .map(|ty| substitute_type(ty, quantifiers, arguments))
            .collect(),
    }
}

fn normalize_row(row: &EffRow) -> EffRow {
    EffRow::canonical(
        row.labels().into_iter().map(|label| Label {
            name: label.name,
            args: label.args.iter().map(normalize_type_rows).collect(),
        }),
        row.tail().clone(),
    )
}

fn normalize_type_rows(ty: &Type) -> Type {
    match ty {
        Type::Forall(name, body) => Type::Forall(*name, Box::new(normalize_type_rows(body))),
        Type::RowForall(name, body) => Type::RowForall(*name, Box::new(normalize_type_rows(body))),
        Type::Fun(params, row, result) => Type::Fun(
            params.iter().map(normalize_type_rows).collect(),
            normalize_row(row),
            Box::new(normalize_type_rows(result)),
        ),
        Type::Con(name, arguments) => {
            Type::Con(*name, arguments.iter().map(normalize_type_rows).collect())
        }
        Type::App(head, argument) => {
            Type::app(normalize_type_rows(head), normalize_type_rows(argument))
        }
        Type::Tuple(fields) => Type::Tuple(fields.iter().map(normalize_type_rows).collect()),
        Type::UnboxedTuple(fields) => {
            Type::UnboxedTuple(fields.iter().map(normalize_type_rows).collect())
        }
        Type::UnboxedRecord(fields) => Type::UnboxedRecord(
            fields
                .iter()
                .map(|(name, ty)| (*name, normalize_type_rows(ty)))
                .collect(),
        ),
        Type::OrNull(inner) => Type::OrNull(Box::new(normalize_type_rows(inner))),
        Type::Row(row) => Type::Row(normalize_row(row)),
        Type::Coeffect(inner, row) => {
            Type::Coeffect(Box::new(normalize_type_rows(inner)), row.clone())
        }
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Var(_)
        | Type::Exist(_)
        | Type::Nat(_) => ty.clone(),
    }
}

fn pop_scoped<T>(scopes: &mut BTreeMap<Sym, Vec<T>>, name: Sym) -> Option<T> {
    let (value, empty) = {
        let stack = scopes.get_mut(&name)?;
        let value = stack.pop();
        (value, stack.is_empty())
    };
    if empty {
        scopes.remove(&name);
    }
    value
}

fn merge_token_states(
    left: &BTreeMap<Sym, Vec<u8>>,
    right: &BTreeMap<Sym, Vec<u8>>,
) -> BTreeMap<Sym, Vec<u8>> {
    left.iter()
        .map(|(name, credits)| {
            (
                *name,
                credits
                    .iter()
                    .enumerate()
                    .map(|(index, credit)| {
                        (*credit).min(
                            right
                                .get(name)
                                .and_then(|other| other.get(index))
                                .copied()
                                .unwrap_or_default(),
                        )
                    })
                    .collect(),
            )
        })
        .collect()
}

fn merge_shell_states(
    left: &BTreeMap<Sym, Vec<ReuseShell>>,
    right: &BTreeMap<Sym, Vec<ReuseShell>>,
) -> BTreeMap<Sym, Vec<ReuseShell>> {
    let mut merged = left.clone();
    for (name, shells) in &mut merged {
        for (index, shell) in shells.iter_mut().enumerate() {
            let other = right.get(name).and_then(|others| others.get(index));
            shell.remaining = other.map_or(0, |other| {
                if shell.scrutinee == other.scrutinee
                    && shell.binding_depth == other.binding_depth
                    && shell.capacity == other.capacity
                {
                    shell.remaining.min(other.remaining)
                } else {
                    0
                }
            });
        }
    }
    merged
}

pub(super) fn union_rows(left: &EffRow, right: &EffRow) -> Result<EffRow, String> {
    let tail = match (left.tail(), right.tail()) {
        (a, b) if a == b => a.clone(),
        (EffRow::Empty, other) | (other, EffRow::Empty) => other.clone(),
        (a, b) => {
            return Err(format!(
                "cannot prove union of distinct open tails {} and {}",
                a.show(),
                b.show()
            ));
        }
    };
    let mut labels: BTreeMap<Sym, Label> = BTreeMap::new();
    for label in left.labels().into_iter().chain(right.labels()) {
        match labels.get(&label.name) {
            Some(existing) if existing.args == label.args => {}
            Some(existing) if existing.args.is_empty() => {
                labels.insert(label.name, label.clone());
            }
            Some(_) if label.args.is_empty() => {}
            Some(existing) => {
                return Err(format!(
                    "cannot prove union of effect labels {} and {}",
                    existing.show(),
                    label.show()
                ));
            }
            None => {
                labels.insert(label.name, label.clone());
            }
        }
    }
    Ok(EffRow::canonical(labels.into_values(), tail))
}

fn core_subtype(actual: &CoreType, expected: &CoreType) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (CoreType::Source(actual), CoreType::Source(expected)) => source_repr_eq(actual, expected),
        (CoreType::Thunk(actual), CoreType::Thunk(expected)) => sig_subtype(actual, expected),
        (CoreType::Function(actual), CoreType::Function(expected)) => {
            fn_sig_subtype(actual, expected)
        }
        // Mutable cells and reuse tokens are invariant in their payload.
        (CoreType::Ref(actual), CoreType::Ref(expected))
        | (CoreType::ReuseToken(actual), CoreType::ReuseToken(expected)) => actual == expected,
        (CoreType::Lowered(actual), CoreType::Lowered(expected)) => actual == expected,
        _ => false,
    }
}

pub(super) fn lowered_representation_conversion(actual: &CoreType, expected: &CoreType) -> bool {
    let runtime_word = |ty: &CoreType| {
        matches!(
            ty,
            CoreType::Source(ty) if repr_of_type(ty).is_gc_value()
        ) || matches!(
            ty,
            CoreType::Thunk(_) | CoreType::Function(_) | CoreType::Ref(_)
        )
    };
    match (actual, expected) {
        (actual, CoreType::Lowered(LoweredType::Word)) if runtime_word(actual) => true,
        (CoreType::Lowered(LoweredType::Word), expected) if runtime_word(expected) => true,
        (CoreType::Source(Type::Unit), CoreType::Lowered(LoweredType::Queue(_))) => true,
        _ => false,
    }
}

pub(super) fn representation_preserving(actual: &CoreType, expected: &CoreType) -> bool {
    if matches!(
        (actual, expected),
        (CoreType::Source(Type::Int), CoreType::Source(Type::Char))
            | (CoreType::Source(Type::Char), CoreType::Source(Type::Int))
    ) {
        return true;
    }
    let (CoreType::Thunk(actual), CoreType::Thunk(expected)) = (actual, expected) else {
        return false;
    };
    let (CoreType::Function(actual_fn), CoreType::Function(expected_fn)) =
        (actual.result(), expected.result())
    else {
        return false;
    };
    let Some((actual_fn, expected_fn)) = alpha_align_fn_sigs(actual_fn, expected_fn) else {
        return false;
    };
    actual.effects() == expected.effects()
        && actual_fn.params() == expected_fn.params()
        && actual_fn.body().result() == expected_fn.body().result()
}

fn fn_sig_subtype(actual: &CoreFnSig, expected: &CoreFnSig) -> bool {
    let Some((actual, expected)) = alpha_align_fn_sigs(actual, expected) else {
        return false;
    };
    actual.params() == expected.params() && sig_subtype(actual.body(), expected.body())
}

/// Rename corresponding function quantifiers to shared fresh names before a
/// structural comparison. Quantifier spelling is not part of a Core type, and
/// substitution deliberately changes it to avoid capture.
fn alpha_align_fn_sigs(actual: &CoreFnSig, expected: &CoreFnSig) -> Option<(CoreFnSig, CoreFnSig)> {
    if actual.quantifiers().len() != expected.quantifiers().len() {
        return None;
    }
    if !actual
        .quantifiers()
        .iter()
        .zip(expected.quantifiers())
        .all(|(actual, expected)| {
            matches!(
                (actual, expected),
                (CoreQuantifier::Type(_), CoreQuantifier::Type(_))
                    | (CoreQuantifier::Row(_), CoreQuantifier::Row(_))
            )
        })
    {
        return None;
    }

    let mut actual = actual.clone();
    let mut expected = expected.clone();
    for index in 0..actual.quantifiers().len() {
        let fresh = Sym::fresh();
        actual = rename_fn_quantifier(&actual, index, fresh);
        expected = rename_fn_quantifier(&expected, index, fresh);
    }
    Some((actual, expected))
}

fn source_repr_eq(actual: &Type, expected: &Type) -> bool {
    if actual == expected
        || matches!(
            (actual, expected),
            (Type::Int, Type::Char) | (Type::Char, Type::Int)
        )
    {
        return true;
    }
    match (actual, expected) {
        (Type::Fun(ap, ae, ar), Type::Fun(ep, ee, er)) => {
            ap.len() == ep.len()
                && ap.iter().zip(ep).all(|(a, e)| source_repr_eq(a, e))
                && row_repr_eq(ae, ee)
                && source_repr_eq(ar, er)
        }
        (Type::Con(an, aa), Type::Con(en, ea)) if an == en && aa.len() == ea.len() => {
            aa.iter().zip(ea).all(|(a, e)| source_repr_eq(a, e))
        }
        (Type::App(ah, aa), Type::App(eh, ea)) => source_repr_eq(ah, eh) && source_repr_eq(aa, ea),
        (Type::Tuple(af), Type::Tuple(ef)) | (Type::UnboxedTuple(af), Type::UnboxedTuple(ef))
            if af.len() == ef.len() =>
        {
            af.iter().zip(ef).all(|(a, e)| source_repr_eq(a, e))
        }
        (Type::UnboxedRecord(af), Type::UnboxedRecord(ef)) if af.len() == ef.len() => af
            .iter()
            .zip(ef)
            .all(|((an, a), (en, e))| an == en && source_repr_eq(a, e)),
        (Type::OrNull(a), Type::OrNull(e)) => source_repr_eq(a, e),
        (Type::Row(a), Type::Row(e)) => row_repr_eq(a, e),
        (Type::Coeffect(a, ar), Type::Coeffect(e, er)) if ar == er => source_repr_eq(a, e),
        (Type::Forall(an, a), Type::Forall(en, e))
        | (Type::RowForall(an, a), Type::RowForall(en, e))
            if an == en =>
        {
            source_repr_eq(a, e)
        }
        _ => false,
    }
}

fn row_repr_eq(actual: &EffRow, expected: &EffRow) -> bool {
    actual.tail() == expected.tail()
        && actual.labels().len() == expected.labels().len()
        && actual.labels().iter().zip(expected.labels()).all(|(a, e)| {
            a.name == e.name
                && a.args.len() == e.args.len()
                && a.args
                    .iter()
                    .zip(&e.args)
                    .all(|(a, e)| source_repr_eq(a, e))
        })
}

fn sig_subtype(actual: &CompSig, expected: &CompSig) -> bool {
    core_subtype(actual.result(), expected.result())
        && row_included(actual.effects(), expected.effects())
}

fn row_included(actual: &EffRow, expected: &EffRow) -> bool {
    if actual == expected || actual == &EffRow::Empty {
        return true;
    }
    for label in actual.labels() {
        let Some(wanted) = expected.labels().into_iter().find(|wanted| {
            wanted.name == label.name
                && (wanted.args == label.args || wanted.args.is_empty() || label.args.is_empty())
        }) else {
            return false;
        };
        if label.args != wanted.args && !label.args.is_empty() && !wanted.args.is_empty() {
            return false;
        }
    }
    match actual.tail() {
        EffRow::Empty => true,
        EffRow::Var(name) => expected.tail() == &EffRow::Var(*name),
        // Existentials are independently rejected by `check_row`; they cannot
        // be evidence for subtyping.
        EffRow::Exist(_) | EffRow::Extend(..) => false,
    }
}

fn subtract_names(row: &EffRow, names: &[Sym]) -> EffRow {
    let names: BTreeSet<_> = names.iter().copied().collect();
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !names.contains(&label.name))
            .cloned(),
        row.tail().clone(),
    )
}

fn subtract_labels(row: &EffRow, labels: &BTreeSet<Label>) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !labels.contains(*label))
            .cloned(),
        row.tail().clone(),
    )
}

fn check_type_rows(ty: &Type, f: &mut impl FnMut(&EffRow)) {
    match ty {
        Type::Forall(_, body)
        | Type::RowForall(_, body)
        | Type::OrNull(body)
        | Type::Coeffect(body, _) => check_type_rows(body, f),
        Type::Fun(params, row, result) => {
            for ty in params {
                check_type_rows(ty, f);
            }
            f(row);
            check_type_rows(result, f);
        }
        Type::Con(_, arguments) | Type::Tuple(arguments) | Type::UnboxedTuple(arguments) => {
            for ty in arguments {
                check_type_rows(ty, f);
            }
        }
        Type::UnboxedRecord(fields) => {
            for (_, ty) in fields {
                check_type_rows(ty, f);
            }
        }
        Type::App(head, argument) => {
            check_type_rows(head, f);
            check_type_rows(argument, f);
        }
        Type::Row(row) => f(row),
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Var(_)
        | Type::Exist(_)
        | Type::Nat(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::builtins::FloatOp;
    use crate::core::typed::{TypedForward, TypedHandler};
    use crate::core::Comp;

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn value(ty: Type, kind: TypedValueKind) -> TypedValue {
        TypedValue::new(source(ty), kind)
    }

    fn return_value(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(value.ty().clone()), TypedCompKind::Return(value))
    }

    fn fatal_error(sig: CompSig) -> TypedComp {
        TypedComp::new(
            sig,
            TypedCompKind::Error(value(Type::Str, TypedValueKind::Str("boom".into()))),
        )
    }

    fn function<P>(body: &TypedComp) -> TypedCore<P> {
        TypedCore::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        )])
    }

    fn local(name: &str, ty: Type) -> TypedValue {
        value(
            ty,
            TypedValueKind::Var {
                name: Sym::new(name),
                instantiation: Vec::new(),
            },
        )
    }

    #[test]
    fn accepts_a_closed_well_typed_program() {
        let body = return_value(value(Type::Int, TypedValueKind::Int(42)));
        assert_eq!(
            verify(&function::<Elaborated>(&body), &VerifyEnv::new()),
            Ok(())
        );
    }

    #[test]
    fn case_arms_may_widen_latent_effect_rows_but_not_narrow_them() {
        let row_name = Sym::new("e");
        let closure = |effects| {
            CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
                CoreFnSig::new(
                    Vec::new(),
                    vec![source(Type::U64)],
                    CompSig::new(source(Type::Int), effects),
                ),
            )))))
        };
        let pure_closure = closure(EffRow::Empty);
        let open_closure = closure(EffRow::Var(row_name));
        let program = |arm_ty: CoreType, result_ty: CoreType| {
            let choice = TypedBinder::new(Sym::new("choice"), source(Type::Bool));
            let selected = TypedBinder::new(Sym::new("selected"), arm_ty.clone());
            let arm_value = TypedValue::new(
                arm_ty.clone(),
                TypedValueKind::Var {
                    name: selected.name(),
                    instantiation: Vec::new(),
                },
            );
            let body = TypedComp::new(
                pure(result_ty.clone()),
                TypedCompKind::Case(
                    TypedValue::new(
                        choice.ty().clone(),
                        TypedValueKind::Var {
                            name: choice.name(),
                            instantiation: Vec::new(),
                        },
                    ),
                    vec![(TypedPattern::Wild, return_value(arm_value))],
                ),
            );
            TypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
                Sym::new("main"),
                vec![choice, selected],
                body,
                CoreFnSig::new(
                    vec![CoreQuantifier::Row(row_name)],
                    vec![source(Type::Bool), arm_ty],
                    pure(result_ty),
                ),
                0,
            )])
        };

        assert_eq!(
            verify(
                &program(pure_closure.clone(), open_closure.clone()),
                &VerifyEnv::new()
            ),
            Ok(())
        );
        let errors = verify(&program(open_closure, pure_closure), &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.path().ends_with("body.arm[0]")
                && error.message().contains("expected a subtype of Thunk")
        }));
    }

    #[test]
    fn rc_sequence_witness_is_confined_to_administrative_owned_binds() {
        let unit = source(Type::Unit);
        let unit_value = || value(Type::Unit, TypedValueKind::Unit);
        let sequence = |binder: TypedBinder, rest: TypedComp| {
            TypedComp::new(
                rest.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        pure(unit.clone()),
                        TypedCompKind::Dup(unit_value()),
                    )),
                    binder,
                    Box::new(rest),
                ),
            )
        };

        let valid = sequence(TypedBinder::rc_sequence(), return_value(unit_value()));
        let valid_core = function::<Owned>(&valid);
        assert_eq!(verify(&valid_core, &VerifyEnv::new()), Ok(()));
        let Comp::Bind(_, erased_binder, _) = &valid_core.erase().fns[0].body else {
            panic!("expected erased administrative bind");
        };
        assert_eq!(erased_binder.as_str(), "_");

        let too_early = sequence(TypedBinder::rc_sequence(), return_value(unit_value()));
        let errors = verify(&function::<EffectLowered>(&too_early), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("illegal in effect-lowered Core")));

        let ordinary_first = TypedComp::new(
            pure(unit.clone()),
            TypedCompKind::Bind(
                Box::new(return_value(unit_value())),
                TypedBinder::rc_sequence(),
                Box::new(return_value(unit_value())),
            ),
        );
        let errors = verify(&function::<Owned>(&ordinary_first), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("does not sequence a dup or drop")));

        let missing_witness = sequence(
            TypedBinder::new(Sym::new(names::RC_SEQUENCE_BINDER), unit.clone()),
            return_value(unit_value()),
        );
        let errors = verify(&function::<Owned>(&missing_witness), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("lacks its erasure witness")));

        let wrong_name = sequence(
            TypedBinder {
                name: Sym::new("wrong"),
                ty: unit.clone(),
                erasure: BinderErasure::RcSequence,
            },
            return_value(unit_value()),
        );
        let errors = verify(&function::<Owned>(&wrong_name), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("wrong reserved identity")));

        let wrong_type = sequence(
            TypedBinder {
                name: Sym::new(names::RC_SEQUENCE_BINDER),
                ty: source(Type::Int),
                erasure: BinderErasure::RcSequence,
            },
            return_value(unit_value()),
        );
        let errors = verify(&function::<Owned>(&wrong_type), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("RC sequence witness")));

        let lambda_body = return_value(unit_value());
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![unit.clone()],
                lambda_body.sig().clone(),
            )))),
            TypedCompKind::Lam(vec![TypedBinder::rc_sequence()], Box::new(lambda_body)),
        );
        let errors = verify(&function::<Owned>(&lambda), &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| error
            .message()
            .contains("outside an administrative dup/drop bind")));

        let parameter_body = return_value(unit_value());
        let parameter_core = TypedCore::<Owned>::new(vec![TypedCoreFn::new(
            Sym::new("parameter"),
            vec![TypedBinder::rc_sequence()],
            parameter_body.clone(),
            CoreFnSig::new(Vec::new(), vec![unit.clone()], parameter_body.sig().clone()),
            0,
        )]);
        let errors = verify(&parameter_core, &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| error
            .message()
            .contains("outside an administrative dup/drop bind")));

        let dangling = TypedValue::new(
            unit.clone(),
            TypedValueKind::Var {
                name: Sym::new(names::RC_SEQUENCE_BINDER),
                instantiation: Vec::new(),
            },
        );
        let referenced = sequence(TypedBinder::rc_sequence(), return_value(dangling));
        let errors = verify(&function::<Owned>(&referenced), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("neither local nor global")));
    }

    #[test]
    fn rejects_a_drifting_literal_witness() {
        let body = return_value(value(Type::Bool, TypedValueKind::Int(42)));
        let errors = verify(&function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("integer literal")));
    }

    #[test]
    fn rejects_effect_row_drift() {
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Io(IoOp::ReadInt, Vec::new()),
        );
        let errors = verify(&function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("I/O operation row mismatch")));
    }

    #[test]
    fn accepts_error_with_arbitrary_well_formed_inherited_witnesses() {
        let inherited = fatal_error(CompSig::new(
            source(Type::Bool),
            EffRow::singleton(crate::names::IO_EFFECT),
        ));
        assert_eq!(
            verify(&function::<Elaborated>(&inherited), &VerifyEnv::new()),
            Ok(())
        );
    }

    #[test]
    fn rejects_error_with_an_unbound_result_type_witness() {
        let unbound_result = Sym::new("unbound_error_result");
        let bad_result = fatal_error(pure(source(Type::Var(unbound_result))));
        let bad_result_core = TypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
            Sym::new("bad_result"),
            Vec::new(),
            bad_result,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Unit))),
            0,
        )]);
        let errors = verify(&bad_result_core, &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| {
            error
                .message()
                .contains(&format!("unbound rigid type variable {unbound_result}"))
        }));
    }

    #[test]
    fn rejects_error_with_an_unbound_effect_row_witness() {
        let unbound_effects = Sym::new("unbound_error_effects");
        let bad_effects = fatal_error(CompSig::new(
            source(Type::Unit),
            EffRow::Var(unbound_effects),
        ));
        let bad_effects_core = TypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
            Sym::new("bad_effects"),
            Vec::new(),
            bad_effects,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Unit))),
            0,
        )]);
        let errors = verify(&bad_effects_core, &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.message().contains(&format!(
                "unbound rigid effect-row variable {unbound_effects}"
            ))
        }));
    }

    #[test]
    fn rejects_a_bind_that_hides_a_child_effect() {
        let unit = source(Type::Unit);
        let io = TypedComp::new(
            CompSig::new(unit.clone(), EffRow::singleton(crate::names::IO_EFFECT)),
            TypedCompKind::Io(IoOp::PrintNl, Vec::new()),
        );
        let rest = return_value(value(Type::Unit, TypedValueKind::Unit));
        let hidden = TypedComp::new(
            pure(unit.clone()),
            TypedCompKind::Bind(
                Box::new(io),
                TypedBinder::new(Sym::new("ignored"), unit),
                Box::new(rest),
            ),
        );
        let errors = verify(&function::<Elaborated>(&hidden), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("does not include derived {IO}")));
    }

    #[test]
    fn rejects_unknown_references_and_duplicate_binders() {
        let binder = TypedBinder::new(Sym::new("x"), source(Type::Int));
        let unknown = value(
            Type::Int,
            TypedValueKind::Var {
                name: Sym::new("missing"),
                instantiation: Vec::new(),
            },
        );
        let lambda_body = return_value(unknown);
        let lambda_sig = CoreFnSig::new(
            Vec::new(),
            vec![source(Type::Int), source(Type::Int)],
            lambda_body.sig().clone(),
        );
        let body = TypedComp::new(
            pure(CoreType::Function(Box::new(lambda_sig))),
            TypedCompKind::Lam(vec![binder.clone(), binder], Box::new(lambda_body)),
        );
        let errors = verify(&function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("duplicated in one binding group")));
        assert!(errors
            .iter()
            .any(|error| error.message().contains("neither local nor global")));
    }

    #[test]
    fn checks_explicit_polymorphic_call_instantiation() {
        let type_parameter = Sym::new("a");
        let parameter = TypedBinder::new(Sym::new("x"), source(Type::Var(type_parameter)));
        let id_body = return_value(local("x", Type::Var(type_parameter)));
        let id = TypedCoreFn::new(
            Sym::new("id"),
            vec![parameter],
            id_body.clone(),
            CoreFnSig::new(
                vec![CoreQuantifier::Type(type_parameter)],
                vec![source(Type::Var(type_parameter))],
                id_body.sig().clone(),
            ),
            0,
        );
        let call = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Call {
                callee: Sym::new("id"),
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                args: vec![value(Type::Int, TypedValueKind::Int(1))],
            },
        );
        let main = TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            call.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), call.sig().clone()),
            0,
        );
        let core = TypedCore::<Elaborated>::new(vec![id.clone(), main]);
        assert_eq!(verify(&core, &VerifyEnv::new()), Ok(()));

        let bad_call = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Call {
                callee: Sym::new("id"),
                instantiation: vec![CoreInstantiation::Row(EffRow::Empty)],
                args: vec![value(Type::Int, TypedValueKind::Int(1))],
            },
        );
        let bad_main = TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            bad_call.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), bad_call.sig().clone()),
            0,
        );
        let errors = verify(
            &TypedCore::<Elaborated>::new(vec![id, bad_main]),
            &VerifyEnv::new(),
        )
        .unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("wrong kind")));
    }

    #[test]
    fn rejects_constructor_tag_and_field_drift() {
        let parameter = Sym::new("a");
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            Sym::new("Some"),
            ConstructorSig::new(
                vec![CoreQuantifier::Type(parameter)],
                7,
                vec![source(Type::Var(parameter))],
                source(Type::Con(Sym::new("Option"), vec![Type::Var(parameter)])),
            ),
        );
        let option_int = Type::Con(Sym::new("Option"), vec![Type::Int]);
        let constructor = TypedValue::new(
            source(option_int),
            TypedValueKind::Ctor {
                name: Sym::new("Some"),
                tag: 8,
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                fields: vec![value(Type::Bool, TypedValueKind::Bool(true))],
            },
        );
        let errors = verify(&function::<Elaborated>(&return_value(constructor)), &env).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("declared tag 7")));
        assert!(errors
            .iter()
            .any(|error| error.message().contains("constructor field type mismatch")));
    }

    #[test]
    fn checks_handler_residual_rows_and_resumption_type() {
        let operation_name = Sym::new("get");
        let effect_name = Sym::new("State");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation_name,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect_name),
            ),
        );
        let handled = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::singleton(effect_name)),
            TypedCompKind::Do {
                operation: operation_name,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let outer = pure(source(Type::Int));
        let resume = TypedBinder::new(
            Sym::new("resume"),
            CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
                CoreFnSig::new(Vec::new(), vec![source(Type::Int)], outer.clone()),
            ))))),
        );
        let arm = TypedHandleOp::new(
            operation_name,
            Vec::new(),
            Vec::new(),
            resume,
            return_value(value(Type::Int, TypedValueKind::Int(0))),
        );
        let clauses = TypedHandler::new(vec![arm]).unwrap();
        let body = TypedComp::new(
            outer,
            TypedCompKind::Handle {
                body: Box::new(handled.clone()),
                return_binder: None,
                return_body: None,
                ops: clauses,
            },
        );
        assert_eq!(verify(&function::<Elaborated>(&body), &env), Ok(()));

        env.insert_operation(
            Sym::new("put"),
            OperationSig::new(
                Vec::new(),
                vec![source(Type::Int)],
                source(Type::Unit),
                Label::bare(effect_name),
            ),
        );
        let residual = CompSig::new(source(Type::Int), EffRow::singleton(effect_name));
        let resume = TypedBinder::new(
            Sym::new("resume_partial"),
            CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
                CoreFnSig::new(Vec::new(), vec![source(Type::Int)], residual.clone()),
            ))))),
        );
        let arm = TypedHandleOp::new(
            operation_name,
            Vec::new(),
            Vec::new(),
            resume,
            return_value(value(Type::Int, TypedValueKind::Int(0))),
        );
        let partial =
            TypedComp::new(
                residual,
                TypedCompKind::Handle {
                    body: Box::new(handled),
                    return_binder: None,
                    return_body: None,
                    ops: TypedHandler::new(vec![arm]).unwrap().with_forwarded(vec![
                        TypedForward::new(Sym::new("put"), Label::bare(effect_name)),
                    ]),
                },
            );
        assert_eq!(verify(&function::<Elaborated>(&partial), &env), Ok(()));
    }

    #[test]
    fn rejects_nodes_outside_their_phase() {
        let integer = value(Type::Int, TypedValueKind::Int(1));
        let ref_new = TypedComp::new(
            pure(CoreType::Ref(Box::new(source(Type::Int)))),
            TypedCompKind::RefNew(integer),
        );
        let elaborated_errors =
            verify(&function::<Elaborated>(&ref_new), &VerifyEnv::new()).unwrap_err();
        assert!(elaborated_errors
            .iter()
            .any(|error| error.message().contains("illegal in elaborated Core")));

        let returned = return_value(value(Type::Int, TypedValueKind::Int(1)));
        let mask = TypedComp::new(
            returned.sig().clone(),
            TypedCompKind::Mask(Vec::new(), Box::new(returned)),
        );
        let lowered_errors =
            verify(&function::<EffectLowered>(&mask), &VerifyEnv::new()).unwrap_err();
        assert!(lowered_errors
            .iter()
            .any(|error| error.message().contains("illegal in effect-lowered Core")));
    }

    // `init_at` is the proof that a cell an allocator handed out now holds a
    // constructor. Each premise of that claim is independent, so each is pinned:
    // the phase it may appear in, that the cell is the declared `alloc` result,
    // that the payload is something a cell can hold, and that the node's own
    // witness is the constructor's.
    #[test]
    fn init_at_checks_every_premise_of_its_claim() {
        let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
        let cell = Type::Con(Sym::new("Arena.Cell"), Vec::new());
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            Sym::new("Boxed"),
            ConstructorSig::new(Vec::new(), 0, Vec::new(), source(boxed.clone())),
        );
        env.insert_operation(
            Sym::new("alloc"),
            OperationSig::new(
                Vec::new(),
                vec![source(Type::Int)],
                source(cell.clone()),
                Label::bare("Alloc"),
            ),
        );
        let ctor = || {
            TypedValue::new(
                source(boxed.clone()),
                TypedValueKind::Ctor {
                    name: Sym::new("Boxed"),
                    tag: 0,
                    instantiation: Vec::new(),
                    fields: Vec::new(),
                },
            )
        };
        let init_at = |cell_value: TypedValue, payload: TypedValue, result: Type| {
            TypedComp::new(
                pure(source(result)),
                TypedCompKind::InitAt(cell_value, payload),
            )
        };
        let good = || init_at(local("c", cell.clone()), ctor(), boxed.clone());
        let in_scope = |body: &TypedComp| {
            TypedComp::new(
                CompSig::new(body.sig().result().clone(), EffRow::singleton("Alloc")),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(source(cell.clone()), EffRow::singleton("Alloc")),
                        TypedCompKind::Do {
                            operation: Sym::new("alloc"),
                            instantiation: Vec::new(),
                            args: vec![value(Type::Int, TypedValueKind::Int(0))],
                        },
                    )),
                    TypedBinder::new(Sym::new("c"), source(cell.clone())),
                    Box::new(body.clone()),
                ),
            )
        };

        // Legal once an arena has been prepared, and never before.
        assert_eq!(
            verify(&function::<ArenaPrepared>(&in_scope(&good())), &env),
            Ok(())
        );
        let too_early = verify(&function::<Elaborated>(&in_scope(&good())), &env).unwrap_err();
        assert!(too_early
            .iter()
            .any(|error| error.message().contains("illegal in elaborated Core")));

        // The cell must be what this allocator hands out.
        let wrong_cell = in_scope(&init_at(local("c", Type::Int), ctor(), boxed.clone()));
        let errors = verify(&function::<ArenaPrepared>(&wrong_cell), &env).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("init-at cell")));

        // A cell holds a constructor, not an arbitrary value.
        let not_a_ctor = in_scope(&init_at(
            local("c", cell.clone()),
            value(Type::Int, TypedValueKind::Int(1)),
            Type::Int,
        ));
        let errors = verify(&function::<ArenaPrepared>(&not_a_ctor), &env).unwrap_err();
        assert!(errors.iter().any(|error| error
            .message()
            .contains("init-at payload is not a constructor")));

        // The node returns the constructor it wrote, purely.
        let drifting = in_scope(&init_at(local("c", cell.clone()), ctor(), Type::Int));
        let errors = verify(&function::<ArenaPrepared>(&drifting), &env).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("init-at type mismatch")));
    }

    #[test]
    fn reference_count_operations_return_unit() {
        let dup = TypedComp::new(
            pure(source(Type::Unit)),
            TypedCompKind::Dup(value(Type::Int, TypedValueKind::Int(1))),
        );
        assert_eq!(verify(&function::<Owned>(&dup), &VerifyEnv::new()), Ok(()));

        let drifting = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Dup(value(Type::Int, TypedValueKind::Int(1))),
        );
        let errors = verify(&function::<Owned>(&drifting), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("dup type mismatch")));
    }

    #[test]
    fn row_instantiation_recanonicalizes_duplicate_labels() {
        let row_parameter = Sym::new("e");
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Row(row_parameter)],
            Vec::new(),
            CompSig::new(
                source(Type::Unit),
                EffRow::Extend(Label::bare(IO_EFFECT), Box::new(EffRow::Var(row_parameter))),
            ),
        );
        let instantiated = instantiate_fn(
            &signature,
            &[CoreInstantiation::Row(EffRow::singleton(IO_EFFECT))],
        )
        .unwrap();
        assert_eq!(instantiated.body().effects(), &EffRow::singleton(IO_EFFECT));
    }

    #[test]
    fn scheme_instantiation_is_simultaneous() {
        let first = Sym::new("a");
        let second = Sym::new("b");
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Type(first), CoreQuantifier::Type(second)],
            vec![source(Type::Var(first))],
            pure(source(Type::Var(second))),
        );
        let instantiated = instantiate_fn(
            &signature,
            &[
                CoreInstantiation::Type(Type::Var(second)),
                CoreInstantiation::Type(Type::Int),
            ],
        )
        .unwrap();
        assert_eq!(instantiated.params(), &[source(Type::Var(second))]);
        assert_eq!(instantiated.body().result(), &source(Type::Int));
    }

    #[test]
    fn canonical_builtin_signatures_are_checked_without_inference() {
        let sqrt = TypedComp::new(
            pure(source(Type::Float)),
            TypedCompKind::FloatBuiltin(
                FloatOp::Sqrt,
                value(Type::Float, TypedValueKind::Float(4.0)),
            ),
        );
        assert_eq!(
            verify(&function::<Elaborated>(&sqrt), &VerifyEnv::new()),
            Ok(())
        );

        let array_int = Type::Con(Sym::new("Array"), vec![Type::Int]);
        let get = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::StrBuiltin {
                op: Builtin::ArrayGet,
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                args: vec![
                    local("array", array_int.clone()),
                    value(Type::Int, TypedValueKind::Int(0)),
                ],
            },
        );
        let array = TypedBinder::new(Sym::new("array"), source(array_int.clone()));
        let core = TypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            vec![array],
            get.clone(),
            CoreFnSig::new(Vec::new(), vec![source(array_int)], get.sig().clone()),
            0,
        )]);
        assert_eq!(verify(&core, &VerifyEnv::new()), Ok(()));
    }

    #[test]
    fn reuse_credit_must_be_consumed_once_on_every_branch() {
        let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            Sym::new("Boxed"),
            ConstructorSig::new(Vec::new(), 0, Vec::new(), source(boxed.clone())),
        );
        let old = TypedBinder::new(Sym::new("old"), source(boxed.clone()));
        let token = TypedBinder::new(
            Sym::new("token"),
            CoreType::ReuseToken(Box::new(source(boxed.clone()))),
        );
        let rebuild = || {
            TypedValue::new(
                source(boxed.clone()),
                TypedValueKind::Ctor {
                    name: Sym::new("Boxed"),
                    tag: 0,
                    instantiation: Vec::new(),
                    fields: Vec::new(),
                },
            )
        };
        let reuse = || {
            TypedComp::new(
                pure(source(boxed.clone())),
                TypedCompKind::Reuse(token.clone(), rebuild()),
            )
        };
        let branches = TypedComp::new(
            pure(source(boxed.clone())),
            TypedCompKind::If(
                value(Type::Bool, TypedValueKind::Bool(true)),
                Box::new(reuse()),
                Box::new(reuse()),
            ),
        );
        let body = TypedComp::new(
            branches.sig().clone(),
            TypedCompKind::WithReuse {
                token: token.clone(),
                freed: local("old", boxed.clone()),
                body: Box::new(branches),
            },
        );
        let make_program = |body: TypedComp| {
            let body = TypedComp::new(
                body.sig().clone(),
                TypedCompKind::Case(
                    local("old", boxed.clone()),
                    vec![(
                        TypedPattern::Ctor {
                            name: Sym::new("Boxed"),
                            instantiation: Vec::new(),
                            fields: Vec::new(),
                        },
                        body,
                    )],
                ),
            );
            TypedCore::<ReuseLowered>::new(vec![TypedCoreFn::new(
                Sym::new("main"),
                vec![old.clone()],
                body.clone(),
                CoreFnSig::new(Vec::new(), vec![source(boxed.clone())], body.sig().clone()),
                0,
            )])
        };
        assert_eq!(verify(&make_program(body), &env), Ok(()));

        let unbalanced = TypedComp::new(
            pure(source(boxed.clone())),
            TypedCompKind::If(
                value(Type::Bool, TypedValueKind::Bool(true)),
                Box::new(reuse()),
                Box::new(return_value(rebuild())),
            ),
        );
        let unbalanced = TypedComp::new(
            unbalanced.sig().clone(),
            TypedCompKind::WithReuse {
                token,
                freed: local("old", boxed.clone()),
                body: Box::new(unbalanced),
            },
        );
        let errors = verify(&make_program(unbalanced), &env).unwrap_err();
        assert!(errors.iter().any(|error| error
            .message()
            .contains("branches consume different reuse-token credits")));
    }

    #[test]
    fn polymorphic_function_subtyping_is_alpha_invariant() {
        let a = Sym::new("a");
        let renamed = Sym::new("a$typedq0");
        let function = |name| {
            CoreType::Function(Box::new(CoreFnSig::new(
                vec![CoreQuantifier::Type(name)],
                vec![source(Type::Var(name))],
                pure(source(Type::Var(name))),
            )))
        };
        assert!(core_subtype(&function(a), &function(renamed)));
        assert!(core_subtype(&function(renamed), &function(a)));
    }

    #[test]
    fn alpha_alignment_does_not_capture_a_free_type_variable() {
        let bound = Sym::new("bound");
        let other_bound = Sym::new("other_bound");
        let free = Sym::new("free");
        let actual = CoreType::Function(Box::new(CoreFnSig::new(
            vec![CoreQuantifier::Type(bound)],
            vec![source(Type::Var(bound)), source(Type::Var(free))],
            pure(source(Type::Var(bound))),
        )));
        let expected = CoreType::Function(Box::new(CoreFnSig::new(
            vec![CoreQuantifier::Type(other_bound)],
            vec![
                source(Type::Var(other_bound)),
                source(Type::Var(other_bound)),
            ],
            pure(source(Type::Var(other_bound))),
        )));
        assert!(!core_subtype(&actual, &expected));
    }
}
