//! Syntax-directed traversal of witness-carrying Core.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names::{self, ALLOC_OP, IO_EFFECT};

use crate::core::builtins::Builtin;
use crate::core::typed::build::lower_value_type;
use crate::core::typed::reuse::rebuild_arity;
use crate::core::typed::violation::{
    ArityBound, ArityRelation, Form, InstantiationSubject, NameKind, QuantifierKind,
    RcOperandFault, RcSequenceFault, ReuseFault, RowRelation, Site, Violation,
};
use crate::core::typed::{
    BinderErasure, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder,
    TypedComp, TypedCompKind, TypedCoreFn, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind, CORE_GROW_STACK, CORE_MIN_STACK,
};
use crate::core::CoreOp::{
    Add, Addf, Div, Divf, Eq, Eqf, Ge, Gef, Gt, Gtf, Le, Lef, Lt, Ltf, Mul, Mulf, Ne, Nef, Rem,
    Sub, Subf,
};
use crate::core::{CoreOp, IoOp, NegLane};
use crate::types::ty::{EffRow, Label};
use crate::types::{layout_of_type_in, AbiLayout, Repr, Type};

use super::super::compat::{representation_preserving, row_included};
use super::super::env::MonoOperation;
use super::super::instantiate::instantiate_value_scheme;
use super::super::{
    SITE_CONSTRUCTOR_FIELD, SITE_DUP, SITE_INIT_AT, SITE_INIT_AT_CELL, SITE_INTEGER_LITERAL,
    SITE_IO_OPERATION, SITE_PRODUCT_FIELD, SITE_RC_SEQUENCE_WITNESS,
};
use super::phase::TypedCorePhase;
use super::state::{merge_shell_states, merge_token_states, pop_scoped};
use super::Checker;

impl<P: TypedCorePhase> Checker<'_, P> {
    pub(super) fn function(&mut self, function: &TypedCoreFn) {
        for quantifier in function.sig().quantifiers() {
            match quantifier {
                CoreQuantifier::Type(name) => {
                    if self.allowed_rows.contains(name) || !self.allowed_types.insert(*name) {
                        self.fail(Violation::DuplicateQuantifier {
                            kind: QuantifierKind::Type,
                            nested: false,
                            name: *name,
                        });
                    }
                }
                CoreQuantifier::Row(name) => {
                    if self.allowed_types.contains(name) || !self.allowed_rows.insert(*name) {
                        self.fail(Violation::DuplicateQuantifier {
                            kind: QuantifierKind::Row,
                            nested: false,
                            name: *name,
                        });
                    }
                }
            }
        }
        self.check_fn_sig(function.sig());

        if function.dict_arity() > function.params().len() {
            self.fail(Violation::Arity {
                counted: Site::At("dictionary"),
                relation: ArityRelation::AtMost,
                bound: ArityBound::Parameter,
                found: function.dict_arity(),
                expected: function.params().len(),
            });
        }
        if function.params().len() != function.sig().params().len() {
            self.fail(Violation::Arity {
                counted: Site::At("parameter"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Signature,
                found: function.params().len(),
                expected: function.sig().params().len(),
            });
        }
        let mut parameter_names = BTreeSet::new();
        for (index, parameter) in function.params().iter().enumerate() {
            self.at(format!("param[{index}]"), |this| {
                if let Some(expected) = function.sig().params().get(index) {
                    this.expect_type(parameter.ty(), expected, "parameter witness");
                }
                if !parameter_names.insert(parameter.name()) {
                    this.fail(Violation::DuplicateBinder {
                        name: parameter.name(),
                    });
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
                                Site::LocalReference(*name),
                            );
                        }
                        Err(error) => {
                            self.fail(Violation::Instantiation {
                                subject: InstantiationSubject::Local(*name),
                                error,
                            });
                        }
                    }
                    if matches!(local, CoreType::ReuseToken(_)) {
                        self.fail(Violation::Reuse(ReuseFault::Escapes(*name)));
                    }
                    if self.captured(*name) && !self.one_boundary_word(&local) {
                        self.fail(Violation::CellSlotNotOneWord {
                            site: Site::LocalReference(*name),
                            ty: local,
                        });
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
                    self.fail(Violation::UnboundReference { name: *name });
                }
            }
            TypedValueKind::Int(_) => {
                if !matches!(value.ty(), CoreType::Source(Type::Int | Type::Char)) {
                    self.fail(Violation::LiteralWitness {
                        site: Site::At(SITE_INTEGER_LITERAL),
                        witness: value.ty().clone(),
                    });
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
                    self.fail(Violation::ReprCoercionIllegal {
                        from: inner.ty().clone(),
                        to: value.ty().clone(),
                    });
                }
            }
            TypedValueKind::LoweredRepr {
                value: inner,
                proof,
            } => {
                self.at("lowered-repr", |this| this.value(inner));
                if !P::ALLOW_LOWERED_ABI {
                    self.fail(Violation::PhaseIllegal {
                        what: Site::At("lowered representation evidence"),
                        phase: P::NAME,
                    });
                }
                if !proof.validates(inner.ty(), value.ty()) {
                    self.fail(Violation::ReprConversionIllegal {
                        from: inner.ty().clone(),
                        to: value.ty().clone(),
                    });
                }
            }
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value: inner,
            } => {
                self.at("newtype-repr", |this| this.value(inner));
                if !self.env.newtype_constructors.contains(constructor) {
                    self.fail(Violation::NotANewtype {
                        constructor: *constructor,
                    });
                    return;
                }
                let Some(declared) = self.env.constructor(*constructor).cloned() else {
                    self.fail(Violation::UnknownName {
                        kind: NameKind::CoercionConstructor,
                        name: *constructor,
                    });
                    return;
                };
                let Some(instantiated) = self.instantiate_constructor(&declared, instantiation)
                else {
                    return;
                };
                let [field] = instantiated.fields.as_slice() else {
                    self.fail(Violation::NewtypeFieldCount {
                        constructor: *constructor,
                        found: instantiated.fields.len(),
                    });
                    return;
                };
                let construction = inner.ty() == field && value.ty() == &instantiated.result;
                let projection = inner.ty() == &instantiated.result && value.ty() == field;
                if !construction && !projection {
                    self.fail(Violation::NewtypeCoercionDisconnected {
                        constructor: *constructor,
                        field: field.clone(),
                        result: instantiated.result.clone(),
                        inner: inner.ty().clone(),
                        outer: value.ty().clone(),
                    });
                }
            }
            TypedValueKind::Thunk(body) => {
                let token_state = self.token_uses.clone();
                let shell_state = self.reuse_shells.clone();
                let quantifiers = match body.sig().result() {
                    CoreType::Function(signature) => signature.quantifiers().to_vec(),
                    _ => Vec::new(),
                };
                self.thunk_depth += 1;
                self.scoped_quantifiers(&quantifiers, |this| {
                    this.at("thunk", |this| this.comp(body));
                });
                self.thunk_depth -= 1;
                if self.token_uses != token_state {
                    self.fail(Violation::Reuse(ReuseFault::CapturesToken(Site::At(
                        "a suspended computation",
                    ))));
                }
                if self.reuse_shells != shell_state {
                    self.fail(Violation::Reuse(ReuseFault::FreesShell(Site::At(
                        "a suspended computation",
                    ))));
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
        let Some(declared) = self.env.constructor(name).cloned() else {
            self.fail(Violation::UnknownName {
                kind: NameKind::Constructor,
                name,
            });
            fields.iter().enumerate().for_each(|(index, field)| {
                self.at(format!("field[{index}]"), |this| this.value(field));
            });
            return;
        };
        let Some(instantiated) = self.instantiate_constructor(&declared, instantiation) else {
            return;
        };
        if tag != instantiated.tag {
            self.fail(Violation::ConstructorTag {
                name,
                found: tag,
                declared: instantiated.tag,
            });
        }
        self.values(fields, &instantiated.fields, SITE_CONSTRUCTOR_FIELD);
        self.cell_slots(&instantiated.fields, SITE_CONSTRUCTOR_FIELD);
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
                    SITE_PRODUCT_FIELD,
                );
                return;
            }
            _ => None,
        };
        let expected = expected.cloned();
        if let Some(expected) = expected {
            let expected: Vec<_> = expected.iter().map(lower_value_type).collect();
            self.values(fields, &expected, SITE_PRODUCT_FIELD);
            // Only a boxed tuple allocates a cell; an unboxed product has no
            // cell, and its fields keep their component layouts by design.
            if kind == ProductKind::Tuple {
                self.cell_slots(&expected, SITE_PRODUCT_FIELD);
            }
        } else {
            self.fail(Violation::ProductShape {
                witness: witness.clone(),
            });
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
            self.fail(Violation::UnboxedRecordWitness {
                witness: witness.clone(),
            });
            for (name, value) in fields {
                self.at(format!("field[{name}]"), |this| this.value(value));
            }
            return;
        };
        if fields.len() != expected.len() {
            self.fail(Violation::Arity {
                counted: Site::At("record field"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Witness,
                found: fields.len(),
                expected: expected.len(),
            });
        }
        for (index, (name, value)) in fields.iter().enumerate() {
            self.at(format!("field[{name}]"), |this| {
                this.value(value);
                if let Some((expected_name, ty)) = expected.get(index) {
                    if name != expected_name {
                        this.fail(Violation::RecordField {
                            found: *name,
                            expected: *expected_name,
                        });
                    }
                    this.expect_type(value.ty(), &lower_value_type(ty), "record field");
                }
            });
        }
    }

    fn comp(&mut self, comp: &TypedComp) {
        // The verifier recurses per typed node; grow stack segments inside the
        // recursion, same discipline as the builder it checks.
        stacker::maybe_grow(CORE_MIN_STACK, CORE_GROW_STACK, || {
            self.comp_inner(comp);
        });
    }

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
                self.check_bind_comp(comp, first, binder, rest);
            }
            TypedCompKind::Force(value) => {
                self.value(value);
                match value.ty() {
                    CoreType::Thunk(sig) => {
                        self.expect_supertype_sig(comp.sig(), sig, "force");
                    }
                    other => self.fail(Violation::NotAForm {
                        site: Site::At("force operand"),
                        expected: Form::Thunk,
                        found: other.clone(),
                    }),
                }
            }
            TypedCompKind::Lam(params, body) => self.check_lambda_comp(comp, params, body),
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
                        self.fail(Violation::NotAForm {
                            site: Site::At("application callee"),
                            expected: Form::Function,
                            found: other.clone(),
                        });
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
                self.check_if_comp(comp, condition, yes, no);
            }
            TypedCompKind::Prim(op, lhs, rhs) => self.primitive(comp, *op, lhs, rhs),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let Some(declared) = self.globals.get(callee).cloned() else {
                    self.fail(Violation::UnknownName {
                        kind: NameKind::Function,
                        name: *callee,
                    });
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
                    self.fail(Violation::ErrorArgumentWitness {
                        witness: value.ty().clone(),
                    });
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
                    self.fail(Violation::AbsentField {
                        field: *field,
                        operand: value.ty().clone(),
                    });
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
                self.require_rc_node(SITE_DUP);
                self.value(value);
                self.check_rc_operand(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    SITE_DUP,
                );
            }
            TypedCompKind::Drop(value) => {
                self.require_rc_node("drop");
                self.value(value);
                self.check_rc_operand(value);
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    "drop",
                );
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                self.require_reuse_node("with-reuse");
                self.value(freed);
                self.check_rc_operand(freed);
                self.expect_type(
                    token.ty(),
                    &CoreType::ReuseToken(Box::new(freed.ty().clone())),
                    "reuse-token binder",
                );
                let capacity = match self.claim_reuse_shell(freed) {
                    Ok(capacity) => capacity,
                    Err(fault) => {
                        self.fail(Violation::Reuse(fault));
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
                    self.fail(Violation::Reuse(ReuseFault::NotConsumedOnce(token.name())));
                }
                self.expect_sig(comp.sig(), body.sig(), "with-reuse");
            }
            TypedCompKind::Reuse(token, value) => self.check_reuse_comp(comp, token, value),
            TypedCompKind::InitAt(cell, ctor) => {
                self.require_init_at_node(SITE_INIT_AT);
                self.value(cell);
                self.value(ctor);
                // The cell is whatever the checked `alloc` operation hands out,
                // read from the environment rather than named here: the node is
                // a proof that this allocator's cell now holds this
                // constructor, so the two must agree by declaration.
                match self.env.operation(Sym::new(ALLOC_OP)) {
                    Some(alloc) => {
                        let expected = alloc.result().clone();
                        self.expect_type(cell.ty(), &expected, SITE_INIT_AT_CELL);
                    }
                    None => self.fail(Violation::InitAtWithoutAlloc),
                }
                if !matches!(
                    ctor.kind(),
                    TypedValueKind::Ctor { .. } | TypedValueKind::Tuple(_)
                ) {
                    self.fail(Violation::InitAtPayloadIsNotAllocation);
                }
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(ctor.ty().clone(), EffRow::Empty),
                    SITE_INIT_AT,
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
                    other => self.fail(Violation::NotAForm {
                        site: Site::At("ref-get operand"),
                        expected: Form::Reference,
                        found: other.clone(),
                    }),
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
                    other => self.fail(Violation::NotAForm {
                        site: Site::At("ref-set target"),
                        expected: Form::Reference,
                        found: other.clone(),
                    }),
                }
                self.expect_sig(
                    comp.sig(),
                    &CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                    "ref-set",
                );
            }
        }
    }

    fn check_bind_comp(
        &mut self,
        comp: &TypedComp,
        first: &TypedComp,
        binder: &TypedBinder,
        rest: &TypedComp,
    ) {
        self.at("first", |this| this.comp(first));
        self.expect_type(binder.ty(), first.sig().result(), "bind binder");
        if binder.erasure == BinderErasure::RcSequence {
            if !P::ALLOW_RC_NODES {
                self.fail(Violation::PhaseIllegal {
                    what: Site::At(SITE_RC_SEQUENCE_WITNESS),
                    phase: P::NAME,
                });
            }
            if binder.name() != Sym::new(names::RC_SEQUENCE_BINDER) {
                self.fail(Violation::RcSequence(
                    RcSequenceFault::WrongReservedIdentity,
                ));
            }
            self.expect_type(
                binder.ty(),
                &CoreType::Source(Type::Unit),
                SITE_RC_SEQUENCE_WITNESS,
            );
            match first.kind() {
                // The operand is the reference the operation acts on,
                // so it has to be a term that reads one. A constructed
                // value has no prior owner to retain and no owner to
                // release, so an operation standing on one is justified
                // by nothing and a later consumer asking which binding
                // it discharged would have no answer.
                TypedCompKind::Dup(operand) | TypedCompKind::Drop(operand) => {
                    if operand.referenced_binding().is_none() {
                        self.fail(Violation::RcSequence(
                            RcSequenceFault::OperandIsNotAReference,
                        ));
                    }
                }
                _ => self.fail(Violation::RcSequence(RcSequenceFault::NotADupOrDrop)),
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
                self.fail(Violation::RowMismatch {
                    site: Site::At("bind"),
                    relation: RowRelation::Includes,
                    actual: comp.sig().effects().clone(),
                    expected: effects,
                });
            }
        }
    }

    fn check_lambda_comp(&mut self, comp: &TypedComp, params: &[TypedBinder], body: &TypedComp) {
        let token_state = self.token_uses.clone();
        let shell_state = self.reuse_shells.clone();
        let Some(signature) = (match comp.sig().result() {
            CoreType::Function(signature) => Some(signature.as_ref()),
            other => {
                self.fail(Violation::NotAForm {
                    site: Site::At("lambda result"),
                    expected: Form::Function,
                    found: other.clone(),
                });
                None
            }
        }) else {
            return;
        };
        self.expect_row(comp.sig().effects(), &EffRow::Empty, "lambda");
        if params.len() != signature.params().len() {
            self.fail(Violation::Arity {
                counted: Site::At("lambda parameter"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Witness,
                found: params.len(),
                expected: signature.params().len(),
            });
        }
        // A lambda closes over its environment: parameters bind at the deeper
        // suspension depth, so a body reference to an outer binding is known
        // to read a closure capture slot.
        self.thunk_depth += 1;
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
        self.thunk_depth -= 1;
        if self.token_uses != token_state {
            self.fail(Violation::Reuse(ReuseFault::CapturesToken(Site::At(
                "a function closure",
            ))));
        }
        if self.reuse_shells != shell_state {
            self.fail(Violation::Reuse(ReuseFault::FreesShell(Site::At(
                "a function closure",
            ))));
        }
        self.token_uses = token_state;
        self.reuse_shells = shell_state;
    }

    fn check_if_comp(
        &mut self,
        comp: &TypedComp,
        condition: &TypedValue,
        yes: &TypedComp,
        no: &TypedComp,
    ) {
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
            self.fail(Violation::Reuse(ReuseFault::UnequalCredits(Site::At(
                "if branches",
            ))));
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

    // Whether a type occupies exactly one GC-scanned word at a cell boundary.
    // Constructor fields, boxed tuple fields, and closure captures are each
    // one slot of a heap cell, and every downstream computation over those
    // cells (allocation size, field offsets, reuse capacity) is a plain field
    // count on that assumption. Core-private types are all single runtime
    // words: a suspension, closure, or mutable cell is a pointer, a lowered
    // ABI value is one word by construction, and a reuse token erases to the
    // shell pointer it recycles (its linearity is policed separately). A
    // source type is judged by its boundary layout under the environment's
    // declaration evidence: an unboxed product stored in a slot is its boxed
    // boundary form, and a nominal awaiting declaration evidence stays one
    // slot, the same posture the erased pipeline takes.
    fn one_boundary_word(&self, ty: &CoreType) -> bool {
        match ty {
            CoreType::Thunk(_)
            | CoreType::Function(_)
            | CoreType::Ref(_)
            | CoreType::ReuseToken(_)
            | CoreType::Lowered(_) => true,
            CoreType::Source(ty) => {
                let env = self.env;
                let layout = layout_of_type_in(ty, |name| env.nominal_is_boxed(name));
                matches!(layout.abi(), AbiLayout::DeferredNominal)
                    || layout.abi().repr().is_some_and(|repr| repr.is_gc_value())
            }
        }
    }

    fn cell_slots(&mut self, slots: &[CoreType], site: &'static str) {
        for ty in slots {
            if !self.one_boundary_word(ty) {
                self.fail(Violation::CellSlotNotOneWord {
                    site: Site::At(site),
                    ty: ty.clone(),
                });
            }
        }
    }

    // Whether a `dup`/`drop` (or the cell a `with-reuse` frees) acts on a
    // value the count can touch, judged from the layout authority with the
    // environment's declaration evidence. Core-private types are heap cells or
    // runtime words, so only a linear reuse token is refused among them; for a
    // source type only a non-value (an effect row or a type-level natural) is
    // refused. A nominal without boxing evidence and a polymorphic word stay
    // accepted: both are runtime words whose count is decided dynamically by
    // the tag bit. An unboxed product whose fields cannot cross the ABI is
    // also accepted: the adapter that boxes it is judged where the boundary is
    // introduced, and the count acts on that box.
    fn check_rc_operand(&mut self, value: &TypedValue) {
        match value.ty() {
            CoreType::Thunk(_)
            | CoreType::Function(_)
            | CoreType::Ref(_)
            | CoreType::Lowered(_) => {}
            CoreType::ReuseToken(_) => {
                self.fail(Violation::RcOperand(RcOperandFault::ReuseToken));
            }
            CoreType::Source(ty) => {
                let env = self.env;
                let layout = layout_of_type_in(ty, |name| env.nominal_is_boxed(name));
                if layout.abi() == &AbiLayout::Invalid && layout.local() == &Repr::Any {
                    self.fail(Violation::RcOperand(RcOperandFault::NotAValue));
                }
            }
        }
    }

    fn check_reuse_comp(&mut self, comp: &TypedComp, token: &TypedBinder, value: &TypedValue) {
        self.require_reuse_node("reuse");
        self.value(value);
        let rebuild = rebuild_arity(value);
        if rebuild.is_none() {
            self.fail(Violation::Reuse(ReuseFault::RebuildIsNotAllocation));
        }
        let local = self.local(token.name());
        match local {
            Some(local) => {
                self.expect_type(token.ty(), &local, "reuse token reference");
                if let (Some(arity), Some(capacity)) = (
                    rebuild,
                    self.token_capacities
                        .get(&token.name())
                        .and_then(|capacities| capacities.last())
                        .copied(),
                ) {
                    if arity > capacity {
                        self.fail(Violation::Arity {
                            counted: Site::At("reuse rebuild"),
                            relation: ArityRelation::AtMost,
                            bound: ArityBound::ShellCapacity,
                            found: arity,
                            expected: capacity,
                        });
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
                        self.fail(Violation::Reuse(ReuseFault::ConsumedTwice(token.name())));
                    }
                } else {
                    self.fail(Violation::Reuse(ReuseFault::NotActive(token.name())));
                }
            }
            None => self.fail(Violation::Reuse(ReuseFault::OutOfScope(token.name()))),
        }
        self.expect_sig(
            comp.sig(),
            &CompSig::new(value.ty().clone(), EffRow::Empty),
            "reuse",
        );
    }

    fn primitive(&mut self, comp: &TypedComp, op: CoreOp, lhs: &TypedValue, rhs: &TypedValue) {
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
                    self.fail(Violation::LaneOperands {
                        lhs: lhs.ty().clone(),
                        rhs: rhs.ty().clone(),
                    });
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
            self.fail(Violation::Arity {
                counted: Site::At("I/O argument"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Expected,
                found: args.len(),
                expected: op.arity(),
            });
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
            SITE_IO_OPERATION,
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
            self.fail(Violation::CaseHasNoArms);
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
                    self.fail(Violation::Reuse(ReuseFault::UnequalCredits(Site::At(
                        "case arms",
                    ))));
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
                    self.fail(Violation::TuplePatternScrutinee {
                        scrutinee: scrutinee.clone(),
                    });
                    return fields.iter().filter_map(Clone::clone).collect();
                };
                self.pattern_fields(fields, &expected)
            }
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => {
                let Some(declared) = self.env.constructor(*name).cloned() else {
                    self.fail(Violation::UnknownName {
                        kind: NameKind::PatternConstructor,
                        name: *name,
                    });
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
                    self.fail(Violation::Arity {
                        counted: Site::At("constructor pattern"),
                        relation: ArityRelation::Exact,
                        bound: ArityBound::Declared,
                        found: fields.len(),
                        expected: instantiated.fields.len(),
                    });
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
            self.fail(Violation::Arity {
                counted: Site::At("tuple pattern"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Scrutinee,
                found: fields.len(),
                expected: expected.len(),
            });
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
        let Some(declared) = self.env.operation(name).cloned() else {
            self.fail(Violation::UnknownName {
                kind: NameKind::Operation,
                name,
            });
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
            self.fail(Violation::HandlerReturnClauseIncomplete);
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
                    this.fail(Violation::UnknownName {
                        kind: NameKind::HandledOperation,
                        name: arm.name(),
                    });
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
            self.fail(Violation::ForwardingMismatch {
                derived: expected_forwarding,
                stored: stored_forwarding,
            });
        }

        let discharged = self.exhaustively_handled_labels(body.sig().effects(), &instantiated_arms);
        let residual = subtract_labels(body.sig().effects(), &discharged);
        if let Some(effects) = self.union_rows(&residual, &clause_effects, "handler effect union") {
            if !row_included(&effects, comp.sig().effects()) {
                self.fail(Violation::HandlerResidualRow {
                    derived: effects,
                    stored: comp.sig().effects().clone(),
                });
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
            self.fail(Violation::Arity {
                counted: Site::At("operation arm"),
                relation: ArityRelation::Exact,
                bound: ArityBound::Declared,
                found: arm.params().len(),
                expected: operation.params.len(),
            });
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
            self.env.builtin_override(op).cloned().or_else(|| {
                self.fail(Violation::MissingBuiltinSignature {
                    builtin: op.name().into(),
                });
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

    fn values(&mut self, values: &[TypedValue], expected: &[CoreType], context: impl Into<Site>) {
        let context = context.into();
        if values.len() != expected.len() {
            self.fail(Violation::Arity {
                counted: context,
                relation: ArityRelation::Exact,
                bound: ArityBound::Expected,
                found: values.len(),
                expected: expected.len(),
            });
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
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProductKind {
    Tuple,
    UnboxedTuple,
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
