//! Syntax-directed reconstruction of typed-Core witnesses.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names::IO_EFFECT;

use crate::core::builtins::Builtin;
use crate::core::CoreOp::{
    Add, Addf, Div, Divf, Eq, Eqf, Ge, Gef, Gt, Gtf, Le, Lef, Lt, Ltf, Mul, Mulf, Ne, Nef, Rem,
    Sub, Subf,
};
use crate::core::{CheckedHandler, Comp, CoreOp, CorePat, IoOp, NegLane, Value};
use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::on_core_stack;
use super::super::violation::{
    BindPart, BuildContext, BuildError, BuildSubject, Form, NameKind, Site,
};
use super::super::{
    instantiate_constructor, instantiate_fn, instantiate_operation, instantiate_value_scheme,
    CompSig, CoreFnSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedForward,
    TypedHandleOp, TypedHandler, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
};
use super::env::{
    intrinsic_sig, lower_value_type, representation_preserving, source_type, subtract_labels,
    subtract_names,
};
use super::solve::Solver;

const FORCE_OPERAND: &str = "force operand";
const APPLICATION_CALLEE: &str = "application callee";

pub(super) struct Builder<'a> {
    globals: &'a BTreeMap<Sym, CoreFnSig>,
    verify_env: &'a VerifyEnv,
    pub(super) solver: Solver,
    scopes: BTreeMap<Sym, Vec<(Sym, CoreType)>>,
    pending_handler_rows: Vec<PendingHandlerRow>,
}

struct PendingHandlerRow {
    target: EffRow,
    body: EffRow,
    handled: BTreeMap<Sym, Label>,
    clauses: EffRow,
}

impl<'a> Builder<'a> {
    pub(super) fn new(globals: &'a BTreeMap<Sym, CoreFnSig>, verify_env: &'a VerifyEnv) -> Self {
        Self {
            globals,
            verify_env,
            solver: Solver::default(),
            scopes: BTreeMap::new(),
            pending_handler_rows: Vec::new(),
        }
    }

    pub(super) fn bind(&mut self, raw: Sym, ty: CoreType) -> TypedBinder {
        self.scopes.entry(raw).or_default().push((raw, ty.clone()));
        TypedBinder::new(raw, ty)
    }

    pub(super) fn unbind(&mut self, raw: Sym) {
        if let Some(stack) = self.scopes.get_mut(&raw) {
            stack.pop();
            if stack.is_empty() {
                self.scopes.remove(&raw);
            }
        }
    }

    fn local(&self, raw: Sym) -> Option<(Sym, CoreType)> {
        self.scopes
            .get(&raw)
            .and_then(|stack| stack.last())
            .cloned()
    }

    fn finish_comp(
        &mut self,
        sig: CompSig,
        kind: TypedCompKind,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        self.solve_pending_handler_rows(false)?;
        if let Some(expected) = expected {
            self.solver.subsume_sig(&sig, expected)?;
        }
        Ok(TypedComp::new(sig, kind))
    }

    pub(super) fn solve_pending_handler_rows(&mut self, force: bool) -> Result<(), BuildError> {
        let pending = std::mem::take(&mut self.pending_handler_rows);
        for constraint in pending {
            let resolved_body = self.solver.resolve_row(&constraint.body);
            if !force && resolved_body == constraint.body {
                self.pending_handler_rows.push(constraint);
                continue;
            }
            let effects = self.derive_handler_effects(
                &resolved_body,
                &constraint.handled,
                &constraint.clauses,
                &constraint.target,
            )?;
            self.solver
                .constrain_row_join(&constraint.target, &effects)?;
        }
        Ok(())
    }

    fn value(
        &mut self,
        value: Value,
        expected: Option<&CoreType>,
    ) -> Result<TypedValue, BuildError> {
        let (ty, kind) = match value {
            Value::Var(raw) => {
                if let Some((name, ty)) = self.local(raw) {
                    let declared = self.solver.resolve_core_head(&ty);
                    let preserve_scheme = expected
                        .is_none_or(|expected| self.solver.resolve_core_head(expected) == declared);
                    let quantifiers = if preserve_scheme {
                        &[][..]
                    } else {
                        match &declared {
                            CoreType::Function(signature) => signature.quantifiers(),
                            CoreType::Thunk(signature) => match signature.result() {
                                CoreType::Function(function) => function.quantifiers(),
                                _ => &[],
                            },
                            _ => &[],
                        }
                    };
                    let instantiation = self.solver.fresh_instantiation(quantifiers);
                    let ty = if preserve_scheme {
                        ty
                    } else {
                        instantiate_value_scheme(&ty, &instantiation)?
                    };
                    (
                        ty,
                        TypedValueKind::Var {
                            name,
                            instantiation,
                        },
                    )
                } else {
                    let declared = self
                        .globals
                        .get(&raw)
                        .ok_or(BuildError::UnknownName {
                            kind: NameKind::ValueReference,
                            name: raw,
                        })?
                        .clone();
                    let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                    let instantiated = instantiate_fn(&declared, &instantiation)?;
                    (
                        CoreType::Function(Box::new(instantiated)),
                        TypedValueKind::Var {
                            name: raw,
                            instantiation,
                        },
                    )
                }
            }
            Value::Int(value) => {
                let ty = if let Some(expected) = expected {
                    if let CoreType::Source(Type::Exist(id)) = expected {
                        self.solver.int_defaults.insert(*id);
                    }
                    expected.clone()
                } else {
                    self.solver.fresh_int_core()
                };
                (ty, TypedValueKind::Int(value))
            }
            Value::I64(value) => (CoreType::Source(Type::I64), TypedValueKind::I64(value)),
            Value::U64(value) => (CoreType::Source(Type::U64), TypedValueKind::U64(value)),
            Value::Float(value) => (CoreType::Source(Type::Float), TypedValueKind::Float(value)),
            Value::Bool(value) => (CoreType::Source(Type::Bool), TypedValueKind::Bool(value)),
            Value::Unit => (CoreType::Source(Type::Unit), TypedValueKind::Unit),
            Value::Str(value) => (CoreType::Source(Type::Str), TypedValueKind::Str(value)),
            Value::Thunk(body) => {
                let expected = expected.map(|expected| self.solver.resolve_core_head(expected));
                let expected_sig = match &expected {
                    Some(CoreType::Thunk(signature)) => Some(signature.as_ref().clone()),
                    _ => None,
                };
                let body = self.comp(*body, expected_sig.as_ref())?;
                (
                    CoreType::Thunk(Box::new(body.sig().clone())),
                    TypedValueKind::Thunk(Box::new(body)),
                )
            }
            Value::Ctor(name, tag, fields) => {
                let declared = self
                    .verify_env
                    .constructor(name)
                    .ok_or(BuildError::UnknownName {
                        kind: NameKind::Constructor,
                        name,
                    })?
                    .clone();
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let instantiated = instantiate_constructor(&declared, &instantiation)?;
                if tag != instantiated.tag {
                    return Err(BuildError::ConstructorTag {
                        name,
                        found: tag,
                        expected: instantiated.tag,
                    });
                }
                if let Some(expected) = expected {
                    self.solver.unify_core(&instantiated.result, expected)?;
                }
                if fields.len() != instantiated.fields.len() {
                    return Err(BuildError::Arity {
                        subject: BuildSubject::Constructor(name),
                        found: fields.len(),
                        expected: instantiated.fields.len(),
                    });
                }
                let fields = fields
                    .into_iter()
                    .zip(&instantiated.fields)
                    .map(|(field, expected)| self.value(field, Some(expected)))
                    .collect::<Result<Vec<_>, _>>()?;
                (
                    instantiated.result,
                    TypedValueKind::Ctor {
                        name,
                        tag,
                        instantiation,
                        fields,
                    },
                )
            }
            Value::Tuple(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::Tuple(fields))) => Some(fields.clone()),
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(lower_value_type);
                        self.value(field, expected.as_ref())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = Type::Tuple(
                    fields
                        .iter()
                        .map(|field| source_type(field.ty()))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                (CoreType::Source(ty), TypedValueKind::Tuple(fields))
            }
            Value::UnboxedTuple(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::UnboxedTuple(fields))) => Some(fields.clone()),
                    Some(CoreType::Source(Type::UnboxedRecord(fields))) => {
                        Some(fields.iter().map(|(_, ty)| ty.clone()).collect())
                    }
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(lower_value_type);
                        self.value(field, expected.as_ref())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let field_types = fields
                    .iter()
                    .map(|field| source_type(field.ty()))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = match expected {
                    Some(CoreType::Source(Type::UnboxedRecord(names))) => Type::UnboxedRecord(
                        names
                            .iter()
                            .zip(field_types)
                            .map(|((name, _), ty)| (*name, ty))
                            .collect(),
                    ),
                    _ => Type::UnboxedTuple(field_types),
                };
                (CoreType::Source(ty), TypedValueKind::UnboxedTuple(fields))
            }
            Value::UnboxedRecord(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::UnboxedRecord(fields))) => Some(fields.clone()),
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, (name, field))| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(|(_, ty)| lower_value_type(ty));
                        Ok((name, self.value(field, expected.as_ref())?))
                    })
                    .collect::<Result<Vec<_>, BuildError>>()?;
                let ty = Type::UnboxedRecord(
                    fields
                        .iter()
                        .map(|(name, field)| Ok((*name, source_type(field.ty())?)))
                        .collect::<Result<Vec<_>, BuildError>>()?,
                );
                (CoreType::Source(ty), TypedValueKind::UnboxedRecord(fields))
            }
        };
        let value = TypedValue::new(ty.clone(), kind);
        if let Some(expected) = expected {
            let actual = self.solver.resolve_core(&ty);
            let wanted = self.solver.resolve_core(expected);
            if representation_preserving(&actual, &wanted) {
                return Ok(TypedValue::new(
                    expected.clone(),
                    TypedValueKind::Reinterpret(Box::new(value)),
                ));
            }
            self.solver.subsume_core(&ty, expected)?;
        }
        Ok(value)
    }

    pub(super) fn comp(
        &mut self,
        comp: Comp,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        // The builder recurses per Core node, so a long `Bind` chain (a compiled
        // statement block) is deep recursion. The entry-point guard in
        // `build_typed` buys one segment; growing here, inside the recursion,
        // chains segments so depth is bounded by memory, not by one stack.
        on_core_stack(|| self.comp_inner(comp, expected))
    }

    fn return_comp(
        &mut self,
        value: Value,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        let value = self.value(value, expected.map(CompSig::result))?;
        self.finish_comp(
            CompSig::new(value.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(value),
            expected,
        )
    }

    #[allow(clippy::too_many_lines)] // One arm per computation form; the exhaustive match is the point.
    fn comp_inner(
        &mut self,
        comp: Comp,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        match comp {
            Comp::Return(value) => self.return_comp(value, expected),
            Comp::Bind(first, raw, rest) => {
                let first = *first;
                let rest = *rest;
                let (first, binder, rest) = if matches!(&first, Comp::Return(Value::Thunk(_))) {
                    // A suspended function is a checking form: its rank and
                    // latent row can be determined only by the continuation's
                    // use. Propagate that demand backwards across the bind.
                    let rest_retry = rest.clone();
                    let binder_ty = self.solver.fresh_core();
                    let speculative_binder = self.bind(raw, binder_ty.clone());
                    let rest_expected = expected.map(|expected| {
                        CompSig::new(expected.result().clone(), self.solver.fresh_row())
                    });
                    let pending_before = self.pending_handler_rows.len();
                    let speculative_rest =
                        self.comp(rest, rest_expected.as_ref()).map_err(|error| {
                            error.at(BuildContext::Binding {
                                binder: raw,
                                part: BindPart::Rest,
                            })
                        })?;
                    let retry_for_pending = self.pending_handler_rows.len() > pending_before;
                    self.unbind(raw);
                    let first_expected = CompSig::new(binder_ty, self.solver.fresh_row());
                    let first = self.comp(first, Some(&first_expected)).map_err(|error| {
                        error.at(BuildContext::Binding {
                            binder: raw,
                            part: BindPart::First,
                        })
                    })?;
                    // The speculative continuation may leave a mutable join
                    // placeholder in the binder while the producer stores a
                    // concrete closure witness. They can resolve identically
                    // here and diverge when a later sibling widens only the
                    // placeholder. Recheck the continuation whenever the raw
                    // stored witnesses differ; if both store the same
                    // placeholder, every later solution changes them together.
                    // A two-element container of pure functions admitted at an
                    // effectful element type is the smallest case.
                    let retry_exact =
                        retry_for_pending || speculative_binder.ty() != first.sig().result();
                    // The backwards demand is deliberately flexible. Once the
                    // producer has checked, the bind witness records its exact
                    // result rather than the broader metavariable shape used to
                    // type the continuation (notably a closure returned after an
                    // effectful prefix can itself be pure).
                    if retry_exact {
                        let binder = TypedBinder::new(raw, first.sig().result().clone());
                        self.bind(raw, first.sig().result().clone());
                        let rest =
                            self.comp(rest_retry, rest_expected.as_ref())
                                .map_err(|error| {
                                    error.at(BuildContext::Binding {
                                        binder: raw,
                                        part: BindPart::ExactRest,
                                    })
                                })?;
                        self.unbind(raw);
                        (first, binder, rest)
                    } else {
                        (first, speculative_binder, speculative_rest)
                    }
                } else {
                    let first = self.comp(first, None).map_err(|error| {
                        error.at(BuildContext::Binding {
                            binder: raw,
                            part: BindPart::First,
                        })
                    })?;
                    let binder = self.bind(raw, first.sig().result().clone());
                    let rest_expected = expected.map(|expected| {
                        CompSig::new(expected.result().clone(), self.solver.fresh_row())
                    });
                    let rest = self.comp(rest, rest_expected.as_ref()).map_err(|error| {
                        error.at(BuildContext::Binding {
                            binder: raw,
                            part: BindPart::Rest,
                        })
                    })?;
                    self.unbind(raw);
                    (first, binder, rest)
                };
                let effects = self
                    .solver
                    .union_rows(first.sig().effects(), rest.sig().effects())?;
                self.finish_comp(
                    CompSig::new(rest.sig().result().clone(), effects),
                    TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
                    expected,
                )
            }
            Comp::Force(value) => {
                let value = self.value(value, None)?;
                let forced = match self.solver.resolve_core(value.ty()) {
                    CoreType::Thunk(forced) => *forced,
                    CoreType::Source(Type::Exist(_)) => {
                        // Every force emitted by source elaboration exposes a
                        // suspended function. Constructing the closure is pure;
                        // the function body's latent row is inferred separately
                        // when the enclosing application is built.
                        let forced = CompSig::new(self.solver.fresh_core(), EffRow::Empty);
                        self.solver
                            .unify_core(value.ty(), &CoreType::Thunk(Box::new(forced.clone())))?;
                        forced
                    }
                    other => {
                        return Err(BuildError::NotAForm {
                            site: Site::At(FORCE_OPERAND),
                            expected: Form::Thunk,
                            found: other,
                        });
                    }
                };
                self.finish_comp(forced, TypedCompKind::Force(value), expected)
            }
            Comp::Lam(params, body) => {
                let expected_fn = expected.and_then(|expected| match expected.result() {
                    CoreType::Function(signature) => Some(signature.as_ref()),
                    _ => None,
                });
                let mut binders = Vec::new();
                for (index, raw) in params.iter().enumerate() {
                    let ty = expected_fn
                        .and_then(|signature| signature.params().get(index))
                        .cloned()
                        .unwrap_or_else(|| self.solver.fresh_core());
                    binders.push(self.bind(*raw, ty));
                }
                let body = self.comp(*body, None)?;
                if let Some(expected_fn) = expected_fn {
                    self.solver.subsume_sig(body.sig(), expected_fn.body())?;
                }
                for raw in params.into_iter().rev() {
                    self.unbind(raw);
                }
                let latent = if let Some(expected_fn) = expected_fn {
                    expected_fn.body().clone()
                } else {
                    // Nothing has demanded this closure yet, and the consumer
                    // that will is reachable only after it is built: an element
                    // of a list literal is typed before the sibling that fixes
                    // the element type, and the container fixes it invariantly.
                    // Recording the body's own row rigidly leaves a pure element
                    // at the empty row where the binder that names it describes
                    // the wider one, so keep the row open and bounded below by
                    // what the body performs.
                    let row = self.solver.fresh_latent_row();
                    self.solver.constrain_row_join(&row, body.sig().effects())?;
                    CompSig::new(body.sig().result().clone(), row)
                };
                let signature = CoreFnSig::new(
                    expected_fn
                        .map(CoreFnSig::quantifiers)
                        .unwrap_or_default()
                        .to_vec(),
                    binders.iter().map(|binder| binder.ty().clone()).collect(),
                    latent,
                );
                self.finish_comp(
                    CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
                    TypedCompKind::Lam(binders, Box::new(body)),
                    expected,
                )
            }
            Comp::App(callee, args) => {
                let callee = self.comp(*callee, None)?;
                let resolved_callee = self.solver.resolve_core(callee.sig().result());
                let declared = match resolved_callee {
                    CoreType::Function(declared) => declared,
                    CoreType::Source(Type::Exist(_)) => {
                        let inferred = CoreFnSig::new(
                            Vec::new(),
                            args.iter().map(|_| self.solver.fresh_core()).collect(),
                            CompSig::new(
                                expected
                                    .map(CompSig::result)
                                    .cloned()
                                    .unwrap_or_else(|| self.solver.fresh_core()),
                                self.solver.fresh_row(),
                            ),
                        );
                        self.solver.unify_core(
                            callee.sig().result(),
                            &CoreType::Function(Box::new(inferred.clone())),
                        )?;
                        Box::new(inferred)
                    }
                    other => {
                        return Err(BuildError::NotAForm {
                            site: Site::At(APPLICATION_CALLEE),
                            expected: Form::Function,
                            found: other,
                        });
                    }
                };
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let signature = instantiate_fn(&declared, &instantiation)?;
                if args.len() != signature.params().len() {
                    return Err(BuildError::Arity {
                        subject: BuildSubject::ComputedApplication,
                        found: args.len(),
                        expected: signature.params().len(),
                    });
                }
                let args = args
                    .into_iter()
                    .zip(signature.params())
                    .enumerate()
                    .map(|(index, (arg, expected))| {
                        self.value(arg, Some(expected)).map_err(|error| {
                            error.at(BuildContext::Argument {
                                index,
                                expected: self.solver.resolve_core(expected),
                            })
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let effects = self
                    .solver
                    .union_rows(callee.sig().effects(), signature.body().effects())?;
                self.finish_comp(
                    CompSig::new(signature.body().result().clone(), effects),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation,
                        args,
                    },
                    expected,
                )
            }
            Comp::If(condition, yes, no) => {
                let condition = self.value(condition, Some(&CoreType::Source(Type::Bool)))?;
                let branch_result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                let yes_expected = CompSig::new(branch_result.clone(), self.solver.fresh_row());
                let no_expected = CompSig::new(branch_result, self.solver.fresh_row());
                let yes = self.comp(*yes, Some(&yes_expected))?;
                let no = self.comp(*no, Some(&no_expected))?;
                self.solver
                    .unify_core(yes.sig().result(), no.sig().result())?;
                let effects = self
                    .solver
                    .union_rows(yes.sig().effects(), no.sig().effects())?;
                self.finish_comp(
                    CompSig::new(yes.sig().result().clone(), effects),
                    TypedCompKind::If(condition, Box::new(yes), Box::new(no)),
                    expected,
                )
            }
            Comp::Prim(op, lhs, rhs) => self.primitive(op, lhs, rhs, expected),
            Comp::Call(callee, args) => self.call(callee, args, expected),
            Comp::Io(op, args) => self.io(op, args, expected),
            Comp::Error(value) => {
                let value = self.value(value, None)?;
                let result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                let effects = expected
                    .map(CompSig::effects)
                    .cloned()
                    .unwrap_or(EffRow::Empty);
                self.finish_comp(
                    CompSig::new(result, effects),
                    TypedCompKind::Error(value),
                    expected,
                )
            }
            Comp::Case(scrutinee, arms) => self.case(scrutinee, arms, expected),
            Comp::FloatBuiltin(op, value) => {
                let signature = intrinsic_sig(op.signature())?;
                let value = self.value(value, signature.params().first())?;
                self.finish_comp(
                    signature.body().clone(),
                    TypedCompKind::FloatBuiltin(op, value),
                    expected,
                )
            }
            Comp::Neg(lane, value) => {
                let ty = match lane {
                    NegLane::Int => Type::Int,
                    NegLane::I64 => Type::I64,
                    NegLane::Float => Type::Float,
                };
                let value = self.value(value, Some(&CoreType::Source(ty.clone())))?;
                self.finish_comp(
                    CompSig::new(CoreType::Source(ty), EffRow::Empty),
                    TypedCompKind::Neg(lane, value),
                    expected,
                )
            }
            Comp::UnboxedProject(value, field) => {
                let value = self.value(value, None)?;
                let result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                self.finish_comp(
                    CompSig::new(result, EffRow::Empty),
                    TypedCompKind::UnboxedProject(value, field),
                    expected,
                )
            }
            Comp::Do(operation, args) => self.operation(operation, args, expected),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => self.handle(
                *body,
                return_var,
                return_body.map(|body| *body),
                &ops,
                expected,
            ),
            Comp::Mask(effects, body) => {
                let body = self.comp(*body, None)?;
                let residual = subtract_names(body.sig().effects(), &effects);
                self.finish_comp(
                    CompSig::new(body.sig().result().clone(), residual),
                    TypedCompKind::Mask(effects, Box::new(body)),
                    expected,
                )
            }
            Comp::StrBuiltin(op, args) => self.builtin(op, args, expected),
            Comp::Dup(_)
            | Comp::Drop(_)
            | Comp::WithReuse { .. }
            | Comp::Reuse(..)
            | Comp::RefNew(_)
            | Comp::RefGet(_)
            | Comp::RefSet(..)
            | Comp::InitAt(..) => Err(BuildError::RuntimeNode),
        }
    }

    fn primitive(
        &mut self,
        op: CoreOp,
        lhs: Value,
        rhs: Value,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        let (operand, result) = match op {
            Add | Sub | Mul | Div | Rem => (CoreType::Source(Type::Int), Type::Int),
            Addf | Subf | Mulf | Divf => (CoreType::Source(Type::Float), Type::Float),
            Eqf | Nef | Ltf | Lef | Gtf | Gef => (CoreType::Source(Type::Float), Type::Bool),
            Eq | Ne | Lt | Le | Gt | Ge => {
                let operand = self.solver.fresh_core();
                (operand, Type::Bool)
            }
        };
        let lhs = self.value(lhs, Some(&operand))?;
        let rhs = self.value(rhs, Some(&operand))?;
        self.finish_comp(
            CompSig::new(CoreType::Source(result), EffRow::Empty),
            TypedCompKind::Prim(op, lhs, rhs),
            expected,
        )
    }

    fn call(
        &mut self,
        callee: Sym,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        let declared = self
            .globals
            .get(&callee)
            .ok_or(BuildError::UnknownName {
                kind: NameKind::Function,
                name: callee,
            })?
            .clone();
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let signature = instantiate_fn(&declared, &instantiation)?;
        if args.len() != signature.params().len() {
            return Err(BuildError::Arity {
                subject: BuildSubject::Call(callee),
                found: args.len(),
                expected: signature.params().len(),
            });
        }
        let args = args
            .into_iter()
            .zip(signature.params())
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            signature.body().clone(),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn io(
        &mut self,
        op: IoOp,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        if args.len() != op.arity() {
            return Err(BuildError::Arity {
                subject: BuildSubject::Io(op),
                found: args.len(),
                expected: op.arity(),
            });
        }
        let args = args
            .into_iter()
            .map(|arg| {
                let ty = match op {
                    IoOp::PrintF => Some(CoreType::Source(Type::Float)),
                    IoOp::PrintS => Some(CoreType::Source(Type::Str)),
                    IoOp::Srand => Some(CoreType::Source(Type::Int)),
                    IoOp::Print | IoOp::PrintNl | IoOp::ReadInt | IoOp::ReadLine | IoOp::Rand => {
                        None
                    }
                };
                self.value(arg, ty.as_ref())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = match op {
            IoOp::ReadInt | IoOp::Rand => Type::Int,
            IoOp::ReadLine => Type::Str,
            IoOp::Print | IoOp::PrintF | IoOp::PrintS | IoOp::PrintNl | IoOp::Srand => Type::Unit,
        };
        self.finish_comp(
            CompSig::new(CoreType::Source(result), EffRow::singleton(IO_EFFECT)),
            TypedCompKind::Io(op, args),
            expected,
        )
    }

    fn builtin(
        &mut self,
        op: Builtin,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        let unsigned_shared_lane =
            matches!(op, Builtin::I64Add | Builtin::I64Sub | Builtin::I64Mul)
                && (matches!(
                    expected.map(CompSig::result),
                    Some(CoreType::Source(Type::U64))
                ) || args.first().is_some_and(|arg| match arg {
                    Value::U64(_) => true,
                    Value::Var(name) => self.local(*name).is_some_and(|(_, ty)| {
                        self.solver.resolve_core(&ty) == CoreType::Source(Type::U64)
                    }),
                    _ => false,
                }));
        let declared = if unsigned_shared_lane {
            intrinsic_sig("(U64, U64) -> U64")?
        } else if let Some(signature) = op.signature() {
            intrinsic_sig(signature)?
        } else {
            self.verify_env
                .builtin_override(op)
                .ok_or(BuildError::MissingBuiltinSignature { builtin: op })?
                .clone()
        };
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let signature = instantiate_fn(&declared, &instantiation)?;
        if args.len() != signature.params().len() {
            return Err(BuildError::Arity {
                subject: BuildSubject::Builtin(op),
                found: args.len(),
                expected: signature.params().len(),
            });
        }
        let args = args
            .into_iter()
            .zip(signature.params())
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            signature.body().clone(),
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn operation(
        &mut self,
        name: Sym,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        let declared = self
            .verify_env
            .operation(name)
            .ok_or(BuildError::UnknownName {
                kind: NameKind::Operation,
                name,
            })?
            .clone();
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let operation = instantiate_operation(&declared, &instantiation)?;
        if args.len() != operation.params.len() {
            return Err(BuildError::Arity {
                subject: BuildSubject::Operation(name),
                found: args.len(),
                expected: operation.params.len(),
            });
        }
        let args = args
            .into_iter()
            .zip(&operation.params)
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            CompSig::new(
                operation.result,
                EffRow::canonical([operation.effect], EffRow::Empty),
            ),
            TypedCompKind::Do {
                operation: name,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn case(
        &mut self,
        scrutinee: Value,
        arms: Vec<(CorePat, Comp)>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        if arms.is_empty() {
            return Err(BuildError::CaseWithoutArms);
        }
        let scrutinee = self.value(scrutinee, None)?;
        let result = expected
            .map(CompSig::result)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_core());
        let mut effects = EffRow::Empty;
        let mut typed_arms = Vec::with_capacity(arms.len());
        for (pattern, body) in arms {
            let (pattern, raw_binders) = self.pattern(pattern, scrutinee.ty())?;
            let body_expected = CompSig::new(result.clone(), self.solver.fresh_row());
            let body = self.comp(body, Some(&body_expected))?;
            for raw in raw_binders.into_iter().rev() {
                self.unbind(raw);
            }
            effects = self.solver.union_rows(&effects, body.sig().effects())?;
            typed_arms.push((pattern, body));
        }
        self.finish_comp(
            CompSig::new(result, effects),
            TypedCompKind::Case(scrutinee, typed_arms),
            expected,
        )
    }

    fn pattern(
        &mut self,
        pattern: CorePat,
        scrutinee: &CoreType,
    ) -> Result<(TypedPattern, Vec<Sym>), BuildError> {
        match pattern {
            CorePat::Wild => Ok((TypedPattern::Wild, Vec::new())),
            CorePat::Var(raw) => Ok((
                TypedPattern::Var(self.bind(raw, scrutinee.clone())),
                vec![raw],
            )),
            CorePat::Tuple(fields) => {
                let field_count = fields.len();
                let resolved = self.solver.resolve_core(scrutinee);
                let field_types = match resolved {
                    CoreType::Source(Type::Tuple(types) | Type::UnboxedTuple(types))
                        if types.len() == fields.len() =>
                    {
                        types
                    }
                    CoreType::Source(Type::UnboxedRecord(record_fields))
                        if record_fields.len() == field_count =>
                    {
                        record_fields.into_iter().map(|(_, ty)| ty).collect()
                    }
                    _ => {
                        let types: Vec<_> =
                            fields.iter().map(|_| self.solver.fresh_type()).collect();
                        self.solver
                            .unify_core(scrutinee, &CoreType::Source(Type::Tuple(types.clone())))?;
                        types
                    }
                };
                let mut raw_binders = Vec::new();
                let fields = fields
                    .into_iter()
                    .zip(field_types)
                    .map(|(raw, ty)| {
                        raw.map(|raw| {
                            raw_binders.push(raw);
                            self.bind(raw, lower_value_type(&ty))
                        })
                    })
                    .collect();
                Ok((TypedPattern::Tuple(fields), raw_binders))
            }
            CorePat::Ctor(name, fields) => {
                let declared = self
                    .verify_env
                    .constructor(name)
                    .ok_or(BuildError::UnknownName {
                        kind: NameKind::PatternConstructor,
                        name,
                    })?
                    .clone();
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let constructor = instantiate_constructor(&declared, &instantiation)?;
                self.solver.unify_core(scrutinee, &constructor.result)?;
                if fields.len() != constructor.fields.len() {
                    return Err(BuildError::Arity {
                        subject: BuildSubject::Pattern(name),
                        found: fields.len(),
                        expected: constructor.fields.len(),
                    });
                }
                let mut raw_binders = Vec::new();
                let fields = fields
                    .into_iter()
                    .zip(constructor.fields)
                    .map(|(raw, ty)| {
                        raw.map(|raw| {
                            raw_binders.push(raw);
                            self.bind(raw, ty)
                        })
                    })
                    .collect();
                Ok((
                    TypedPattern::Ctor {
                        name,
                        instantiation,
                        fields,
                    },
                    raw_binders,
                ))
            }
        }
    }

    fn handle(
        &mut self,
        body: Comp,
        return_var: Option<Sym>,
        return_body: Option<Comp>,
        ops: &CheckedHandler,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, BuildError> {
        if return_var.is_some() != return_body.is_some() {
            return Err(BuildError::IncompleteHandlerReturn);
        }
        let body = self.comp(body, None)?;
        let result = expected
            .map(CompSig::result)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_core());
        let outer_effects = expected
            .map(CompSig::effects)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_row());
        let outer = CompSig::new(result.clone(), outer_effects.clone());
        let mut clause_results = Vec::new();

        let (return_binder, return_body, mut clause_effects) =
            if let (Some(raw), Some(return_body)) = (return_var, return_body) {
                let binder = self.bind(raw, body.sig().result().clone());
                let return_body = self.comp(return_body, None)?;
                self.unbind(raw);
                clause_results.push(return_body.sig().result().clone());
                let effects = return_body.sig().effects().clone();
                (Some(binder), Some(Box::new(return_body)), effects)
            } else {
                clause_results.push(body.sig().result().clone());
                (None, None, EffRow::Empty)
            };

        let mut handled = BTreeMap::new();
        let mut typed_ops = Vec::new();
        for arm in ops.arms().iter().cloned() {
            let declared = self
                .verify_env
                .operation(arm.name)
                .ok_or(BuildError::UnknownName {
                    kind: NameKind::HandledOperation,
                    name: arm.name,
                })?
                .clone();
            let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
            let operation = instantiate_operation(&declared, &instantiation)?;
            if arm.params.len() != operation.params.len() {
                return Err(BuildError::Arity {
                    subject: BuildSubject::HandlerOperation(arm.name),
                    found: arm.params.len(),
                    expected: operation.params.len(),
                });
            }
            let mut params = Vec::new();
            for (raw, ty) in arm.params.iter().copied().zip(&operation.params) {
                params.push(self.bind(raw, ty.clone()));
            }
            let resume_ty = CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![operation.result.clone()],
                    outer.clone(),
                ))),
                EffRow::Empty,
            )));
            let resume = self.bind(arm.resume, resume_ty);
            let arm_body = self
                .comp(arm.body, None)
                .map_err(|error| error.at(BuildContext::HandlerOperationBody(arm.name)))?;
            self.unbind(arm.resume);
            for raw in arm.params.into_iter().rev() {
                self.unbind(raw);
            }
            clause_effects = self
                .solver
                .union_rows(&clause_effects, arm_body.sig().effects())?;
            clause_results.push(arm_body.sig().result().clone());
            handled.insert(arm.name, operation.effect);
            typed_ops.push(TypedHandleOp::new(
                arm.name,
                instantiation,
                params,
                resume,
                arm_body,
            ));
        }

        let mut joined_result = clause_results
            .first()
            .cloned()
            .ok_or(BuildError::HandlerWithoutResultClause)?;
        for clause_result in clause_results.iter().skip(1) {
            joined_result = self.solver.join_core(&joined_result, clause_result)?;
        }
        self.solver.constrain_join(&result, &joined_result)?;

        let handled: BTreeMap<_, _> = handled
            .into_iter()
            .map(|(name, label)| {
                (
                    name,
                    Label {
                        name: label.name,
                        args: label
                            .args
                            .iter()
                            .map(|ty| self.solver.resolve_type(ty))
                            .collect(),
                    },
                )
            })
            .collect();
        let forwarded = self.lower_residual_forwarding(&handled);
        let body_effects = self.solver.resolve_row(body.sig().effects());
        if body_effects.labels().is_empty()
            && matches!(body_effects.tail(), EffRow::Exist(_))
            && !handled.is_empty()
        {
            // Continuation-directed checking can build a handler before a local
            // thunk's latent row is known. Keep the subtraction equation until
            // that thunk is checked; linking the handler output directly to the
            // unresolved body row would retain an effect that a now-known
            // exhaustive clause should discharge.
            self.pending_handler_rows.push(PendingHandlerRow {
                target: outer_effects.clone(),
                body: body.sig().effects().clone(),
                handled: handled.clone(),
                clauses: clause_effects.clone(),
            });
        } else {
            let effects = self.derive_handler_effects(
                &body_effects,
                &handled,
                &clause_effects,
                &outer_effects,
            )?;
            self.solver.constrain_row_join(&outer_effects, &effects)?;
        }
        let ops = TypedHandler::new(typed_ops)
            .map_err(BuildError::DuplicateHandlerOperation)?
            .with_forwarded(forwarded);
        let derived_effects = outer.effects().clone();
        let expected_effects = expected.map(|signature| signature.effects().clone());
        self.finish_comp(
            outer,
            TypedCompKind::Handle {
                body: Box::new(body),
                return_binder,
                return_body,
                ops,
            },
            expected,
        )
        .map_err(|error| {
            error.at(BuildContext::HandlerEffects {
                derived: derived_effects,
                expected: expected_effects,
            })
        })
    }

    fn derive_handler_effects(
        &mut self,
        body_effects: &EffRow,
        handled: &BTreeMap<Sym, Label>,
        clause_effects: &EffRow,
        outer_effects: &EffRow,
    ) -> Result<EffRow, BuildError> {
        let discharged = self.exhaustively_handled_labels(body_effects, handled);
        // Matching a parametric arm can solve type arguments that were still
        // existential in the body's label. Re-zonk before exact set
        // subtraction so the discharged witness and body label agree.
        let body_effects = self.solver.resolve_row(body_effects);
        let residual = subtract_labels(&body_effects, &discharged);
        let resolved_outer = self.solver.resolve_row(outer_effects);
        let resolved_clauses = self.solver.resolve_row(clause_effects);
        if matches!(resolved_outer, EffRow::Exist(_)) && resolved_clauses.tail() == &resolved_outer
        {
            // Resumption clauses carry the handler's own row recursively. The
            // least fixed point of `outer = residual | clauses | outer` is the
            // union of the non-recursive labels over the residual's tail. The
            // union must run through `union_rows`, not a raw label chain: the
            // residual can spell a local-state effect in the legacy
            // zero-argument form while the clause row carries the recovered
            // cell type, and only the union's merge collapses the two
            // spellings into one instantiation.
            let clause_labels = EffRow::canonical(
                resolved_clauses.labels().into_iter().cloned(),
                EffRow::Empty,
            );
            self.solver
                .union_rows(&residual, &clause_labels)
                .map_err(BuildError::from)
        } else {
            self.solver
                .union_rows(&residual, &resolved_clauses)
                .map_err(BuildError::from)
        }
    }

    // The first born-typed lowering: make the implicit fall-through edges of a
    // partial handler explicit as checked witness data. Erasure drops the
    // witnesses because both executable handler tiers already implement the
    // same forward-and-reperform edge from an absent clause.
    fn lower_residual_forwarding(&self, arms: &BTreeMap<Sym, Label>) -> Vec<TypedForward> {
        let effects: BTreeMap<Sym, Label> = arms
            .values()
            .map(|label| (label.name, label.clone()))
            .collect();
        self.verify_env
            .operations()
            .iter()
            .filter_map(|(operation, declared)| {
                effects
                    .get(&declared.effect().name)
                    .filter(|_| !arms.contains_key(operation))
                    .cloned()
                    .map(|effect| TypedForward::new(*operation, effect))
            })
            .collect()
    }

    fn exhaustively_handled_labels(
        &mut self,
        body: &EffRow,
        arms: &BTreeMap<Sym, Label>,
    ) -> BTreeSet<Label> {
        let mut discharged = BTreeSet::new();
        for label in body.labels() {
            let declared: Vec<_> = self
                .verify_env
                .operations()
                .iter()
                .filter(|(_, operation)| operation.effect().name == label.name)
                .map(|(name, _)| *name)
                .collect();
            if declared.is_empty() {
                continue;
            }
            let mut exhaustive = true;
            let mut trial = self.solver.clone();
            for name in declared {
                let Some(handled) = arms.get(&name) else {
                    exhaustive = false;
                    break;
                };
                if handled.name != label.name || handled.args.len() != label.args.len() {
                    exhaustive = false;
                    break;
                }
                for (handled, body) in handled.args.iter().zip(&label.args) {
                    if trial.unify_type(handled, body).is_err() {
                        exhaustive = false;
                        break;
                    }
                }
                if !exhaustive {
                    break;
                }
            }
            if exhaustive {
                self.solver = trial;
                discharged.insert(Label {
                    name: label.name,
                    args: label
                        .args
                        .iter()
                        .map(|ty| self.solver.resolve_type(ty))
                        .collect(),
                });
            }
        }
        discharged
    }
}
