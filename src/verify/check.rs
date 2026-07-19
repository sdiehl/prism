//! The logical checker: the dedicated sort/scope/eligibility
//! check for `logic fn` declarations and `requires`/`ensures` contract clauses.
//!
//! It consumes the resolved surface program before contracts are erased at the
//! `Core` boundary, resolves each logical name in its own small logical scope
//! (parameters, the `ensures` result binder, and earlier logical declarations),
//! elaborates the supported first-order fragment into the internal
//! [`LogicExpr`]/[`Contract`], and proves it well-sorted with [`wf`]. Calls to a
//! `logic fn` are inlined (they are non-recursive total abbreviations), so a
//! checked contract is a pure `Bool`/`Int` proposition with no uninterpreted
//! applications.
//!
//! It runs no HM inference and installs no runtime check: a malformed contract is
//! an ordinary source error, a valid one leaves every runtime artifact untouched,
//! and no solver is consulted. Diagnostics point at the smallest offending logical
//! subexpression.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{BinOp, Decl, Expr, Program, Span, Suffix, Ty, S};
use crate::verify::logic::{Contract, LogicExpr, LogicSort, VarId};
use crate::verify::{interface::VerificationInterface, normalize, wf};

/// A checked logical declaration: its parameter sorts, result sort, and body
/// elaborated over the parameter binders `VarId(0..params.len())`. The body is
/// fully inlined (calls to earlier logical declarations are already substituted),
/// so it contains no uninterpreted applications.
struct LogicDef {
    params: Vec<LogicSort>,
    result: LogicSort,
    body: LogicExpr,
}

pub(crate) struct Checker {
    // Logical declarations checked so far, by source name; a later one may call an
    // earlier one, never itself or a later one.
    logic: BTreeMap<String, LogicDef>,
    // Runtime function names, so a contract referencing one gets the pointed
    // "not a logical declaration" diagnostic rather than "unresolved".
    runtime_fns: BTreeSet<String>,
    // When set, `elab` records each logical subexpression's source range and sort,
    // for the documentation type-span tooltips. `None` on the check and VC paths,
    // so those pay nothing.
    record: Option<RefCell<Vec<(usize, usize, LogicSort)>>>,
}

/// The name-to-binder environment a logical expression is elaborated against:
/// parameter `i` is `VarId(i)`, and an `ensures` clause appends the result binder
/// last. A later binding shadows an earlier one of the same name.
struct Scope {
    binders: Vec<(String, LogicSort)>,
}

impl Scope {
    fn get(&self, name: &str) -> Option<(VarId, LogicSort)> {
        self.binders
            .iter()
            .enumerate()
            .rev()
            .find(|(_, (n, _))| n == name)
            .map(|(i, (_, s))| (VarId(u32::try_from(i).unwrap_or(u32::MAX)), *s))
    }
}

/// Check every `logic fn` and every contracted `fn` in `prog`, returning the
/// module's verification interface. The interface digest is a pure function of the
/// logical content, independent of the runtime Core hash.
///
/// # Errors
/// A malformed logical declaration or contract clause, reported at the smallest
/// offending source range.
pub(crate) fn check_program(prog: &Program) -> Result<VerificationInterface, TypeError> {
    let checker = Checker::build(prog)?;
    let logic_digests = checker
        .logic
        .iter()
        .map(|(name, def)| {
            (
                name.clone(),
                normalize::logic_def_digest(&def.params, def.result, &def.body),
            )
        })
        .collect();
    let mut contract_digests = BTreeMap::new();
    for d in &prog.fns {
        if d.requires.is_empty() && d.ensures.is_empty() {
            continue;
        }
        let contract = checker.checked_contract(d)?;
        contract_digests.insert(d.name.clone(), normalize::contract_digest(&contract));
    }
    Ok(VerificationInterface::new(logic_digests, contract_digests))
}

impl Checker {
    /// Check every `logic fn` and build the logical environment (signatures and
    /// inlined bodies). Contracts are checked separately, per function.
    pub(crate) fn build(prog: &Program) -> Result<Self, TypeError> {
        Self::build_with(prog, false)
    }

    fn build_with(prog: &Program, record: bool) -> Result<Self, TypeError> {
        let runtime_fns = prog.fns.iter().map(|d| d.name.clone()).collect();
        let mut checker = Self {
            logic: BTreeMap::new(),
            runtime_fns,
            record: record.then(|| RefCell::new(Vec::new())),
        };
        for d in &prog.logic_fns {
            if checker.logic.contains_key(&d.name) {
                return Err(ErrKind::LogicDuplicate {
                    name: d.name.clone(),
                }
                .at(d.span));
            }
            let def = checker.check_logic_fn(d)?;
            checker.logic.insert(d.name.clone(), def);
        }
        Ok(checker)
    }

    /// The source range and sort of every logical subexpression in `prog`, for the
    /// documentation type-span tooltips. Best-effort: a program whose logical
    /// declarations are malformed (the check path reports that) yields no spans,
    /// and a per-function contract error is skipped rather than propagated.
    pub(crate) fn logic_typespans(prog: &Program) -> Vec<(usize, usize, LogicSort)> {
        let Ok(checker) = Self::build_with(prog, true) else {
            return Vec::new();
        };
        for d in &prog.fns {
            if !d.requires.is_empty() || !d.ensures.is_empty() {
                let _ = checker.check_contract(d);
            }
        }
        checker.record.map(RefCell::into_inner).unwrap_or_default()
    }

    /// A well-formed contract, re-verified independently by `wf`.
    pub(crate) fn checked_contract(&self, d: &Decl) -> Result<Contract, TypeError> {
        let contract = self.check_contract(d)?;
        // Independent re-verification of the built term (defense in depth): the
        // elaborator already sorted every node, so a failure here is a compiler
        // bug, not a source error.
        wf::check_contract(&contract).map_err(|e| TypeError::InternalInvariant {
            msg: format!("built an ill-sorted contract for `{}`: {e:?}", d.name),
        })?;
        Ok(contract)
    }

    /// Elaborate a function's body into a logical term over its parameter binders.
    /// The body must lie in the scalar fragment (`elab` rejects anything else),
    /// so an error here is the "unsupported for verification" (pending) signal for
    /// VC generation, distinct from a malformed contract. The body's sort must
    /// match the declared result.
    pub(crate) fn elab_body(
        &self,
        d: &Decl,
        params: &[LogicSort],
        result: LogicSort,
    ) -> Result<LogicExpr, TypeError> {
        let scope = Scope {
            binders: d
                .params
                .iter()
                .map(|p| p.name.clone())
                .zip(params.iter().copied())
                .collect(),
        };
        let (body, body_sort) = self.elab(&scope, &d.body)?;
        if body_sort != result {
            return Err(sort_err(
                "the function body",
                result,
                body_sort,
                d.body.span,
            ));
        }
        Ok(body)
    }

    /// Elaborate an arbitrary surface expression (a ranking measure, a path
    /// condition, or a recursive-call argument) into a logical term over `d`'s
    /// parameter binders `VarId(0..params.len())`. Like [`Self::elab_body`], an
    /// error is the "outside the supported fragment" signal, which the termination
    /// checker turns into a *pending* verdict rather than a rejection.
    pub(crate) fn elab_expr(
        &self,
        d: &Decl,
        params: &[LogicSort],
        e: &S<Expr>,
    ) -> Result<(LogicExpr, LogicSort), TypeError> {
        let scope = Scope {
            binders: d
                .params
                .iter()
                .map(|p| p.name.clone())
                .zip(params.iter().copied())
                .collect(),
        };
        self.elab(&scope, e)
    }

    fn check_logic_fn(&self, d: &Decl) -> Result<LogicDef, TypeError> {
        let params = param_sorts(d)?;
        let result = declared_sort(d.ret.as_ref(), d.span, "logical declaration result")?;
        let scope = Scope {
            binders: d
                .params
                .iter()
                .map(|p| p.name.clone())
                .zip(params.iter().copied())
                .collect(),
        };
        let (body, body_sort) = self.elab(&scope, &d.body)?;
        if body_sort != result {
            return Err(sort_err(
                "the logical declaration body",
                result,
                body_sort,
                d.body.span,
            ));
        }
        Ok(LogicDef {
            params,
            result,
            body,
        })
    }

    fn check_contract(&self, d: &Decl) -> Result<Contract, TypeError> {
        let params = param_sorts(d)?;
        let result = declared_sort(d.ret.as_ref(), d.span, "contracted function result")?;
        let param_scope = Scope {
            binders: d
                .params
                .iter()
                .map(|p| p.name.clone())
                .zip(params.iter().copied())
                .collect(),
        };
        let mut requires = Vec::new();
        for r in &d.requires {
            requires.push(self.clause(&param_scope, r, "requires")?);
        }
        let mut ensures = Vec::new();
        for (binder, p) in &d.ensures {
            let mut ens = param_scope.binders.clone();
            ens.push((binder.clone(), result));
            let scope = Scope { binders: ens };
            ensures.push(self.clause(&scope, p, "ensures")?);
        }
        Ok(Contract {
            params,
            requires,
            result,
            ensures,
        })
    }

    /// Elaborate a clause and require it to be `Bool`.
    fn clause(&self, scope: &Scope, e: &S<Expr>, kind: &str) -> Result<LogicExpr, TypeError> {
        let (logic, sort) = self.elab(scope, e)?;
        if sort != LogicSort::Bool {
            return Err(ErrKind::LogicSort {
                detail: format!(
                    "a `{kind}` clause must be Bool, this is {}",
                    sort_name(sort)
                ),
            }
            .at(e.span));
        }
        Ok(logic)
    }

    /// Elaborate a surface expression into a logical term and its sort, recording
    /// its source range and sort when the checker is in tooltip mode.
    fn elab(&self, scope: &Scope, e: &S<Expr>) -> Result<(LogicExpr, LogicSort), TypeError> {
        let result = self.elab_inner(scope, e)?;
        if let Some(record) = &self.record {
            record
                .borrow_mut()
                .push((e.span.start, e.span.end, result.1));
        }
        Ok(result)
    }

    fn elab_inner(&self, scope: &Scope, e: &S<Expr>) -> Result<(LogicExpr, LogicSort), TypeError> {
        let span = e.span;
        match &e.node {
            Expr::Int(lit) => match lit.suffix {
                Suffix::None => Ok((LogicExpr::Int(lit.value.clone()), LogicSort::Int)),
                Suffix::I64 | Suffix::U64 => Err(ErrKind::LogicUnsupported {
                    detail: "a fixed-width integer literal (I64/U64 are bit-vectors)".into(),
                }
                .at(span)),
            },
            Expr::Bool(b) => Ok((LogicExpr::boolean(*b), LogicSort::Bool)),
            Expr::Neg(x) => Ok((
                LogicExpr::neg(self.expect(scope, x, LogicSort::Int)?),
                LogicSort::Int,
            )),
            Expr::Bin(op, l, r) => self.bin(scope, *op, l, r, span),
            Expr::If(c, t, e2) => {
                let cond = self.expect(scope, c, LogicSort::Bool)?;
                let (then, sort) = self.elab(scope, t)?;
                let els = self.expect(scope, e2, sort)?;
                Ok((LogicExpr::ite(cond, then, els), sort))
            }
            Expr::Var(name) => self.var(scope, name, span),
            Expr::Call(f, args) => self.call(scope, f, args, span),
            // A redundant type annotation on a contract subterm is harmless; the
            // sort comes from the term, and the annotation is ignored.
            Expr::Ann(inner, _) => self.elab(scope, inner),
            other => Err(ErrKind::LogicUnsupported {
                detail: describe(other).to_string(),
            }
            .at(span)),
        }
    }

    fn expect(&self, scope: &Scope, e: &S<Expr>, want: LogicSort) -> Result<LogicExpr, TypeError> {
        let (logic, got) = self.elab(scope, e)?;
        if got == want {
            Ok(logic)
        } else {
            Err(sort_err("this operand", want, got, e.span))
        }
    }

    fn bin(
        &self,
        scope: &Scope,
        op: BinOp,
        l: &S<Expr>,
        r: &S<Expr>,
        span: Span,
    ) -> Result<(LogicExpr, LogicSort), TypeError> {
        match op {
            BinOp::And => Ok((self.both_bool(scope, l, r, true)?, LogicSort::Bool)),
            BinOp::Or => Ok((self.both_bool(scope, l, r, false)?, LogicSort::Bool)),
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let a = self.expect(scope, l, LogicSort::Int)?;
                let b = self.expect(scope, r, LogicSort::Int)?;
                Ok((compare(op, a, b), LogicSort::Bool))
            }
            BinOp::Eq | BinOp::Ne => {
                let (a, sort) = self.elab(scope, l)?;
                let b = self.expect(scope, r, sort)?;
                let eq = LogicExpr::eq(a, b);
                Ok((if op == BinOp::Ne { LogicExpr::not(eq) } else { eq }, LogicSort::Bool))
            }
            BinOp::Add => {
                let a = self.expect(scope, l, LogicSort::Int)?;
                let b = self.expect(scope, r, LogicSort::Int)?;
                Ok((LogicExpr::add(vec![a, b]), LogicSort::Int))
            }
            BinOp::Sub => {
                let a = self.expect(scope, l, LogicSort::Int)?;
                let b = self.expect(scope, r, LogicSort::Int)?;
                Ok((LogicExpr::sub(a, b), LogicSort::Int))
            }
            BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Pow => Err(ErrKind::LogicUnsupported {
                detail: format!(
                    "the `{}` operator (nonlinear arithmetic and division are not in the first fragment)",
                    bin_symbol(op)
                ),
            }
            .at(span)),
        }
    }

    fn both_bool(
        &self,
        scope: &Scope,
        l: &S<Expr>,
        r: &S<Expr>,
        and: bool,
    ) -> Result<LogicExpr, TypeError> {
        let a = self.expect(scope, l, LogicSort::Bool)?;
        let b = self.expect(scope, r, LogicSort::Bool)?;
        Ok(if and {
            LogicExpr::and(vec![a, b])
        } else {
            LogicExpr::or(vec![a, b])
        })
    }

    fn var(
        &self,
        scope: &Scope,
        name: &str,
        span: Span,
    ) -> Result<(LogicExpr, LogicSort), TypeError> {
        if let Some((vid, sort)) = scope.get(name) {
            return Ok((LogicExpr::var(vid), sort));
        }
        if let Some(def) = self.logic.get(name) {
            if def.params.is_empty() {
                return Ok((def.body.clone(), def.result));
            }
            return Err(ErrKind::LogicArity {
                name: name.to_string(),
                expected: def.params.len(),
                got: 0,
            }
            .at(span));
        }
        Err(self.unbound(name, span))
    }

    fn call(
        &self,
        scope: &Scope,
        f: &S<Expr>,
        args: &[S<Expr>],
        span: Span,
    ) -> Result<(LogicExpr, LogicSort), TypeError> {
        let Expr::Var(name) = &f.node else {
            return Err(ErrKind::LogicUnsupported {
                detail: "an indirect or higher-order call".into(),
            }
            .at(span));
        };
        let Some(def) = self.logic.get(name) else {
            return Err(self.unbound(name, f.span));
        };
        if args.len() != def.params.len() {
            return Err(ErrKind::LogicArity {
                name: name.clone(),
                expected: def.params.len(),
                got: args.len(),
            }
            .at(span));
        }
        let mut logic_args = Vec::with_capacity(args.len());
        for (arg, &want) in args.iter().zip(&def.params) {
            logic_args.push(self.expect(scope, arg, want)?);
        }
        Ok((subst(&def.body, &logic_args), def.result))
    }

    fn unbound(&self, name: &str, span: Span) -> TypeError {
        if self.runtime_fns.contains(name) {
            ErrKind::LogicNotLogical {
                name: name.to_string(),
            }
            .at(span)
        } else {
            ErrKind::LogicUnresolved {
                name: name.to_string(),
            }
            .at(span)
        }
    }
}

/// Substitute `args` for the parameter binders `VarId(0..)` of an inlined body.
/// The body carries no uninterpreted applications, so the `App` arm is inert.
///
/// Reused by the termination checker to instantiate a callee's measure or
/// precondition at a call site: `args[i]` is the term passed in parameter
/// position `i`, so `subst(measure, call_args)` is the measure at the callee.
pub(crate) fn subst(e: &LogicExpr, args: &[LogicExpr]) -> LogicExpr {
    match e {
        LogicExpr::Var(v) => args[v.0 as usize].clone(),
        LogicExpr::Builtin(b, xs) => {
            LogicExpr::Builtin(*b, xs.iter().map(|x| subst(x, args)).collect())
        }
        LogicExpr::App(f, xs) => LogicExpr::App(*f, xs.iter().map(|x| subst(x, args)).collect()),
        LogicExpr::Bool(_) | LogicExpr::Int(_) => e.clone(),
    }
}

/// Replace one binder (the `ensures` result binder) with a term, leaving every
/// other variable untouched. Used by VC generation to substitute a function's
/// return value for `result`.
pub(crate) fn subst_var(e: &LogicExpr, target: VarId, replacement: &LogicExpr) -> LogicExpr {
    match e {
        LogicExpr::Var(v) if *v == target => replacement.clone(),
        LogicExpr::Var(_) | LogicExpr::Bool(_) | LogicExpr::Int(_) => e.clone(),
        LogicExpr::Builtin(b, xs) => LogicExpr::Builtin(
            *b,
            xs.iter()
                .map(|x| subst_var(x, target, replacement))
                .collect(),
        ),
        LogicExpr::App(f, xs) => LogicExpr::App(
            *f,
            xs.iter()
                .map(|x| subst_var(x, target, replacement))
                .collect(),
        ),
    }
}

fn compare(op: BinOp, a: LogicExpr, b: LogicExpr) -> LogicExpr {
    match op {
        BinOp::Lt => LogicExpr::lt(a, b),
        BinOp::Le => LogicExpr::le(a, b),
        BinOp::Gt => LogicExpr::gt(a, b),
        BinOp::Ge => LogicExpr::ge(a, b),
        _ => unreachable!("compare only handles the four ordering operators"),
    }
}

/// The logical sorts of a function's parameters when every one carries an
/// explicit `Int`/`Bool` annotation, or `None` if any parameter is unannotated or
/// of another type. The soft counterpart of [`param_sorts`]: the termination
/// checker uses it to decide a function is outside the scalar fragment (pending)
/// rather than raising a source error, since a `total fn` with a richer parameter
/// type is still valid Prism.
pub(crate) fn logical_param_sorts(d: &Decl) -> Option<Vec<LogicSort>> {
    d.params
        .iter()
        .map(|p| p.ty.as_ref().and_then(sort_of_ty))
        .collect()
}

const fn sort_of_ty(ty: &Ty) -> Option<LogicSort> {
    match ty {
        Ty::Int => Some(LogicSort::Int),
        Ty::Bool => Some(LogicSort::Bool),
        _ => None,
    }
}

const fn sort_name(s: LogicSort) -> &'static str {
    match s {
        LogicSort::Bool => "Bool",
        LogicSort::Int => "Int",
    }
}

fn sort_err(context: &str, expected: LogicSort, got: LogicSort, span: Span) -> TypeError {
    ErrKind::LogicSort {
        detail: format!(
            "{context} has sort {}, expected {}",
            sort_name(got),
            sort_name(expected)
        ),
    }
    .at(span)
}

fn unsupported_type(ty: &Ty, span: Span) -> TypeError {
    ErrKind::LogicUnsupported {
        detail: format!(
            "the type `{}` (only Int and Bool are in the first logical fragment)",
            crate::fmt::decl::fmt_ty(ty)
        ),
    }
    .at(span)
}

/// The logical sorts of a function's parameters. A contracted or logical
/// parameter must carry an explicit `Int`/`Bool` annotation.
fn param_sorts(d: &Decl) -> Result<Vec<LogicSort>, TypeError> {
    d.params
        .iter()
        .map(|p| {
            p.ty.as_ref().map_or_else(
                || {
                    Err(ErrKind::LogicUnsupported {
                        detail: format!(
                            "parameter `{}` needs an explicit `Int` or `Bool` type to appear in a contract",
                            p.name
                        ),
                    }
                    .at(d.span))
                },
                |ty| sort_of_ty(ty).ok_or_else(|| unsupported_type(ty, d.span)),
            )
        })
        .collect()
}

/// The logical sort of a declared result/parameter type, or a diagnostic.
fn declared_sort(ty: Option<&Ty>, span: Span, what: &str) -> Result<LogicSort, TypeError> {
    ty.map_or_else(
        || {
            Err(ErrKind::LogicUnsupported {
                detail: format!("{what} needs an explicit `Int` or `Bool` type"),
            }
            .at(span))
        },
        |ty| sort_of_ty(ty).ok_or_else(|| unsupported_type(ty, span)),
    )
}

const fn bin_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Pow => "^",
        _ => "?",
    }
}

/// A short human name for an unsupported surface node, for the diagnostic.
const fn describe(e: &Expr) -> &'static str {
    match e {
        Expr::Str(_) => "a string literal",
        Expr::Float(_) => "a floating-point literal",
        Expr::Char(_) => "a character literal",
        Expr::Unit => "the unit value",
        Expr::Let(..) => "a `let` binding",
        Expr::Lam(..) => "a lambda",
        Expr::Match(..) => "a `match` expression",
        Expr::List(..) => "a list literal",
        Expr::Tuple(..) => "a tuple",
        Expr::Hole(_) => "a typed hole",
        Expr::FieldAccess(..) | Expr::UnboxedField(..) => "a field access",
        Expr::RecordCreate(..) | Expr::UnboxedRecord(..) => "a record",
        Expr::Handle(..) => "a handler",
        Expr::Index(..) => "an index read",
        _ => "this expression form",
    }
}
