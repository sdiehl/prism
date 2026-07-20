//! The independent well-formedness verifier for internal Logic IR. It proves an
//! [`Obligation`] is well-sorted: every variable and function reference resolves,
//! every builtin is applied at its arity and argument sorts, and every assumption
//! and the goal are `Bool`. It performs no inference and repairs nothing; it only
//! checks. Since the internal IR has no surface syntax, a failure here means a compiler bug
//! built an ill-formed obligation, so the error carries the canonical code rather
//! than surfacing as an opaque panic downstream.

use crate::error::{ErrorCode, SMT_LOGIC_WELLFORMED};
use crate::verify::logic::{Contract, FuncDecl, FuncId, LogicExpr, LogicSort, Obligation, VarId};
use crate::verify::registry::{Arity, LogicBuiltin};

/// A well-formedness failure. All variants carry [`SMT_LOGIC_WELLFORMED`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum WfError {
    UnknownVar(VarId),
    UnknownFunc(FuncId),
    BuiltinArity {
        symbol: &'static str,
        got: usize,
    },
    FuncArity {
        func: FuncId,
        expected: usize,
        got: usize,
    },
    Sort {
        context: &'static str,
        expected: LogicSort,
        got: LogicSort,
    },
    AssumptionNotBool(LogicSort),
    GoalNotBool(LogicSort),
    RequiresNotBool(LogicSort),
    EnsuresNotBool(LogicSort),
}

impl WfError {
    // Every variant shares one code, so `self` is unused today; the `&self`
    // accessor keeps parity with every other error type's `.code()` and lets a
    // future variant map to a distinct code without moving call sites.
    #[allow(clippy::unused_self)]
    pub(crate) const fn code(&self) -> ErrorCode {
        SMT_LOGIC_WELLFORMED
    }
}

/// The declaration context a term is sorted against: the free variables in scope
/// and the uninterpreted functions it may apply. Both an obligation and a contract
/// clause reduce to sorting their terms over one of these.
struct Env<'a> {
    vars: &'a [LogicSort],
    funcs: &'a [FuncDecl],
}

/// Prove `ob` well-formed: every assumption and the goal are `Bool` over a
/// well-sorted term tree.
pub(crate) fn check(ob: &Obligation) -> Result<(), WfError> {
    let env = Env {
        vars: &ob.vars,
        funcs: &ob.funcs,
    };
    for a in &ob.assumptions {
        let s = sort_of(&env, a)?;
        if s != LogicSort::Bool {
            return Err(WfError::AssumptionNotBool(s));
        }
    }
    let g = sort_of(&env, &ob.goal)?;
    if g != LogicSort::Bool {
        return Err(WfError::GoalNotBool(g));
    }
    Ok(())
}

/// Prove a [`Contract`] well-formed: every `requires` clause is `Bool` over the
/// parameters, and every `ensures` clause is `Bool` over the parameters plus the
/// result binder. Contracts declare no uninterpreted functions, so a
/// clause that applies one is rejected as an unknown function.
pub(crate) fn check_contract(c: &Contract) -> Result<(), WfError> {
    let req_env = Env {
        vars: &c.params,
        funcs: &[],
    };
    for r in &c.requires {
        let s = sort_of(&req_env, r)?;
        if s != LogicSort::Bool {
            return Err(WfError::RequiresNotBool(s));
        }
    }
    let mut ens_vars = c.params.clone();
    ens_vars.push(c.result);
    let ens_env = Env {
        vars: &ens_vars,
        funcs: &[],
    };
    for e in &c.ensures {
        let s = sort_of(&ens_env, e)?;
        if s != LogicSort::Bool {
            return Err(WfError::EnsuresNotBool(s));
        }
    }
    Ok(())
}

/// Infer the sort of a well-formed term, or report the first offending node.
fn sort_of(env: &Env<'_>, e: &LogicExpr) -> Result<LogicSort, WfError> {
    match e {
        LogicExpr::Var(v) => env
            .vars
            .get(v.0 as usize)
            .copied()
            .ok_or(WfError::UnknownVar(*v)),
        LogicExpr::Bool(_) => Ok(LogicSort::Bool),
        LogicExpr::Int(_) => Ok(LogicSort::Int),
        LogicExpr::Builtin(b, args) => builtin_sort(env, *b, args),
        LogicExpr::App(f, args) => {
            let decl = env
                .funcs
                .get(f.0 as usize)
                .ok_or(WfError::UnknownFunc(*f))?;
            if args.len() != decl.params.len() {
                return Err(WfError::FuncArity {
                    func: *f,
                    expected: decl.params.len(),
                    got: args.len(),
                });
            }
            for (arg, &want) in args.iter().zip(&decl.params) {
                expect(env, arg, want, "function argument")?;
            }
            Ok(decl.result)
        }
    }
}

/// Check `e` has exactly sort `want`.
fn expect(
    env: &Env<'_>,
    e: &LogicExpr,
    want: LogicSort,
    context: &'static str,
) -> Result<(), WfError> {
    let got = sort_of(env, e)?;
    if got == want {
        Ok(())
    } else {
        Err(WfError::Sort {
            context,
            expected: want,
            got,
        })
    }
}

const fn check_arity(b: LogicBuiltin, n: usize) -> Result<(), WfError> {
    let ok = match b.arity() {
        Arity::Exactly(k) => n == k,
        Arity::AtLeast(k) => n >= k,
    };
    if ok {
        Ok(())
    } else {
        Err(WfError::BuiltinArity {
            symbol: b.symbol(),
            got: n,
        })
    }
}

/// The sort rules for the builtin operators. This is the canonical home for
/// "which arguments must be what sort, and what does the result become"; the
/// registry owns tags/symbols/arity, this owns sorts.
fn builtin_sort(env: &Env<'_>, b: LogicBuiltin, args: &[LogicExpr]) -> Result<LogicSort, WfError> {
    use LogicBuiltin::{Add, And, Eq, Ge, Gt, Implies, Ite, Le, Lt, Neg, Not, Or, Sub};
    check_arity(b, args.len())?;
    match b {
        Not => {
            expect(env, &args[0], LogicSort::Bool, "not")?;
            Ok(LogicSort::Bool)
        }
        And | Or => {
            for a in args {
                expect(env, a, LogicSort::Bool, b.symbol())?;
            }
            Ok(LogicSort::Bool)
        }
        Implies => {
            expect(env, &args[0], LogicSort::Bool, "=>")?;
            expect(env, &args[1], LogicSort::Bool, "=>")?;
            Ok(LogicSort::Bool)
        }
        Ite => {
            expect(env, &args[0], LogicSort::Bool, "ite condition")?;
            let t = sort_of(env, &args[1])?;
            expect(env, &args[2], t, "ite branches")?;
            Ok(t)
        }
        Eq => {
            let l = sort_of(env, &args[0])?;
            expect(env, &args[1], l, "=")?;
            Ok(LogicSort::Bool)
        }
        Lt | Le | Gt | Ge => {
            expect(env, &args[0], LogicSort::Int, b.symbol())?;
            expect(env, &args[1], LogicSort::Int, b.symbol())?;
            Ok(LogicSort::Bool)
        }
        Add => {
            for a in args {
                expect(env, a, LogicSort::Int, "+")?;
            }
            Ok(LogicSort::Int)
        }
        Sub => {
            expect(env, &args[0], LogicSort::Int, "-")?;
            expect(env, &args[1], LogicSort::Int, "-")?;
            Ok(LogicSort::Int)
        }
        Neg => {
            expect(env, &args[0], LogicSort::Int, "-")?;
            Ok(LogicSort::Int)
        }
    }
}
