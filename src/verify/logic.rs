//! The canonical first-order logical IR that a verification obligation is built
//! from and that the SMT-LIB encoder consumes. A solver sees a `LogicExpr`, never
//! HIR or Core. It is deliberately small, total, and solver-neutral. Terms are
//! built through the constructors here and trusted only after `wf::check` proves
//! the whole obligation well-sorted.

use num_bigint::BigInt;

use crate::verify::registry::LogicBuiltin;

/// A logical sort. `Int` is mathematical (arbitrary precision), matching Prism's
/// `Int`. Bit-vector and datatype sorts are not yet supported; the supported
/// fragment is the `Bool` + `Int` quantifier-free linear-integer core.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub(crate) enum LogicSort {
    Bool,
    Int,
}

impl LogicSort {
    /// Frozen structural tag; append-only, like the builtin tags.
    pub(crate) const fn tag(self) -> u16 {
        match self {
            Self::Bool => 1,
            Self::Int => 2,
        }
    }

    pub(crate) const fn smtlib(self) -> &'static str {
        match self {
            Self::Bool => "Bool",
            Self::Int => "Int",
        }
    }
}

/// Index of a declared free variable within an [`Obligation`]; `VarId(i)` has sort
/// `obligation.vars[i]`. The canonical name is derived from the index, never a
/// source spelling, so renaming source cannot move a query's bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) struct VarId(pub(crate) u32);

/// Index of a declared uninterpreted function within an [`Obligation`];
/// `FuncId(i)` has signature `obligation.funcs[i]`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) struct FuncId(pub(crate) u32);

/// A first-order logical term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum LogicExpr {
    Var(VarId),
    Bool(bool),
    Int(BigInt),
    Builtin(LogicBuiltin, Vec<Self>),
    App(FuncId, Vec<Self>),
}

impl LogicExpr {
    pub(crate) const fn var(v: VarId) -> Self {
        Self::Var(v)
    }
    pub(crate) fn int(n: impl Into<BigInt>) -> Self {
        Self::Int(n.into())
    }
    pub(crate) const fn boolean(b: bool) -> Self {
        Self::Bool(b)
    }
    pub(crate) const fn func(f: FuncId, args: Vec<Self>) -> Self {
        Self::App(f, args)
    }
    pub(crate) fn not(a: Self) -> Self {
        Self::Builtin(LogicBuiltin::Not, vec![a])
    }
    pub(crate) const fn and(xs: Vec<Self>) -> Self {
        Self::Builtin(LogicBuiltin::And, xs)
    }
    pub(crate) const fn or(xs: Vec<Self>) -> Self {
        Self::Builtin(LogicBuiltin::Or, xs)
    }
    pub(crate) fn implies(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Implies, vec![a, b])
    }
    pub(crate) fn ite(c: Self, t: Self, e: Self) -> Self {
        Self::Builtin(LogicBuiltin::Ite, vec![c, t, e])
    }
    pub(crate) fn eq(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Eq, vec![a, b])
    }
    pub(crate) fn lt(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Lt, vec![a, b])
    }
    pub(crate) fn le(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Le, vec![a, b])
    }
    pub(crate) fn gt(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Gt, vec![a, b])
    }
    pub(crate) fn ge(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Ge, vec![a, b])
    }
    pub(crate) const fn add(xs: Vec<Self>) -> Self {
        Self::Builtin(LogicBuiltin::Add, xs)
    }
    pub(crate) fn sub(a: Self, b: Self) -> Self {
        Self::Builtin(LogicBuiltin::Sub, vec![a, b])
    }
    pub(crate) fn neg(a: Self) -> Self {
        Self::Builtin(LogicBuiltin::Neg, vec![a])
    }
}

/// The signature of an uninterpreted function.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct FuncDecl {
    pub(crate) params: Vec<LogicSort>,
    pub(crate) result: LogicSort,
}

/// A single verification obligation: prove `goal` under `assumptions`, over the
/// declared free variables and uninterpreted functions. The SMT query it lowers
/// to asserts the assumptions and the negated goal and asks `check-sat`; an
/// `unsat` answer discharges it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Obligation {
    pub(crate) vars: Vec<LogicSort>,
    pub(crate) funcs: Vec<FuncDecl>,
    pub(crate) assumptions: Vec<LogicExpr>,
    pub(crate) goal: LogicExpr,
}

/// The internal, source-free form of a function contract: the logical core that
/// the surface `requires`/`ensures` elaborates into and that VC generation
/// consumes alongside a function body. It fixes only the logic, not names or
/// spans (those live in checked HIR beside it).
///
/// Binder convention, positional and canonical: parameter `i` is the variable
/// `VarId(i)` for `i` in `0..params.len()`; the single result binder is
/// `VarId(params.len())` and is in scope only in `ensures`. `requires` may mention
/// the parameters; a reference to the result binder there is ill-formed. A
/// contract is trusted only after [`crate::verify::wf::check_contract`] proves it
/// well-sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Contract {
    pub(crate) params: Vec<LogicSort>,
    pub(crate) requires: Vec<LogicExpr>,
    pub(crate) result: LogicSort,
    pub(crate) ensures: Vec<LogicExpr>,
}

impl Contract {
    /// The result binder `VarId(params.len())`, in scope only in `ensures`.
    pub(crate) fn result_binder(&self) -> VarId {
        VarId(u32::try_from(self.params.len()).unwrap_or(u32::MAX))
    }
}
