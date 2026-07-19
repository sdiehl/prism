//! The stable registry of logical builtins: the fixed first-order operators a
//! `LogicExpr` may apply. Each builtin has one home here for its frozen structural
//! `tag` (the only thing the structural digest sees), its canonical SMT-LIB
//! `symbol`, and its `arity` shape. Sort rules live beside the verifier in `wf`,
//! the single place that decides well-sortedness, so no operator string or arity
//! is re-typed elsewhere.

/// A fixed logical operator. Identity is the `tag`, which is frozen: append new
/// builtins with fresh tags, never renumber an existing one.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub(crate) enum LogicBuiltin {
    Not,
    And,
    Or,
    Implies,
    Ite,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Neg,
}

/// How many operands a builtin takes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Arity {
    Exactly(usize),
    AtLeast(usize),
}

impl LogicBuiltin {
    /// The frozen structural tag. Changing a value here changes every digest that
    /// names this operator, so the mapping is append-only.
    pub(crate) const fn tag(self) -> u16 {
        match self {
            Self::Not => 1,
            Self::And => 2,
            Self::Or => 3,
            Self::Implies => 4,
            Self::Ite => 5,
            Self::Eq => 6,
            Self::Lt => 7,
            Self::Le => 8,
            Self::Gt => 9,
            Self::Ge => 10,
            Self::Add => 11,
            Self::Sub => 12,
            Self::Neg => 13,
        }
    }

    /// The canonical SMT-LIB symbol. `Sub` and `Neg` share `-`, disambiguated by
    /// arity at the print site; their distinct tags keep them apart in the digest.
    pub(crate) const fn symbol(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::And => "and",
            Self::Or => "or",
            Self::Implies => "=>",
            Self::Ite => "ite",
            Self::Eq => "=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Add => "+",
            Self::Sub | Self::Neg => "-",
        }
    }

    pub(crate) const fn arity(self) -> Arity {
        match self {
            Self::Not | Self::Neg => Arity::Exactly(1),
            Self::Implies | Self::Eq | Self::Lt | Self::Le | Self::Gt | Self::Ge | Self::Sub => {
                Arity::Exactly(2)
            }
            Self::Ite => Arity::Exactly(3),
            Self::And | Self::Or | Self::Add => Arity::AtLeast(2),
        }
    }
}
