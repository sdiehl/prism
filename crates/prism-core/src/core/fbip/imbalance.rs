//! What the reference-count token machine rejected, and where.
//!
//! The balance check is an independent verifier: it re-simulates the inserted
//! dup/drop ops and fails when a count goes negative, when a binding leaves
//! scope holding tokens, or when two arms of a branch disagree. Every one of
//! those is an internal invariant violation, never a user diagnostic, so the
//! reason travels as data from the site that found it to the caller that
//! reports it. A test that wants to pin which invariant broke matches a
//! variant; before this it matched a substring of the sentence, which made the
//! sentence the contract and left it unsafe to reword.

use std::fmt;

use prism_common::sym::Sym;

use super::super::cbpv::Value;

/// The shapes the token machine can reject at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenFault {
    /// A binding left its scope still holding tokens: the pass under-dropped.
    ScopeExit { var: Sym, tokens: i64 },
    /// A closure capture left the thunk body still holding tokens. Captures
    /// start borrowed, so this is the same fault seen through a thunk.
    ThunkCapture { var: Sym, tokens: i64 },
    /// A use drove a count below zero: the pass under-dup'd, or dropped a value
    /// that was still live.
    BelowZero { var: Sym },
    /// A field extracted by a pattern was still holding tokens when its arm
    /// ended.
    ArmLeak { field: Sym },
    /// A borrowed argument was not live across the call that borrows it, so the
    /// callee would read a cell the caller had already released.
    BorrowNotLive { var: Sym, callee: Sym },
    /// Two arms of a branch left the same binding at different counts, so no
    /// single count describes the join.
    BranchDisagreement { var: Sym, left: i64, right: i64 },
    /// A borrowed argument was not a let-bound variable, so there is no binding
    /// for the loan to be held against.
    BorrowedArgNotBound { callee: Sym, arg: Box<Value> },
    /// A raw effect node reached the simulation. The check only holds on
    /// lowered Core (a `handle`'s clauses would go unsimulated), so an
    /// unlowered tree is refused rather than certified.
    UnloweredEffect { node: &'static str },
}

impl fmt::Display for TokenFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ScopeExit { var, tokens } => write!(f, "{var} ends with {tokens} tokens"),
            Self::ThunkCapture { var, tokens } => {
                write!(f, "thunk capture {var} ends with {tokens} tokens")
            }
            Self::BelowZero { var } => write!(f, "{var} consumed below zero"),
            Self::ArmLeak { field } => write!(f, "field {field} leaks in arm"),
            Self::BorrowNotLive { var, callee } => write!(
                f,
                "borrowed call argument {var} is not live through call to {callee}"
            ),
            Self::BranchDisagreement { var, left, right } => {
                write!(f, "branch disagreement on {var}: {left} vs {right}")
            }
            Self::BorrowedArgNotBound { callee, arg } => write!(
                f,
                "borrowed argument to {callee} is not a let-bound variable: {arg:?}"
            ),
            Self::UnloweredEffect { node } => write!(
                f,
                "unlowered `{node}` node reached the reuse linearity check; effect lowering must run first"
            ),
        }
    }
}

/// A token fault together with the declaration it was found in.
///
/// The function is optional because the same simulation runs over a thunk body
/// and over a fixture handed straight to the checker, where there is no
/// enclosing declaration to name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Imbalance {
    pub fault: TokenFault,
    pub function: Option<Sym>,
}

impl Imbalance {
    /// A fault with no declaration attributed to it yet.
    #[must_use]
    pub const fn new(fault: TokenFault) -> Self {
        Self {
            fault,
            function: None,
        }
    }

    /// Attribute a fault to the declaration whose body was being simulated.
    #[must_use]
    pub const fn in_function(fault: TokenFault, function: Sym) -> Self {
        Self {
            fault,
            function: Some(function),
        }
    }
}

impl From<TokenFault> for Imbalance {
    fn from(fault: TokenFault) -> Self {
        Self::new(fault)
    }
}

impl fmt::Display for Imbalance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.function {
            Some(function) => write!(f, "{function}: {}", self.fault),
            None => write!(f, "{}", self.fault),
        }
    }
}
