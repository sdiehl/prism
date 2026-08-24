//! Construction authority for whole-program typed Core.
//!
//! Passes may freely assemble unchecked witnesses, but only the independent
//! whole-program verifier can mint the authoritative phase marker consumed by
//! the next compiler transition.

use std::marker::PhantomData;

use super::verify::{check_functions, CoreViolation, TypedCorePhase, VerifyEnv};
use super::TypedCoreFn;
use crate::core::Core;

/// Whole-program typed Core awaiting independent verification at phase `P`.
///
/// This is the honest result type for rewrites and partial SCC work: its
/// functions carry witnesses, but the complete global table and phase-local
/// judgments have not yet been checked.
#[derive(Debug, PartialEq)]
pub struct UncheckedTypedCore<P> {
    fns: Vec<TypedCoreFn>,
    phase: PhantomData<fn() -> P>,
}

// Manual so a phase-generic caller can clone without requiring `P: Clone`.
impl<P> Clone for UncheckedTypedCore<P> {
    fn clone(&self) -> Self {
        Self::new(self.fns.clone())
    }
}

impl<P> UncheckedTypedCore<P> {
    /// Assemble functions without claiming that their witnesses verify.
    #[must_use]
    pub const fn new(fns: Vec<TypedCoreFn>) -> Self {
        Self {
            fns,
            phase: PhantomData,
        }
    }

    /// Functions in deterministic program order.
    #[must_use]
    pub fn functions(&self) -> &[TypedCoreFn] {
        &self.fns
    }

    /// Decompose an unchecked assembly for regrouping or another rewrite.
    #[must_use]
    pub fn into_functions(self) -> Vec<TypedCoreFn> {
        self.fns
    }
}

/// Independently verified whole-program typed Core at phase `P`.
///
/// There is intentionally no public `new` or `from_functions`: forgeable typed
/// nodes are valid verifier inputs, but only [`verify`] can mint this marker.
///
/// ```compile_fail
/// use prism_core::core::{TypedCore, TypedCoreFn, TypedElaborated};
/// let _ = TypedCore::<TypedElaborated>::new(Vec::<TypedCoreFn>::new());
/// ```
///
/// ```compile_fail
/// use prism_core::core::{TypedCore, TypedCoreFn, TypedElaborated};
/// let _ = TypedCore::<TypedElaborated>::from_functions(Vec::<TypedCoreFn>::new());
/// ```
///
/// ```compile_fail
/// use prism_core::core::{TypedCoreFn, TypedElaborated, UncheckedTypedCore};
/// let draft = UncheckedTypedCore::<TypedElaborated>::new(Vec::<TypedCoreFn>::new());
/// let _ = draft.erase();
/// ```
#[derive(Debug, PartialEq)]
pub struct TypedCore<P> {
    fns: Vec<TypedCoreFn>,
    phase: PhantomData<fn() -> P>,
}

// Manual so a phase-generic caller can clone without requiring `P: Clone`.
impl<P> Clone for TypedCore<P> {
    fn clone(&self) -> Self {
        Self::from_verified(self.fns.clone())
    }
}

impl<P> TypedCore<P> {
    const fn from_verified(fns: Vec<TypedCoreFn>) -> Self {
        Self {
            fns,
            phase: PhantomData,
        }
    }

    /// Functions in deterministic program order.
    #[must_use]
    pub fn functions(&self) -> &[TypedCoreFn] {
        &self.fns
    }

    /// Consume the proof-bearing wrapper before transforming or regrouping it.
    #[must_use]
    pub fn into_unchecked(self) -> UncheckedTypedCore<P> {
        UncheckedTypedCore::new(self.fns)
    }

    /// Consume all type/effect witnesses, yielding executable Core.
    #[must_use]
    pub fn erase(self) -> Core {
        Core {
            fns: self.fns.into_iter().map(TypedCoreFn::erase).collect(),
        }
    }
}

/// Verify a complete assembly and mint its authoritative phase marker.
///
/// `P` identifies the legal node vocabulary. The compiler transition that
/// produced the assembly remains the authority that the phase actually ran.
///
/// # Errors
/// Every independently observed invalid scope, type, effect, handler, phase,
/// ownership, or reuse judgment.
pub fn verify<P: TypedCorePhase>(
    core: UncheckedTypedCore<P>,
    env: &VerifyEnv,
) -> Result<TypedCore<P>, Vec<CoreViolation>> {
    check_functions::<P>(core.functions(), env)?;
    Ok(TypedCore::from_verified(core.into_functions()))
}

/// Recheck an existing authoritative value without creating another minting
/// path. Primarily useful at assertions and cache boundaries.
///
/// # Errors
/// Every independently observed invalid stored judgment.
pub fn audit<P: TypedCorePhase>(
    core: &TypedCore<P>,
    env: &VerifyEnv,
) -> Result<(), Vec<CoreViolation>> {
    check_functions::<P>(core.functions(), env)
}
