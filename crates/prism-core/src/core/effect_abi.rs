//! Erased effect-runtime ABI shared by typed lowering and native codegen.
//!
//! This module owns names, constructor tags, constructor-table synthesis, and
//! the native driver-name predicate. It contains no lowering algorithm.

use std::collections::BTreeMap;

use prism_syntax::names;

use crate::types::{CtorInfo, Type};

pub const EFF: &str = "Eff";
pub const EPURE: &str = "EPure";
pub const EOP: &str = "EOp";
pub const ERESUME: &str = "EResume";
pub const EBOUNCE: &str = "EBounce";
/// Every constructor of the reified effect cell.
pub const EFF_CTORS: [&str; 4] = [EPURE, EOP, ERESUME, EBOUNCE];

pub const TQ: &str = "TQ";
pub const TQNIL: &str = "TQNil";
pub const TQCONS: &str = "TQCons";

pub const PURE_TAG: usize = 0;
pub const OP_TAG: usize = 1;
pub const RESUME_TAG: usize = 2;
pub const BOUNCE_TAG: usize = 3;
pub const TQNIL_TAG: usize = 0;
pub const TQCONS_TAG: usize = 1;

pub const EBIND: &str = "ebind";
pub const QAPPLY: &str = "qApply";

pub const MORE_TAG: usize = 0;
pub const DONE_TAG: usize = 1;
/// Private step-carrier constructors used to turn resumptions into loops. The
/// `@` sigil is not source-spellable, preventing collisions with user types.
pub const STEP: &str = "Eff@Step";
pub const SMORE: &str = "Eff@SMore";
pub const SDONE: &str = "Eff@SDone";

/// The residual free-monad driver templates that typed lowering generates.
///
/// Lowering and codegen share this enum so driver names and recognition cannot
/// drift apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FreeMonadDriver {
    /// Drives one handler's reified computation to its answer.
    Handle,
    /// Drives a sub-computation past the handler its operations tunnel through.
    Mask,
    /// Drives a confined monadic region back to its enclosing convention.
    Region,
}

impl FreeMonadDriver {
    /// Every driver template, in one place because a phase that accounts for one
    /// has to account for all of them.
    pub const ALL: [Self; 3] = [Self::Handle, Self::Mask, Self::Region];

    const fn hint(self) -> &'static str {
        match self {
            Self::Handle => "handle",
            Self::Mask => "mask",
            Self::Region => "region",
        }
    }

    /// The name of the `n`th generated instance of this driver.
    #[must_use]
    pub fn mint(self, n: u32) -> String {
        names::lowered(self.hint(), n)
    }

    /// The driver a generated `name` was minted for, or `None` otherwise.
    #[must_use]
    pub fn of_name(name: &str) -> Option<Self> {
        let (_, hint) = names::parse_lowered(name)?;
        Self::ALL.into_iter().find(|driver| driver.hint() == hint)
    }
}

/// Whether `name` is one of the residual free-monad driver templates whose
/// entry counts as one native structural reduction step.
#[cfg(feature = "native")]
#[must_use]
pub fn is_free_monad_driver(name: &str) -> bool {
    name == EBIND || name == QAPPLY || FreeMonadDriver::of_name(name).is_some()
}

/// Reconstruct one constructor introduced by typed effect lowering.
///
/// Returns `false` for names outside the effect-runtime ABI.
pub fn add_synthetic_ctor(ctors: &mut BTreeMap<String, CtorInfo>, name: &str) -> bool {
    let ctor = match name {
        EPURE => synth_ctor(EFF, PURE_TAG, 1),
        EOP => synth_ctor(EFF, OP_TAG, 4),
        ERESUME => synth_ctor(EFF, RESUME_TAG, 2),
        EBOUNCE => synth_ctor(EFF, BOUNCE_TAG, 1),
        TQNIL => synth_ctor(TQ, TQNIL_TAG, 0),
        TQCONS => synth_ctor(TQ, TQCONS_TAG, 2),
        SMORE => synth_ctor(STEP, MORE_TAG, 1),
        SDONE => synth_ctor(STEP, DONE_TAG, 1),
        _ => return false,
    };
    ctors.insert(name.to_string(), ctor);
    true
}

fn synth_ctor(type_name: &str, tag: usize, arity: usize) -> CtorInfo {
    CtorInfo {
        type_name: type_name.into(),
        params: Vec::new(),
        param_kinds: Vec::new(),
        // These are arity-carrying placeholders. Native layout stores every
        // erased field in one uniform value word.
        args: vec![Type::Int; arity],
        tag,
        fields: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::FreeMonadDriver;

    const COUNTERS: [u32; 4] = [0, 1, 9, 4321];

    // Minting and recognizing are inverses, which is the whole contract between
    // typed lowering and native step accounting. A rename of a driver's spelling
    // keeps this green; dropping a variant from the recognizer does not.
    #[test]
    fn every_minted_driver_name_names_its_own_driver() {
        for driver in FreeMonadDriver::ALL {
            for n in COUNTERS {
                let minted = driver.mint(n);
                assert_eq!(
                    FreeMonadDriver::of_name(&minted),
                    Some(driver),
                    "{minted} must round-trip"
                );
            }
        }
    }

    // Recognition accepts only names produced by the minter.
    #[test]
    fn only_minted_names_are_recognized() {
        assert_eq!(FreeMonadDriver::of_name("handle"), None);
        assert_eq!(FreeMonadDriver::of_name("region"), None);
        assert_eq!(FreeMonadDriver::of_name("x7@handle"), None);
        assert_eq!(FreeMonadDriver::of_name("7@handles"), None);
        assert_eq!(FreeMonadDriver::of_name("7@drv"), None);
    }
}
