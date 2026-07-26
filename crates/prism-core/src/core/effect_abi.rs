//! Erased effect-runtime ABI shared by typed lowering and native codegen.
//!
//! This module owns names, constructor tags, constructor-table synthesis, and
//! the native driver-name predicate. It contains no lowering algorithm.

use std::collections::BTreeMap;

use crate::types::{CtorInfo, Type};

pub const EFF: &str = "Eff";
pub const EPURE: &str = "EPure";
pub const EOP: &str = "EOp";
pub const ERESUME: &str = "EResume";
pub const EBOUNCE: &str = "EBounce";
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
pub const STEP: &str = "Step";
pub const SMORE: &str = "SMore";
pub const SDONE: &str = "SDone";

/// Whether `name` is one of the residual free-monad driver templates whose
/// entry counts as one native structural reduction step.
#[cfg(feature = "native")]
#[must_use]
pub fn is_free_monad_driver(name: &str) -> bool {
    name == EBIND
        || name == QAPPLY
        || name.ends_with("@handle")
        || name.ends_with("@mask")
        || name.ends_with("@region")
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
