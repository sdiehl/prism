pub mod builtins;
pub mod captures;
mod cbpv;
pub(crate) mod effect_abi;
pub(crate) mod effect_analysis;
pub(crate) mod effect_check;
pub(crate) mod effect_shape;
mod effects;
mod elaborate;
pub mod fbip;
pub mod fv;
pub mod graph;
pub mod hash;
mod json;
pub mod opt;
mod pretty;
pub mod shape;
pub mod simd;
pub mod tailrec;
pub mod traverse;
pub mod typed;

pub use cbpv::{
    reachable_fns, CheckedHandler, Comp, Core, CoreFn, CoreOp, CorePat, ElaboratedCore, HandleOp,
    IoOp, LoweredCore, NegLane, Value,
};
pub(crate) use effect_analysis::latent_ops;
pub(crate) use effect_check::residual_effects;
pub use effects::{EffectStrategy, OpGrades, EFFECT_TIERS};
pub use elaborate::{builtin_arities, elaborate, elaborate_expr, konst_fns};
pub(crate) use elaborate::{elaborate_typed, typed_verification_error};
pub use fbip::{
    balanced, check_fip, check_fip_linear, fip_annots, insert_rc, replayable_annots, reuse, Fips,
};
pub use graph::DepGraph;
pub(crate) use hash::hex as hash_str;
pub use hash::{
    hash_group, hash_program, root as hash_root, scc_groups, shallow_hashes, Digest, Hashes,
    HASH_PREFIX_HEX, SCHEME as HASH_SCHEME,
};
pub use json::core_to_json;
pub use opt::{
    effective_passes, erase_newtypes, lint as lint_core, newtype_ctors, pass_fingerprint,
    run as run_opt, run_spec_stage as run_opt_spec, specialize, CorePass, OptLevel, PassSpec,
    PassStage, PassStats,
};
pub use pretty::{pp_comp, pp_core, pp_core_pretty, pp_value};
pub use shape::{class_digests, contract_digest, instance_digest, shape_digests};
pub use typed::{
    verify as verify_typed_core, CompSig, ConstructorSig, CoreFnSig, CoreInstantiation,
    CoreQuantifier, CoreType, CoreViolation, EffectLowered as TypedEffectLowered,
    Elaborated as TypedElaborated, OperationSig, Owned as TypedOwned,
    ReuseLowered as TypedReuseLowered, TypedBinder, TypedComp, TypedCompKind, TypedCore,
    TypedCoreFn, TypedCorePhase, TypedForward, TypedHandleOp, TypedHandler, TypedPattern,
    TypedValue, TypedValueKind, VerifyEnv,
};
