pub mod builtins;
mod cbpv;
pub mod effect_lower;
mod elaborate;
pub mod fbip;
pub mod fv;
pub mod graph;
pub mod hash;
mod json;
pub mod opt;
mod pretty;
pub mod shape;
pub mod tailrec;
pub mod traverse;

pub use cbpv::{reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, IoOp, Value};
pub use effect_lower::lower as lower_effects;
pub use effect_lower::strategy as effect_strategy;
pub use effect_lower::EFFECT_TIERS;
pub use elaborate::{builtin_arities, elaborate, elaborate_expr, konst_fns};
pub use fbip::{
    balanced, check_fip, check_fip_linear, fip_annots, insert_rc, replayable_annots, reuse, Fips,
};
pub use graph::DepGraph;
pub use hash::{
    hash_group, hash_program, root as hash_root, scc_groups, shallow_hashes, Hashes,
    HASH_PREFIX_HEX, SCHEME as HASH_SCHEME,
};
pub use json::core_to_json;
pub use opt::{
    erase_newtypes, lint as lint_core, newtype_ctors, run as run_opt,
    run_spec_stage as run_opt_spec, specialize, CorePass, OptLevel, PassSpec, PassStats,
};
pub use pretty::{pp_comp, pp_core, pp_core_pretty, pp_value};
pub use shape::{class_digests, instance_digest, shape_digests};
