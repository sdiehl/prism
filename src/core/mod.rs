pub mod builtins;
mod cbpv;
pub mod effect_lower;
mod elaborate;
pub mod fbip;
pub mod fv;
pub mod hash;
mod json;
pub mod opt;
mod pretty;
pub mod tailrec;
pub mod traverse;

pub use cbpv::{reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
pub use effect_lower::lower as lower_effects;
pub use effect_lower::strategy as effect_strategy;
pub use elaborate::{builtin_arities, elaborate, elaborate_expr};
pub use fbip::{balanced, check_fip, check_fip_linear, fip_annots, insert_rc, reuse, Fips};
pub use hash::{hash_program, Hashes};
pub use json::core_to_json;
pub use opt::{
    erase_newtypes, lint as lint_core, newtype_ctors, run as run_opt, specialize, OptLevel,
    PassStats,
};
pub use pretty::{pp_comp, pp_core, pp_core_pretty, pp_value};
