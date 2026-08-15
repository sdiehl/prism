//! The native oracles: interpreter parity, the effect-tier relations, fusion,
//! the performance gates, sort selection, the compiler cache, and float and
//! symbol conformance. One target so the corpus links the compiler once.

use prism::error::Error;
use prism::{dump_on, Config, EffectTier, Root};

/// The dump phase rendering the effect plan selected by the lowering cascade.
const EFFECT_PLAN: &str = "effect-plan";

fn effect_plan(full: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    dump_on(EFFECT_PLAN, full, roots, cfg)
}

fn forced(tier: EffectTier, erasures: bool) -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.effect_tier = tier;
    cfg.flags.erasures = erasures;
    cfg.flags.compiler_cache = false;
    cfg.flags.quiet = true;
    cfg
}

mod support;

#[path = "native/compiler_cache.rs"]
mod compiler_cache;
#[path = "native/float_fmt.rs"]
mod float_fmt;
#[path = "native/float_math_conformance.rs"]
mod float_math_conformance;
#[path = "native/fuse_parity.rs"]
mod fuse_parity;
#[path = "native/gate_cache_identity.rs"]
mod gate_cache_identity;
#[path = "native/parity.rs"]
mod parity;
#[path = "native/partial_handler_fuzz.rs"]
mod partial_handler_fuzz;
#[path = "native/perf_gate.rs"]
mod perf_gate;
#[path = "native/sort_kind.rs"]
mod sort_kind;
#[path = "native/symbol_namespace.rs"]
mod symbol_namespace;
#[path = "native/tier_cross.rs"]
mod tier_cross;
#[path = "native/tier_handler_parity.rs"]
mod tier_handler_parity;
#[path = "native/tier_parity.rs"]
mod tier_parity;
#[path = "native/typed_fuzz.rs"]
mod typed_fuzz;
