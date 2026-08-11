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

#[path = "native/tier_parity.rs"]
mod tier_parity;

#[path = "native/tier_cross.rs"]
mod tier_cross;

#[path = "native/tier_handler_parity.rs"]
mod tier_handler_parity;

#[path = "native/partial_handler_fuzz.rs"]
mod partial_handler_fuzz;

#[path = "native/typed_fuzz.rs"]
mod typed_fuzz;
