// Tier-invisibility oracle: the effect-lowering cascade is a pure cost
// decision, so forcing a program onto a slower tier must not change one byte
// of observable output. `PRISM_EFFECT_TIER` (here set programmatically via
// `Config.flags.effect_tier`) caps the cascade; for every corpus program whose
// forced classification differs from its natural one, this gate builds the
// forced native binary and diffs its stdout (and leak report) against the
// interpreter. `tests/parity.rs` pins native(auto) == interp over the same
// corpus, so the two gates together give native(auto) == native(forced):
// tier-vs-tier agreement, enforced rather than argued.
//
// The build/run/diff/leak path and the parallel fan-out are shared with
// tests/parity.rs through `common` (one leak predicate for both), so this file
// only adds the tier-forcing filter and floor.
//
// Programs whose classification does not move under forcing are skipped: their
// forced build is byte-identical to the natural one parity.rs already diffs.
// A floor on the exercised count keeps the oracle from going vacuous if the
// forcing knob or the strategy classifier silently breaks.

use std::path::Path;

use prism::{default_roots, Config, EffectTier};

mod common;
use common::{check_native_parity, corpus, parallel_check, require_cc, source};

fn forced(tier: EffectTier) -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.effect_tier = tier;
    cfg
}

// Force `tier` over the corpus, exercising exactly the programs whose lowering
// strategy moves under the cap, and require at least `floor` of them so the
// oracle cannot silently become vacuous.
fn run_forced(tag: &str, tier: EffectTier, floor: usize) {
    require_cc();
    let auto_cfg = Config::from_env();
    let forced_cfg = forced(tier);
    let base = Path::new(".");
    let cases: Vec<_> = corpus()
        .into_iter()
        .filter(|case| {
            let full = source(case);
            let auto = prism::effect_strategy_on(&full, base, &auto_cfg);
            let hard = prism::effect_strategy_on(&full, base, &forced_cfg);
            match (auto, hard) {
                (Ok(a), Ok(h)) => a != h,
                // A strategy error under exactly one config is itself a tier
                // divergence; keep the case so the build surfaces it.
                _ => true,
            }
        })
        .collect();
    assert!(
        cases.len() >= floor,
        "forcing {tag} moved only {} corpus programs off their natural tier \
         (floor {floor}); the forcing knob or strategy classifier likely broke",
        cases.len()
    );
    let roots = default_roots(base);
    let fails = parallel_check(&cases, |case| {
        check_native_parity(case, tag, |full, bin| {
            prism::build_on(full, &roots, bin, &forced_cfg)
        })
    });
    assert!(
        fails.is_empty(),
        "{} of {} forced-{tag} cases diverged from the interpreter:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}

#[test]
fn forced_free_monad_matches_interpreter() {
    run_forced("free-monad", EffectTier::FreeMonad, 10);
}

#[test]
fn forced_state_matches_interpreter() {
    run_forced("state", EffectTier::State, 3);
}
