//! Differential-determinism gate over the typed program generator.
//!
//! Every generated program is well-typed by construction (see `support::fuzzgen`),
//! so a build failure here is a generator bug and a trace divergence is a compiler
//! bug. Each program is compiled and run under every effect-lowering tier and its
//! observation trace diffed against the interpreter oracle; a divergence is greedily
//! shrunk to a minimal reproducer ready to promote into the permanent corpus.
//!
//! Backend and optimizer parity checks consume the same generator through the
//! same shrink loop, so every comparison uses one program distribution.

use std::fs;
use std::path::Path;

use prism::{default_roots, Config, EffectTier};

use crate::support::fuzzgen::{generate, shrink, Program};
use crate::support::{check_native_parity, require_cc, TempDir};

const TIERS: &[EffectTier] = &[EffectTier::Auto, EffectTier::State, EffectTier::FreeMonad];
const GENERATED_CASES: usize = 12;
const SEED: u64 = 0x7479_7065_645f_667a;

fn forced(tier: EffectTier) -> Config {
    let mut config = Config::from_env();
    config.flags.effect_tier = tier;
    config.flags.compiler_cache = false;
    config
}

// The failure reason if `program` diverges on any tier, `None` if all agree.
fn divergence(program: &Program, path: &Path) -> Option<String> {
    fs::write(path, program.render()).unwrap();
    let roots = default_roots(Path::new("."));
    for &tier in TIERS {
        let config = forced(tier);
        let tag = format!("typed-fuzz-{}", tier.label());
        if let Err(reason) = check_native_parity(path, &tag, |full, binary| {
            prism::build_on(full, &roots, binary, &config)
        }) {
            return Some(reason);
        }
    }
    None
}

#[test]
fn generated_programs_agree_across_all_tiers() {
    require_cc();
    let scratch = TempDir::new("typed-fuzz", "cases");
    let path = scratch.join("candidate.pr");
    for (index, program) in generate(SEED, GENERATED_CASES).into_iter().enumerate() {
        if let Some(failure) = divergence(&program, &path) {
            let (minimal, failure) = shrink(program, failure, |p| divergence(p, &path));
            panic!(
                "generated case {index} diverged after shrinking:\n{failure}\n\nminimal reproducer:\n{}",
                minimal.render()
            );
        }
    }
}
