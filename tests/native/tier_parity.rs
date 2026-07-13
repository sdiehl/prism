// Tier-invisibility oracle: the effect-lowering cascade is a pure cost
// decision, so forcing a program onto a slower tier must not change one byte
// of observable output. `PRISM_EFFECT_TIER` (here set programmatically via
// `Config.flags.effect_tier`) caps the cascade; for every corpus program whose
// forced classification differs from its natural one, this gate builds the
// forced native binary and diffs its stdout (and leak report) against the
// interpreter. Native-only sub-lowering knobs (`native_effects`, `trampoline`)
// do not move the tier classifier, so they run a named effectful corpus twice
// and diff native output directly. Together these catch both cascade-level and
// fastest-vs-slowest native tier drift.
//
// The build/run/diff/leak path and the parallel fan-out are shared with
// tests/parity.rs through `support` (one leak predicate for both), so this file
// only adds the tier-forcing filter and floor.
//
// Programs whose classification does not move under forcing are skipped: their
// forced build is byte-identical to the natural one parity.rs already diffs.
// A floor on the exercised count keeps the oracle from going vacuous if the
// forcing knob or the strategy classifier silently breaks.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use prism::{default_roots, Config, EffectTier};

use crate::support::{
    check_native_parity, corpus, leak_free, parallel_check, require_cc, source, temp_bin,
};

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
        r"forcing {tag} moved only {} corpus programs off their natural tier (floor {floor}); the forcing knob or strategy classifier likely broke",
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

fn cleanup_bin(bin: &Path) {
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(bin);
}

fn native_output(case: &Path, tag: &str, cfg: &Config) -> Result<std::process::Output, String> {
    let roots = default_roots(Path::new("."));
    let full = source(case);
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = temp_bin(tag, &stem);
    if let Err(e) = prism::build_on(&full, &roots, &bin, cfg) {
        cleanup_bin(&bin);
        return Err(format!("{}: {tag} build failed: {e}", case.display()));
    }
    let out = Command::new(&bin)
        .env("PRISM_CHECK_LEAKS", "1")
        .output()
        .map_err(|e| format!("{}: {tag} spawn failed: {e}", case.display()));
    cleanup_bin(&bin);
    out
}

fn sub_lowering_cases() -> Vec<PathBuf> {
    [
        // Evidence and evidence fusion.
        "tests/cases/run/eff_fuse.pr",
        "tests/cases/run/eff_two_handlers.pr",
        // State-fusion paths.
        "tests/cases/run/fold_chains.pr",
        "examples/eff_state.pr",
        "examples/eff_writer.pr",
        // Selective and whole-program free-monad paths.
        "tests/cases/run/final_ctl.pr",
        "examples/eff_nontail.pr",
        "tests/cases/run/cancel_completed.pr",
        "examples/async.pr",
    ]
    .into_iter()
    .map(PathBuf::from)
    .collect()
}

fn run_native_diff(
    tag: &str,
    a_tag: &str,
    a_cfg: &Config,
    b_tag: &str,
    b_cfg: &Config,
    floor: usize,
) {
    require_cc();
    let cases = sub_lowering_cases();
    assert!(
        cases.len() >= floor,
        "{tag} has only {} native-vs-native sub-lowering cases (floor {floor})",
        cases.len()
    );
    let fails = parallel_check(&cases, |case| {
        let a = native_output(case, &format!("{tag}-{a_tag}"), a_cfg)?;
        let b = native_output(case, &format!("{tag}-{b_tag}"), b_cfg)?;
        let a_err = String::from_utf8_lossy(&a.stderr);
        let b_err = String::from_utf8_lossy(&b.stderr);
        if !leak_free(&a_err) || !leak_free(&b_err) {
            return Err(format!(
                "{tag} leak report failed for {}:\n  {a_tag}: {}\n  {b_tag}: {}",
                case.display(),
                a_err.trim(),
                b_err.trim()
            ));
        }
        let program_stderr = |stderr: &str| {
            stderr
                .lines()
                .filter(|line| !line.starts_with("prism: ") || !line.ends_with(" cells leaked"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let a_trace = prism::ObservationTrace::from_process(
            &a.stdout,
            program_stderr(&a_err).as_bytes(),
            a.status.code().unwrap_or(-1),
        );
        let b_trace = prism::ObservationTrace::from_process(
            &b.stdout,
            program_stderr(&b_err).as_bytes(),
            b.status.code().unwrap_or(-1),
        );
        if a_trace != b_trace {
            return Err(format!(
                "{tag} observation trace diverges for {}:\n  {a_tag}: {:?}\n  {b_tag}: {:?}",
                case.display(),
                a_trace.observations,
                b_trace.observations
            ));
        }
        Ok(())
    });
    assert!(
        fails.is_empty(),
        "{} of {} {tag} native-vs-native cases diverged:\n{}",
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

#[test]
fn native_effects_toggle_matches_native() {
    let mut fast = Config::from_env();
    fast.flags.quiet = true;
    let mut slow = fast.clone();
    slow.flags.native_effects = false;
    run_native_diff("native-effects", "on", &fast, "off", &slow, 3);
}

#[test]
fn trampoline_toggle_matches_native() {
    let mut tramp = Config::from_env();
    tramp.flags.native_effects = false;
    tramp.flags.trampoline = true;
    tramp.flags.quiet = true;
    let mut no_tramp = tramp.clone();
    no_tramp.flags.trampoline = false;
    run_native_diff("trampoline", "on", &tramp, "off", &no_tramp, 3);
}
