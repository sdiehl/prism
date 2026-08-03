// Tier-invisibility oracle: the effect-lowering cascade is a pure cost
// decision, so forcing a program onto a slower tier must not change one byte
// of observable output. `PRISM_EFFECT_TIER` (here set programmatically via
// `Config.flags.effect_tier`) caps the cascade; for every corpus program whose
// forced effect plan differs from its natural one, this gate builds the forced
// native binary and diffs its stdout (and leak report) against the
// interpreter. Native-only sub-lowering knobs (`native_effects`, `trampoline`)
// do not move the tier classifier, so they run a named effectful corpus twice
// and diff native output directly. Together these catch both cascade-level and
// fastest-vs-slowest native tier drift.
//
// The build/run/diff/leak path and the parallel fan-out are shared with
// tests/parity.rs through `support` (one leak predicate for both), so this file
// only adds the tier-forcing filter and floor.
//
// Programs whose lowering does not move under forcing are skipped: their forced
// build is byte-identical to the natural one parity.rs already diffs. What
// "does not move" means is the whole effect plan, not the tier label alone:
// lowering confines per region, so two configurations can agree on the label and
// still build a different region, refuse confinement for a different reason, or
// read different per-function facts off a differently erased tree. Selecting on
// the label would exclude exactly those programs, which are the ones a
// tier-invisibility gate exists for. A floor on the exercised count keeps the
// oracle from going vacuous if the forcing knob or the classifier silently
// breaks.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use prism::error::Error;
use prism::{default_roots, dump_on, Config, EffectTier, Root};

use crate::support::{
    check_native_parity, corpus, leak_free, parallel_check, require_cc, source, temp_bin,
};

/// The dump phase rendering the effect plan: the strategy the cascade picked,
/// why a confined region was refused when one was attempted, and the
/// per-function facts (reachable operations, thunk parameters, genuine /
/// escaping / capturing marks) it decided from. Every input to the tier decision
/// is a row, which is what makes it the right selection fact here.
const EFFECT_PLAN: &str = "effect-plan";

// The whole tier decision for `full` under `cfg`, as the artifact the cascade
// explains itself with. Two configurations that render the same plan lower the
// same way, so a program whose plan is unmoved by forcing is one the natural
// parity oracle already covers; a program whose plan moves in any row (a
// different tier, a confined region refused for a different reason, or different
// per-function facts once an erasure is off) is one this gate must build.
fn effect_plan(full: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    dump_on(EFFECT_PLAN, full, roots, cfg)
}

fn forced(tier: EffectTier, erasures: bool) -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.effect_tier = tier;
    cfg.flags.erasures = erasures;
    cfg.flags.compiler_cache = false;
    cfg
}

// Force one point of the (floor, erasures) grid over the corpus, exercising
// exactly the programs whose effect plan moves under it, and require at least
// `floor_count` of them so the oracle cannot silently become vacuous.
fn run_forced(tier: EffectTier, erasures: bool, floor_count: usize) {
    require_cc();
    let tag = if erasures {
        tier.label().to_string()
    } else {
        format!("{}-no-erasures", tier.label())
    };
    let tag = tag.as_str();
    let mut auto_cfg = Config::from_env();
    auto_cfg.flags.compiler_cache = false;
    let forced_cfg = forced(tier, erasures);
    let base = Path::new(".");
    let roots = default_roots(base);
    let cases: Vec<_> = corpus()
        .into_iter()
        .filter(|case| {
            let full = source(case);
            let auto = effect_plan(&full, &roots, &auto_cfg);
            let hard = effect_plan(&full, &roots, &forced_cfg);
            match (auto, hard) {
                (Ok(a), Ok(h)) => a != h,
                // A planning error under exactly one config is itself a tier
                // divergence; keep the case so the build surfaces it.
                _ => true,
            }
        })
        .collect();
    assert!(
        cases.len() >= floor_count,
        r"forcing {tag} moved only {} corpus programs off their natural lowering (floor {floor_count}); the forcing knob or the effect planner likely broke",
        cases.len()
    );
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

// One point of the (floor, erasures) grid per test, each moving one axis at a
// time so a divergence names the knob that caused it. The floors below sit under
// the counts measured on a 346-program corpus (28, 40, 41, 89, 28, 108 in the
// order the tests appear) with enough slack that ordinary corpus churn does not
// trip them; when a floor does trip, its panic reports the true count, which is
// how the numbers here were derived and how a stale one is refreshed. Those
// counts predate selecting on the whole effect plan, which only ever admits more
// programs, so they remain lower bounds. Forcing `auto` is deliberately absent:
// it moves nothing, being the default.

// The floors, erasures left on. Evidence is not forceable either: flooring there
// is what `auto` already does.
#[test]
fn forced_state_fusion_matches_interpreter() {
    run_forced(EffectTier::StateFusion, true, 20);
}

#[test]
fn forced_local_partial_matches_interpreter() {
    run_forced(EffectTier::LocalPartial, true, 30);
}

#[test]
fn forced_free_monad_matches_interpreter() {
    run_forced(EffectTier::FreeMonad, true, 30);
}

#[test]
fn forced_whole_program_free_monad_matches_interpreter() {
    run_forced(EffectTier::WholeProgramFreeMonad, true, 60);
}

// The other axis on its own: the erasures off, the cascade otherwise free, so a
// divergence here is the erasures' and not the ladder's.
#[test]
fn disabled_erasures_match_interpreter() {
    run_forced(EffectTier::Auto, false, 20);
}

// Both axes at their extreme: nothing erased, everything reified, the whole
// program in the monad. There is nothing slower to fall back to, so this is the
// cascade's outer bound.
#[test]
fn slowest_lowering_matches_interpreter() {
    run_forced(EffectTier::WholeProgramFreeMonad, false, 75);
}

#[test]
fn native_effects_toggle_matches_native() {
    let mut fast = Config::from_env();
    fast.flags.quiet = true;
    fast.flags.compiler_cache = false;
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
    tramp.flags.compiler_cache = false;
    let mut no_tramp = tramp.clone();
    no_tramp.flags.trampoline = false;
    run_native_diff("trampoline", "on", &tramp, "off", &no_tramp, 3);
}
