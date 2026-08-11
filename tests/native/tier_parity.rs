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

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use prism::{build_on, default_roots, Config, EffectTier, ObservationTrace};

use super::{effect_plan, forced};

use crate::support::{
    check_native_parity, cleanup_bin, corpus_is_sharded, heavy_corpus_delegated, leak_free,
    parallel_check, program_stderr, require_cc, sharded_corpus, source, temp_bin, CHECK_LEAKS,
};

const PROCESS_FAULT_EXIT: i32 = -1;
const MIN_STATE_FUSION_CASES: usize = 20;
const MIN_LOCAL_PARTIAL_CASES: usize = 30;
const MIN_FREE_MONAD_CASES: usize = 30;
const MIN_WHOLE_PROGRAM_CASES: usize = 60;
const MIN_ERASURE_CASES: usize = 20;
const MIN_SLOWEST_CASES: usize = 75;
const MIN_NATIVE_SUB_LOWERING_CASES: usize = 3;

// Force one point of the (floor, erasures) grid over the corpus, exercising
// exactly the programs whose effect plan moves under it, and require at least
// `floor_count` of them so the oracle cannot silently become vacuous.
fn run_forced(tier: EffectTier, erasures: bool, floor_count: usize) {
    if heavy_corpus_delegated() {
        return;
    }
    require_cc();
    let tag = if erasures {
        tier.label().to_string()
    } else {
        format!("{}-no-erasures", tier.label())
    };
    let tag = tag.as_str();
    let mut auto_cfg = Config::from_env();
    auto_cfg.flags.compiler_cache = false;
    auto_cfg.flags.quiet = true;
    let forced_cfg = forced(tier, erasures);
    let base = Path::new(".");
    let roots = default_roots(base);
    let cases: Vec<_> = sharded_corpus()
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
        corpus_is_sharded() || cases.len() >= floor_count,
        r"forcing {tag} moved only {} corpus programs off their natural lowering (floor {floor_count}); the forcing knob or the effect planner likely broke",
        cases.len()
    );
    let fails = parallel_check(&cases, |case| {
        check_native_parity(case, tag, |full, bin| {
            build_on(full, &roots, bin, &forced_cfg)
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

fn native_output(case: &Path, tag: &str, cfg: &Config) -> Result<Output, String> {
    let roots = default_roots(Path::new("."));
    let full = source(case);
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = temp_bin(tag, &stem);
    if let Err(e) = build_on(&full, &roots, &bin, cfg) {
        cleanup_bin(&bin);
        return Err(format!("{}: {tag} build failed: {e}", case.display()));
    }
    let out = Command::new(&bin)
        .env(CHECK_LEAKS, "1")
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
        let a_trace = ObservationTrace::from_process(
            &a.stdout,
            program_stderr(&a_err).as_bytes(),
            a.status.code().unwrap_or(PROCESS_FAULT_EXIT),
        );
        let b_trace = ObservationTrace::from_process(
            &b.stdout,
            program_stderr(&b_err).as_bytes(),
            b.status.code().unwrap_or(PROCESS_FAULT_EXIT),
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
    run_forced(EffectTier::StateFusion, true, MIN_STATE_FUSION_CASES);
}

#[test]
fn forced_local_partial_matches_interpreter() {
    run_forced(EffectTier::LocalPartial, true, MIN_LOCAL_PARTIAL_CASES);
}

#[test]
fn forced_free_monad_matches_interpreter() {
    run_forced(EffectTier::FreeMonad, true, MIN_FREE_MONAD_CASES);
}

#[test]
fn forced_whole_program_free_monad_matches_interpreter() {
    run_forced(
        EffectTier::WholeProgramFreeMonad,
        true,
        MIN_WHOLE_PROGRAM_CASES,
    );
}

// The other axis on its own: the erasures off, the cascade otherwise free, so a
// divergence here is the erasures' and not the ladder's.
#[test]
fn disabled_erasures_match_interpreter() {
    run_forced(EffectTier::Auto, false, MIN_ERASURE_CASES);
}

// Both axes at their extreme: nothing erased, everything reified, the whole
// program in the monad. There is nothing slower to fall back to, so this is the
// cascade's outer bound.
#[test]
fn slowest_lowering_matches_interpreter() {
    run_forced(EffectTier::WholeProgramFreeMonad, false, MIN_SLOWEST_CASES);
}

#[test]
fn native_effects_toggle_matches_native() {
    let mut fast = Config::from_env();
    fast.flags.quiet = true;
    fast.flags.compiler_cache = false;
    let mut slow = fast.clone();
    slow.flags.native_effects = false;
    run_native_diff(
        "native-effects",
        "on",
        &fast,
        "off",
        &slow,
        MIN_NATIVE_SUB_LOWERING_CASES,
    );
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
    run_native_diff(
        "trampoline",
        "on",
        &tramp,
        "off",
        &no_tramp,
        MIN_NATIVE_SUB_LOWERING_CASES,
    );
}
