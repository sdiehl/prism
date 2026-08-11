// Tier-vs-tier differential oracle. The cascade's contract is that the tier it
// picks is unobservable, and the parity oracles prove each tier against the
// interpreter one at a time. This gate closes the remaining seam by comparing
// the tiers directly to each other: for every program whose effect plan moves
// under forcing, it builds one native binary per distinct plan across the
// forced-tier grid and requires the full observation traces (stdout, stderr,
// exit code) and leak verdicts to agree pairwise. Because no interpreter
// reference run is needed, the committed adversarial fixtures below can carry
// content the interpreter-anchored corpus filter would exclude, and a
// divergence names the two configurations that disagree rather than pointing
// at the reference.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use prism::{build_on, default_roots, Config, EffectTier, ObservationTrace, Root};

use super::{effect_plan, forced};
use crate::support::{
    canonical_process_exit, cleanup_bin, corpus, corpus_is_sharded, leak_free, parallel_check,
    program_stderr, require_cc, shard, source, temp_bin, with_gate_cache, CHECK_LEAKS,
};

/// Gate-cache tag for a cross-tier verdict: one marker covers the whole grid
/// for a program, since the verdict is a pure function of source and compiler.
const CROSS_TAG: &str = "tier-cross";

/// Committed adversarial programs this gate must always exercise; their output
/// bytes sit on the seams (NUL, multibyte boundaries) where tiers could
/// disagree without any ordinary corpus program noticing.
const FIXTURE_CASES: &[&str] = &[
    "tests/fixtures/tier_cross/nul_byte.pr",
    "tests/fixtures/tier_cross/non_ascii.pr",
    "tests/fixtures/tier_cross/byte_seams.pr",
    "tests/fixtures/tier_cross/thunk_param.pr",
];

const MIN_DISTINCT_TIER_PLANS: usize = 2;
const MIN_MOVED_CORPUS_CASES: usize = 60;

/// The forced grid: the natural lowering, every cap the cascade accepts, and
/// the erasure-free outer bound.
fn grid() -> Vec<(String, Config)> {
    let mut auto_cfg = Config::from_env();
    auto_cfg.flags.compiler_cache = false;
    let mut points = vec![("auto".to_string(), auto_cfg)];
    for tier in EffectTier::ALL
        .into_iter()
        .filter(|tier| *tier != EffectTier::Auto)
    {
        points.push((tier.label().to_string(), forced(tier, true)));
    }
    points.push((
        format!("{}-no-erasures", EffectTier::WholeProgramFreeMonad.label()),
        forced(EffectTier::WholeProgramFreeMonad, false),
    ));
    points
}

/// One configuration per distinct effect plan. A planning error is kept as its
/// own "plan" so the survivor's build surfaces the real error: a program that
/// plans under one configuration and not another has already diverged.
fn survivors<'g>(
    full: &str,
    roots: &[Root],
    grid: &'g [(String, Config)],
) -> Vec<(&'g str, &'g Config)> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for (label, cfg) in grid {
        let plan =
            effect_plan(full, roots, cfg).unwrap_or_else(|error| format!("plan error: {error}"));
        if seen.insert(plan) {
            out.push((label.as_str(), cfg));
        }
    }
    out
}

/// Everything a tier run observes: the trace the contract pins plus the leak
/// verdict, labelled by the grid point that produced it.
struct TierRun {
    label: String,
    trace: ObservationTrace,
    leak_clean: bool,
    leak_report: String,
}

fn tier_run(
    case: &Path,
    full: &str,
    roots: &[Root],
    label: &str,
    cfg: &Config,
) -> Result<TierRun, String> {
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = temp_bin(&format!("cross-{label}"), &stem);
    if let Err(error) = build_on(full, roots, &bin, cfg) {
        cleanup_bin(&bin);
        return Err(format!(
            "{}: cross-{label} build failed: {error}",
            case.display()
        ));
    }
    let run = Command::new(&bin).env(CHECK_LEAKS, "1").output();
    cleanup_bin(&bin);
    let out =
        run.map_err(|error| format!("{}: cross-{label} spawn failed: {error}", case.display()))?;
    let Some(exit) = out.status.code() else {
        return Err(format!(
            "cross-{label} process faulted for {} without an exit code",
            case.display()
        ));
    };
    let stderr = String::from_utf8_lossy(&out.stderr);
    Ok(TierRun {
        label: label.to_string(),
        trace: ObservationTrace::from_process(
            &out.stdout,
            program_stderr(&stderr).as_bytes(),
            canonical_process_exit(exit),
        ),
        leak_clean: leak_free(&stderr),
        leak_report: stderr.trim().to_string(),
    })
}

/// Build and run every surviving grid point for `case` and require the runs to
/// agree with each other on the full trace and on leak freedom.
fn diff_survivors(
    case: &Path,
    full: &str,
    roots: &[Root],
    points: &[(&str, &Config)],
) -> Result<(), String> {
    let mut runs = Vec::with_capacity(points.len());
    for (label, cfg) in points {
        runs.push(tier_run(case, full, roots, label, cfg)?);
    }
    for run in &runs {
        if !run.leak_clean {
            return Err(format!(
                "{}: cross-{} did not free all cells: {}",
                case.display(),
                run.label,
                run.leak_report
            ));
        }
    }
    let (first, rest) = runs
        .split_first()
        .ok_or_else(|| format!("{}: empty tier grid", case.display()))?;
    for run in rest {
        if run.trace != first.trace {
            return Err(format!(
                "tiers observably diverge for {}:\n  {}: {:?}\n  {}: {:?}",
                case.display(),
                first.label,
                first.trace.observations,
                run.label,
                run.trace.observations
            ));
        }
    }
    Ok(())
}

fn check_case(
    case: &Path,
    roots: &[Root],
    grid: &[(String, Config)],
    exercised: &AtomicUsize,
) -> Result<(), String> {
    let full = source(case);
    let points = survivors(&full, roots, grid);
    if points.len() < MIN_DISTINCT_TIER_PLANS {
        // Every grid point lowers this program identically, so the natural
        // parity oracle already pins the one binary that exists.
        return Ok(());
    }
    exercised.fetch_add(1, Ordering::Relaxed);
    with_gate_cache(&full, CROSS_TAG, || {
        diff_survivors(case, &full, roots, &points)
    })
}

// The corpus sweep. The floor sits under the union of the per-tier moved
// counts the tier-parity floors were derived from (their per-knob counts were
// 28 to 108 on a 346-program corpus, and any program counted there is counted
// here); when it trips, the panic reports the true count, which is how a stale
// floor is refreshed.
#[test]
fn tiers_match_each_other_on_the_corpus() {
    require_cc();
    let roots = default_roots(Path::new("."));
    let grid = grid();
    let cases = shard(corpus());
    let exercised = AtomicUsize::new(0);
    let fails = parallel_check(&cases, |case| check_case(case, &roots, &grid, &exercised));
    assert!(
        fails.is_empty(),
        "{} of {} cross-tier cases diverged:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
    let moved = exercised.load(Ordering::Relaxed);
    assert!(
        corpus_is_sharded() || moved >= MIN_MOVED_CORPUS_CASES,
        "forcing moved only {moved} corpus programs off their natural lowering (floor {MIN_MOVED_CORPUS_CASES}); the forcing knob or the effect planner likely broke"
    );
}

// The committed adversarial fixtures, unconditionally: each must both move
// under forcing (a fixture whose plan stops moving has stopped testing the
// cascade and fails here by name) and agree across its grid.
#[test]
fn tiers_match_each_other_on_adversarial_fixtures() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(Path::new("."));
    let grid = grid();
    let cases: Vec<PathBuf> = FIXTURE_CASES.iter().map(|case| root.join(case)).collect();
    let fails = parallel_check(&cases, |case| {
        let full = source(case);
        let points = survivors(&full, &roots, &grid);
        if points.len() < MIN_DISTINCT_TIER_PLANS {
            return Err(format!(
                "{}: fixture's effect plan no longer moves under forcing; it has stopped exercising the cascade",
                case.display()
            ));
        }
        with_gate_cache(&full, CROSS_TAG, || {
            diff_survivors(case, &full, &roots, &points)
        })
    });
    assert!(
        fails.is_empty(),
        "{} of {} adversarial cross-tier fixtures failed:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}
