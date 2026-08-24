//! Whole-corpus effect-tier equivalence gate.
//!
//! Tier selection is a cost choice, so every forceable `EffectTier` position
//! must produce the same canonical observation trace. Each position floors the
//! cascade at one rung; the cascade still falls back to costlier rungs, and the
//! whole-program monad is legal for every program, so all five positions lower
//! every runnable corpus program with no skip logic. The auto position is the
//! baseline: it is the only one that can take the pure and evidence rungs, so
//! diffing every floor against it covers the full ladder.
//!
//! This proves lowered-Core semantic equivalence at interpreter cost, which is
//! what lets it sweep the whole corpus and a generated corpus. The native tier
//! gates (tier parity, tier cross, tier handler parity) independently prove
//! that the backend implements each tier's Core correctly and leak-free; they
//! stay authoritative for native behavior and this gate does not replace them.
//!
//! The representative sample is the fast semantic path, the early-exit
//! discovery keeps every adjacent pair of positions engaged, and the
//! whole-corpus relation partitions by source across the CI exact-cover
//! matrix. The generated sweep points the deterministic program generator at
//! the same relation and greedily shrinks any divergence to a minimal
//! reproducer.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use prism::{default_roots, Config, EffectTier, ObservationTrace};

use crate::support::fuzzgen::{generate, generate_arena, shrink, Program, ProgramFamily};
use crate::support::{
    corpus_candidates, corpus_is_sharded, heavy_corpus_delegated, parallel_check, parallel_each,
    runnable_corpus_source, sharded_corpus, source,
};

/// The tier axis only exists after effect lowering, so engagement scans dump
/// this phase alone: pre-lowering Core is tier-independent by construction.
const ENGAGEMENT_PHASE: &str = "lowered";

/// Adjacent positions on the forced ladder. Each pair must change lowered Core
/// somewhere in the corpus, otherwise two positions have collapsed and the
/// sweep between them is vacuous.
const ADJACENT_POSITIONS: [(usize, usize); 4] = [(0, 1), (1, 2), (2, 3), (3, 4)];

const ACTIVITY_LABELS: [&str; 4] = [
    "auto versus state-fusion",
    "state-fusion versus local-partial",
    "local-partial versus selective-free-monad",
    "selective-free-monad versus whole-program-free-monad",
];

/// Committed programs whose effect plans are known to move under forcing; they
/// keep the sample and the whole-corpus extension non-vacuous.
const FIXTURE_CASES: &[&str] = &[
    "tests/fixtures/tier_cross/thunk_param.pr",
    "tests/fixtures/tier_cross/convention_split_map.pr",
    "tests/fixtures/tier_cross/convention_split_map_unrolled.pr",
];

/// Corpus programs scanned first by the engagement discovery, one per rung the
/// blind alphabetical order reaches late. The local-partial rung in particular
/// is chosen by exactly one corpus program, so without seeding it the scan
/// walks most of the corpus (five lowerings per case) before the
/// local-partial/selective pair can engage.
const ENGAGEMENT_SEED_CASES: &[&str] = &[
    "examples/accum.pr",
    "examples/eff_state.pr",
    "tests/cases/run/local_mono_combined.pr",
    "examples/eff_yield.pr",
];

#[derive(Debug)]
struct Variant {
    label: &'static str,
    config: Config,
}

impl Variant {
    fn tier(tier: EffectTier) -> Self {
        let mut config = Config::default();
        config.flags.effect_tier = tier;
        config.flags.compiler_cache = false;
        config.flags.quiet = true;
        Self {
            label: tier.label(),
            config,
        }
    }
}

fn variants() -> Vec<Variant> {
    EffectTier::ALL.into_iter().map(Variant::tier).collect()
}

fn record_lowered_activity(lowered: &[&str], activity: &[AtomicUsize]) {
    for (slot, (left, right)) in ADJACENT_POSITIONS.into_iter().enumerate() {
        if lowered[left] != lowered[right] {
            activity[slot].fetch_add(1, Ordering::Relaxed);
        }
    }
}

fn check_source(
    label: &str,
    full: &str,
    roots: &[prism::Root],
    variants: &[Variant],
    activity: &[AtomicUsize],
) -> Result<(), String> {
    let mut runs: Vec<(&Variant, ObservationTrace, String)> = Vec::with_capacity(variants.len());
    for variant in variants {
        let (trace, lowered) = prism::driver::observe_lowered_run_on(full, roots, &variant.config)
            .map_err(|error| {
                format!(
                    "{label}: {} failed to observe lowered Core: {error}",
                    variant.label
                )
            })?;
        runs.push((variant, trace, lowered));
    }
    let lowered = runs
        .iter()
        .map(|(_, _, lowered)| lowered.as_str())
        .collect::<Vec<_>>();
    record_lowered_activity(&lowered, activity);

    let Some((baseline_variant, baseline_trace, _)) = runs.first() else {
        return Err(format!("{label}: tier matrix is empty"));
    };
    for (variant, trace, _) in &runs[1..] {
        if trace != baseline_trace {
            return Err(format!(
                "tier observation trace diverges for {label}:\n  {}: {:?}\n  {}: {:?}",
                baseline_variant.label,
                baseline_trace.observations,
                variant.label,
                trace.observations,
            ));
        }
    }
    Ok(())
}

fn check_case(
    case: &Path,
    roots: &[prism::Root],
    variants: &[Variant],
    activity: &[AtomicUsize],
) -> Result<(), String> {
    let full = source(case);
    check_source(
        &case.display().to_string(),
        &full,
        roots,
        variants,
        activity,
    )
}

fn run_cases(cases: &[PathBuf], require_engagement: bool) {
    let roots = default_roots(Path::new("."));
    let variants = variants();
    let activity: Vec<AtomicUsize> = (0..ACTIVITY_LABELS.len())
        .map(|_| AtomicUsize::new(0))
        .collect();
    let fails = parallel_check(cases, |case| check_case(case, &roots, &variants, &activity));
    assert!(
        fails.is_empty(),
        "{} of {} tier-equivalence cases failed:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );

    eprintln!(
        "tier-equiv: {} cases, {} tiers, {} lowered-Core evaluator runs",
        cases.len(),
        variants.len(),
        cases.len() * variants.len()
    );
    for (slot, label) in ACTIVITY_LABELS.into_iter().enumerate() {
        let changed = activity[slot].load(Ordering::Relaxed);
        eprintln!("tier-equiv: {label} changed {changed} cases");
        if require_engagement {
            assert!(
                changed > 0,
                "{label} changed no lowered Core in the runnable corpus; the sweep is vacuous"
            );
        }
    }
}

#[test]
fn tier_equivalence_representative_sample() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cases = [
        "examples/accum.pr",
        "examples/eff_state.pr",
        "examples/eff_yield.pr",
        "examples/handlers_funval.pr",
        "examples/delim.pr",
        "examples/eff_poly.pr",
        "examples/effectful_traverse.pr",
        "examples/imperative.pr",
        "tests/fixtures/tier_cross/thunk_param.pr",
        "tests/fixtures/tier_cross/convention_split_map.pr",
    ]
    .into_iter()
    .map(|case| root.join(case))
    .collect::<Vec<_>>();
    run_cases(&cases, false);
}

// Keep engagement independent of the exact-cover CI split: isolated shard
// processes cannot add their counters together. This scan stops as soon as
// every adjacent pair of positions has changed lowered Core somewhere and
// performs no evaluation, so it retains the anti-vacuity contract without
// recreating the heavyweight sweep.
#[test]
fn tier_configurations_are_engaged() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(Path::new("."));
    let variants = variants();
    let activity: Vec<AtomicUsize> = (0..ACTIVITY_LABELS.len())
        .map(|_| AtomicUsize::new(0))
        .collect();
    let mut cases = FIXTURE_CASES
        .iter()
        .chain(ENGAGEMENT_SEED_CASES)
        .map(|case| root.join(case))
        .collect::<Vec<_>>();
    cases.extend(corpus_candidates());

    for case in cases {
        let full = source(&case);
        if !runnable_corpus_source(&full) {
            continue;
        }
        let dumped = variants
            .iter()
            .map(|variant| prism::dump_on(ENGAGEMENT_PHASE, &full, &roots, &variant.config))
            .collect::<Result<Vec<_>, _>>();
        let Ok(dumped) = dumped else { continue };
        let dumped = dumped.iter().map(String::as_str).collect::<Vec<_>>();
        record_lowered_activity(&dumped, &activity);
        if activity
            .iter()
            .all(|changed| changed.load(Ordering::Relaxed) > 0)
        {
            break;
        }
    }

    for (slot, label) in ACTIVITY_LABELS.into_iter().enumerate() {
        assert!(
            activity[slot].load(Ordering::Relaxed) > 0,
            "{label} changed no lowered Core in the runnable corpus; the sweep is vacuous"
        );
    }
}

#[test]
fn tier_configurations_have_identical_observation_traces() {
    if heavy_corpus_delegated() {
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut cases = sharded_corpus();
    cases.extend(FIXTURE_CASES.iter().map(|case| root.join(case)));
    // A shard cannot see aggregate engagement counts from its siblings. The
    // focused discovery test above retains that backstop; this sweep retains
    // exact-cover semantic equivalence over the whole corpus.
    run_cases(&cases, !corpus_is_sharded());
}

// The generated sweep: the deterministic program generator aimed at the tier
// relation. The generated fragment concentrates on handler shapes (full,
// partial, nested resumption arms) and arena regions, which is where the
// cascade's rungs actually disagree in structure, and any divergence shrinks
// greedily to a minimal reproducer before the test fails.

const FUZZ_SEED: u64 = 0x7469_6572_5f66_757a;
const DEFAULT_FUZZ_CASES: usize = 128;
const ARENA_CASE_DIVISOR: usize = 4;
const FUZZ_CASES_ENV: &str = "PRISM_TIER_FUZZ_CASES";

fn fuzz_cases() -> usize {
    std::env::var(FUZZ_CASES_ENV)
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_FUZZ_CASES)
}

fn family_count(programs: &[Program], family: ProgramFamily) -> usize {
    programs
        .iter()
        .filter(|program| program.family() == family)
        .count()
}

#[test]
fn generated_programs_have_identical_observation_traces_across_tiers() {
    let cases = fuzz_cases();
    let mut programs = generate(FUZZ_SEED, cases);
    programs.extend(generate_arena(FUZZ_SEED, cases / ARENA_CASE_DIVISOR));
    for family in [
        ProgramFamily::Pure,
        ProgramFamily::FullHandler,
        ProgramFamily::PartialHandler,
        ProgramFamily::Arena,
    ] {
        assert!(
            family_count(&programs, family) > 0,
            "tier fuzz seed {FUZZ_SEED:#018x} lost {family:?} coverage"
        );
    }

    let roots = default_roots(Path::new("."));
    let variants = variants();
    let activity: Vec<AtomicUsize> = (0..ACTIVITY_LABELS.len())
        .map(|_| AtomicUsize::new(0))
        .collect();
    let indexed: Vec<(usize, &Program)> = programs.iter().enumerate().collect();
    let divergences: Mutex<Vec<(usize, String)>> = Mutex::new(Vec::new());
    parallel_each(&indexed, |(index, program)| {
        let full = prism::with_prelude(&program.render());
        if let Err(failure) = check_source(
            &format!("generated case {index}"),
            &full,
            &roots,
            &variants,
            &activity,
        ) {
            divergences.lock().unwrap().push((*index, failure));
        }
        Ok::<(), String>(())
    });

    let total = programs.len();
    let mut divergences = divergences.into_inner().unwrap();
    divergences.sort_by_key(|(index, _)| *index);
    if let Some((index, failure)) = divergences.into_iter().next() {
        let failing = programs
            .into_iter()
            .nth(index)
            .expect("failing index is within the deterministic corpus");
        let (minimal, failure) = shrink(failing, failure, |candidate| {
            let full = prism::with_prelude(&candidate.render());
            check_source("shrink candidate", &full, &roots, &variants, &activity).err()
        });
        panic!(
            "tier divergence at seed {FUZZ_SEED:#018x}, case {index}, after shrinking:\n\
             {failure}\n\nminimal reproducer:\n{}",
            minimal.render()
        );
    }

    eprintln!(
        "tier-fuzz: {total} generated programs, {} tiers, {} lowered-Core evaluator runs",
        variants.len(),
        total * variants.len()
    );
    for (slot, label) in ACTIVITY_LABELS.into_iter().enumerate() {
        let changed = activity[slot].load(Ordering::Relaxed);
        eprintln!("tier-fuzz: {label} changed {changed} generated cases");
    }
}
