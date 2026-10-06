//! Whole-corpus effect-tier equivalence gate.
//!
//! Tier selection is a cost choice, so every position must produce the same
//! canonical observation trace. Each forceable `EffectTier` floors the cascade
//! at one rung; the cascade still falls back to costlier rungs, and the
//! whole-program monad is legal for every program, so every position lowers
//! every runnable corpus program with no skip logic. Two unforced positions sit
//! above the forced ladder: the default compiler, which offers the consolidated
//! state route the whole program before any rung is asked, and the cascade
//! behind it with that route off, which asks the state rung the narrower
//! question the rung fixtures were written against. Diffing every floor against
//! both covers the ladder and the route that reaches past it. An additional
//! position explicitly enables continuation reification inside the consolidated
//! route, so its semantics are checked even while that option defaults off.
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

use prism::DumpPhase;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use prism::core::traverse::{Rewrite, Visit};
use prism::core::{Comp, Core, Value};
use prism::driver::ArtifactField;
use prism::{default_roots, Config, EffectTier, Observation, ObservationTrace};

use crate::support::fuzzgen::{generate, generate_arena, shrink, Program, ProgramFamily};
use crate::support::{
    corpus_candidates, corpus_is_sharded, heavy_corpus_delegated, parallel_check, parallel_each,
    runnable_corpus_source, sharded_corpus, source,
};

/// The tier axis only exists after effect lowering, so engagement scans dump
/// this phase alone: pre-lowering Core is tier-independent by construction.
const ENGAGEMENT_PHASE: DumpPhase = DumpPhase::Lowered;

/// Adjacent positions on the forced ladder, plus default versus reification.
/// Each pair must change lowered Core somewhere in the corpus, otherwise the
/// sweep between those positions is vacuous.
const COMPARISON_PAIRS: [(usize, usize); 6] = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 6)];

const ACTIVITY_LABELS: [&str; 6] = [
    "default versus cascade",
    "cascade versus state-fusion",
    "state-fusion versus local-partial",
    "local-partial versus selective-free-monad",
    "selective-free-monad versus whole-program-free-monad",
    "default versus reified continuations",
];

/// Committed programs whose effect plans are known to move under forcing; they
/// keep the sample and the whole-corpus extension non-vacuous.
const FIXTURE_CASES: &[&str] = &[
    "tests/fixtures/tier_cross/thunk_param.pr",
    "tests/fixtures/tier_cross/convention_split_map.pr",
    "tests/fixtures/tier_cross/convention_split_map_unrolled.pr",
];

/// Programs where work that must run once announces itself with a `shared`
/// line. Equal results alone cannot show that a tier shared a value rather than
/// recomputing it; a replayed prefix shows up here as an extra observation.
/// Each case names how many announcements a correct run prints.
const SHARED_WORK_CASES: &[(&str, usize)] = &[
    ("tests/fixtures/tier_equiv/shared_before_multishot.pr", 1),
    ("tests/fixtures/tier_equiv/shared_across_finally.pr", 1),
    ("tests/fixtures/tier_equiv/fold_accumulator_state.pr", 3),
];

/// The prefix every shared-work announcement starts with.
const SHARED_MARK: &str = "shared";

/// Corpus programs scanned first by the engagement discovery, one per rung the
/// blind alphabetical order reaches late. The local-partial rung in particular
/// is chosen by exactly one corpus program, so without seeding it the scan
/// walks most of the corpus (one lowering per position, per case) before the
/// local-partial/selective pair can engage.
const ENGAGEMENT_SEED_CASES: &[&str] = &[
    "examples/accum.pr",
    "examples/eff_state.pr",
    "tests/cases/run/local_mono_combined.pr",
    "examples/eff_yield.pr",
    "tests/cases/run/local_mono_multishot.pr",
];

#[derive(Debug)]
struct Variant {
    label: &'static str,
    config: Config,
}

impl Variant {
    fn tier(tier: EffectTier) -> Self {
        Self::with(tier.label(), tier, true)
    }

    /// The unforced cascade with the consolidated state route off. The route is
    /// offered the whole program before any rung is asked, so without this
    /// position the unforced compiler and forced state-fusion lower every
    /// effectful program alike and the first pair measures nothing.
    fn cascade() -> Self {
        Self::with("cascade", EffectTier::Auto, false)
    }

    fn reified() -> Self {
        let mut variant = Self::with(ArtifactField::Reify.label(), EffectTier::Auto, true);
        variant.config.update_flags(|flags| flags.reify = true);
        variant
    }

    fn with(label: &'static str, tier: EffectTier, consolidate: bool) -> Self {
        let mut config = Config::default();
        config.update_flags(|flags| flags.effect_tier = tier);
        config.update_flags(|flags| flags.consolidate = consolidate);
        config.update_flags(|flags| flags.reify = false);
        config.update_flags(|flags| flags.compiler_cache = false);
        config.update_flags(|flags| flags.quiet = true);
        Self { label, config }
    }
}

/// The unforced default first, then the cascade behind it, then the forced
/// rungs. Every position must agree observation for observation, and adjacent
/// ones must differ in lowered Core somewhere.
fn variants() -> Vec<Variant> {
    let mut all = vec![Variant::tier(EffectTier::Auto), Variant::cascade()];
    all.extend(
        EffectTier::ALL
            .into_iter()
            .filter(|tier| *tier != EffectTier::Auto)
            .map(Variant::tier),
    );
    all.push(Variant::reified());
    all
}

fn record_lowered_activity(lowered: &[&str], activity: &[AtomicUsize]) {
    for (slot, (left, right)) in COMPARISON_PAIRS.into_iter().enumerate() {
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
        "tier-equiv: {} cases, {} positions, {} lowered-Core evaluator runs",
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
        "tests/cases/run/local_mono_multishot.pr",
        "tests/fixtures/tier_cross/thunk_param.pr",
        "tests/fixtures/tier_cross/convention_split_map.pr",
    ]
    .into_iter()
    .map(|case| root.join(case))
    .collect::<Vec<_>>();
    run_cases(&cases, false);
}

/// The effect trampoline brackets a tail hop the native code cannot make a
/// tail call between `drive_enter` and `drive_leave`, spending a native
/// stack budget the lowered-Core observer does not have. The observer must
/// run the bracketed hop as a plain call and agree with the source
/// interpreter, which never sees the brackets. Agreement between lowered
/// positions alone cannot show that: every lowered position could fault on
/// the same unknown builtin and still agree with each other.
#[test]
fn reified_drive_brackets_observe_like_the_interpreter() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(Path::new("."));
    let full = source(&root.join("examples/delim.pr"));
    let reified = Variant::reified();

    let (trace, lowered) = prism::driver::observe_lowered_run_on(&full, &roots, &reified.config)
        .expect("delim.pr lowers under reified continuations");
    assert!(
        lowered.contains("drive_enter(") && lowered.contains("drive_leave("),
        "delim.pr no longer bounces under reified continuations, so this \
         check is vacuous; pick a program that does:\n{lowered}"
    );
    assert!(
        !trace
            .observations
            .iter()
            .any(|observation| matches!(observation, Observation::Fault(_))),
        "the lowered observer faulted on delim.pr: {:?}",
        trace.observations
    );

    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    let interpreted = prism::driver::observe_run_on(
        &full,
        &roots,
        &mut out,
        &mut input,
        &reified.config,
        Vec::new(),
    )
    .expect("delim.pr interprets");
    assert_eq!(
        trace, interpreted.canonical_trace,
        "lowered observer and source interpreter disagree on delim.pr"
    );

    let stdout = trace
        .observations
        .iter()
        .filter_map(|observation| match observation {
            Observation::Stdout(bytes) => Some(bytes.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect::<Vec<u8>>();
    assert_eq!(String::from_utf8(stdout).unwrap(), "101\n111\n121\n");
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
        "tier-fuzz: {total} generated programs, {} positions, {} lowered-Core evaluator runs",
        variants.len(),
        total * variants.len()
    );
    for (slot, label) in ACTIVITY_LABELS.into_iter().enumerate() {
        let changed = activity[slot].load(Ordering::Relaxed);
        eprintln!("tier-fuzz: {label} changed {changed} generated cases");
    }
}

/// Every position runs the shared work exactly as often as the source
/// interpreter does. The relation alone would let every tier replay alike, so
/// the default position is also held to the interpreter.
#[test]
fn shared_work_runs_once_on_every_tier() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cases = SHARED_WORK_CASES
        .iter()
        .map(|(case, _)| root.join(case))
        .collect::<Vec<_>>();
    run_cases(&cases, false);

    let roots = default_roots(Path::new("."));
    let config = &variants()[0].config;
    for (case, (_, expected)) in cases.iter().zip(SHARED_WORK_CASES) {
        let full = source(case);
        let (lowered, _) = prism::driver::observe_lowered_run_on(&full, &roots, config)
            .unwrap_or_else(|error| panic!("{}: {error}", case.display()));
        let interpreted = interpreted_trace(&full, &roots, config);
        assert_eq!(
            lowered,
            interpreted,
            "{}: the default position and the interpreter disagree",
            case.display()
        );
        assert_eq!(
            shared_marks(&interpreted),
            *expected,
            "{}: the interpreter ran the shared work a different number of times",
            case.display()
        );
    }
}

/// The negative control: plant a replay in one position's lowered Core and the
/// gate must see it. Every bind whose bound computation announces shared work
/// runs that computation a second time before its body, which is what a tier
/// that recomputes a captured prefix does.
#[test]
fn a_replayed_shared_prefix_diverges_the_trace() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(Path::new("."));
    for variant in variants() {
        for (case, _) in SHARED_WORK_CASES {
            let full = source(&root.join(case));
            let (honest, _) = prism::driver::observe_lowered_run_on(&full, &roots, &variant.config)
                .unwrap_or_else(|error| panic!("{case} at {}: {error}", variant.label));
            let mut planted = 0;
            let (replayed, _) = prism::driver::observe_lowered_run_rewritten_on(
                &full,
                &roots,
                &variant.config,
                |core| planted = replay_shared_work(core),
            )
            .unwrap_or_else(|error| panic!("{case} at {}: {error}", variant.label));
            assert!(
                planted > 0,
                "{case} at {}: no bind announces shared work, so the control is vacuous",
                variant.label
            );
            assert!(
                shared_marks(&replayed) > shared_marks(&honest),
                "{case} at {}: a replayed shared prefix left the trace unchanged",
                variant.label
            );
        }
    }
}

fn interpreted_trace(full: &str, roots: &[prism::Root], config: &Config) -> ObservationTrace {
    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    prism::driver::observe_run_on(full, roots, &mut out, &mut input, config, Vec::new())
        .expect("fixture interprets")
        .canonical_trace
}

fn stdout_of(trace: &ObservationTrace) -> String {
    let bytes = trace
        .observations
        .iter()
        .filter_map(|observation| match observation {
            Observation::Stdout(bytes) => Some(bytes.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect::<Vec<u8>>();
    String::from_utf8(bytes).expect("fixture output is UTF-8")
}

fn shared_marks(trace: &ObservationTrace) -> usize {
    stdout_of(trace)
        .lines()
        .filter(|line| line.starts_with(SHARED_MARK))
        .count()
}

fn replay_shared_work(core: &mut Core) -> usize {
    let mut replay = ReplayShared { planted: 0 };
    for function in &mut core.fns {
        function.body = replay.rewrite_comp(&function.body, &());
    }
    replay.planted
}

struct ReplayShared {
    planted: usize,
}

impl Rewrite for ReplayShared {
    type Ctx = ();

    fn leave_comp(&mut self, _source: &Comp, rewritten: Comp, _cx: &()) -> Comp {
        match rewritten {
            Comp::Bind(bound, binder, body) if announces_shared(&bound) => {
                self.planted += 1;
                let again = Comp::Bind(bound.clone(), binder, body);
                Comp::Bind(bound, binder, Box::new(again))
            }
            other => other,
        }
    }
}

fn announces_shared(comp: &Comp) -> bool {
    struct Find(bool);
    impl Visit for Find {
        fn value(&mut self, value: &Value) -> bool {
            if let Value::Str(text) = value {
                self.0 |= text.starts_with(SHARED_MARK);
            }
            !self.0
        }
    }
    let mut find = Find(false);
    find.walk_comp(comp);
    find.0
}
