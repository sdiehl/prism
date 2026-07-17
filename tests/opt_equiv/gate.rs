//! Whole-corpus optimizer-equivalence gate.
//!
//! Optimization is a cost choice, so O0, O1, O2, and O2 with every supported
//! pass disable except mandatory newtype erasure
//! must produce the same canonical observation trace. Every configuration lowers
//! every runnable corpus program. The shared corpus definition excludes
//! nondeterministic host inputs, and two committed runnable engagement fixtures
//! keep the O1/O2 and CSE comparisons non-vacuous. Every configuration executes
//! directly: the verification seam runs the actual optimized, effect-lowered,
//! reference-counted, reuse-lowered Core handed toward code generation.
//!
//! This proves lowered-Core semantic equivalence, not native artifact or
//! continuation-metadata byte identity. The existing native parity and leak
//! gates independently prove that the backend implements Core correctly.
//! Optimization and disabled-pass labels remain part of artifact identity. The
//! verification evaluator makes no allocator, RC-count, or reuse-cost claim.
//!
//! This is a standalone release gate rather than part of the default test sweep:
//!
//! ```text
//! just opt-equiv
//! ```

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use prism::core::CorePass;
use prism::{default_roots, Config, ObservationTrace, OptLevel};

use crate::support::{corpus, parallel_check, source};

const DISABLEABLE_PASSES: [CorePass; 5] = [
    CorePass::Fuse,
    CorePass::Specialize,
    CorePass::Simplify,
    CorePass::Inline,
    CorePass::Cse,
];

#[derive(Debug)]
struct Variant {
    label: &'static str,
    config: Config,
}

impl Variant {
    fn level(label: &'static str, level: OptLevel) -> Self {
        let mut config = Config {
            opt: level,
            ..Config::default()
        };
        config.flags.compiler_cache = false;
        config.flags.quiet = true;
        Self { label, config }
    }

    fn without(label: &'static str, pass: CorePass) -> Self {
        let mut variant = Self::level(label, OptLevel::O2);
        variant.config.disabled.push(pass);
        variant
    }
}

fn variants() -> Vec<Variant> {
    vec![
        Variant::level("o0", OptLevel::O0),
        Variant::level("o1", OptLevel::O1),
        Variant::level("o2", OptLevel::O2),
        Variant::without("o2-no-fuse", DISABLEABLE_PASSES[0]),
        Variant::without("o2-no-specialize", DISABLEABLE_PASSES[1]),
        Variant::without("o2-no-simplify", DISABLEABLE_PASSES[2]),
        Variant::without("o2-no-inline", DISABLEABLE_PASSES[3]),
        Variant::without("o2-no-cse", DISABLEABLE_PASSES[4]),
    ]
}

fn record_lowered_activity(lowered: &[&str], activity: &[AtomicUsize]) {
    // O1 must differ from O0 somewhere, O2 from O1 somewhere, and removing each
    // supported optimizer pass from O2 must affect at least one committed
    // program. A disabled pass may also change effect-lowering tier; that remains
    // a valid semantic run. These are engagement checks for the configurations
    // whose observation equivalence the sweep claims to prove.
    for (slot, (left, right)) in [(0, 1), (1, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)]
        .into_iter()
        .enumerate()
    {
        if lowered[left] != lowered[right] {
            activity[slot].fetch_add(1, Ordering::Relaxed);
        }
    }
}

fn check_case(
    case: &Path,
    roots: &[prism::Root],
    variants: &[Variant],
    activity: &[AtomicUsize],
) -> Result<(), String> {
    let full = source(case);
    let mut runs: Vec<(&Variant, ObservationTrace, String)> = Vec::with_capacity(variants.len());
    for variant in variants {
        let (trace, lowered) = prism::driver::observe_lowered_run_on(&full, roots, &variant.config)
            .map_err(|error| {
                format!(
                    "{}: {} failed to observe lowered Core: {error}",
                    case.display(),
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
        return Err(format!("{}: optimizer matrix is empty", case.display()));
    };
    for (variant, trace, _) in &runs[1..] {
        if trace != baseline_trace {
            return Err(format!(
                "optimizer observation trace diverges for {}:\n  {}: {:?}\n  {}: {:?}",
                case.display(),
                baseline_variant.label,
                baseline_trace.observations,
                variant.label,
                trace.observations,
            ));
        }
    }
    Ok(())
}

const ACTIVITY_LABELS: [&str; 7] = [
    "O0 versus O1",
    "O1 versus O2",
    "O2 versus --no-fuse",
    "O2 versus --no-specialize",
    "O2 versus --no-simplify",
    "O2 versus --no-inline",
    "O2 versus --no-cse",
];

fn run_cases(cases: &[PathBuf], require_engagement: bool) {
    let roots = default_roots(Path::new("."));
    let variants = variants();
    let activity: Vec<AtomicUsize> = (0..7).map(|_| AtomicUsize::new(0)).collect();
    let fails = parallel_check(cases, |case| check_case(case, &roots, &variants, &activity));
    assert!(
        fails.is_empty(),
        "{} of {} optimizer-equivalence cases failed:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );

    eprintln!(
        "opt-equiv: {} cases, {} configurations, {} lowered-Core evaluator runs",
        cases.len(),
        variants.len(),
        cases.len() * variants.len()
    );
    for (slot, label) in ACTIVITY_LABELS.into_iter().enumerate() {
        let changed = activity[slot].load(Ordering::Relaxed);
        eprintln!("opt-equiv: {label} changed {changed} cases");
        if require_engagement {
            assert!(
                changed > 0,
                "{label} changed no lowered Core in the runnable corpus; the sweep is vacuous"
            );
        }
    }
}

#[test]
#[ignore = "focused optimizer-equivalence cost and correctness sample"]
fn optimizer_equivalence_representative_sample() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cases = [
        "examples/accum.pr",
        "examples/deriving.pr",
        "examples/eff_state.pr",
        "examples/handlers_funval.pr",
        "examples/fip_tree.pr",
        "examples/stream_fuse.pr",
        "examples/newtype_order.pr",
        "tests/cases/run/floats.pr",
        "tests/fixtures/opt_equiv/cse.pr",
        "tests/fixtures/opt_equiv/o2_fuse.pr",
    ]
    .into_iter()
    .map(|case| root.join(case))
    .collect::<Vec<_>>();
    run_cases(&cases, false);
}

#[test]
#[ignore = "standalone whole-corpus lowered-Core optimizer-equivalence gate"]
fn optimizer_configurations_have_identical_observation_traces() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut cases = corpus();
    cases.extend(
        [
            "tests/fixtures/opt_equiv/cse.pr",
            "tests/fixtures/opt_equiv/o2_fuse.pr",
        ]
        .into_iter()
        .map(|case| root.join(case)),
    );
    run_cases(&cases, true);
}
