//! Committed resource baselines for the optimization fixtures under
//! `examples/fixtures/compiler/`.
//!
//! Each fixture stages a cost the compiler does not yet remove: a constructor
//! allocated behind a non-inlined call, a callback that allocates per element,
//! a product boxed across a boundary. The manifest records what each one costs
//! today (interpreter transitions, native cells materialized, cells reused in
//! place), so a rewrite that claims to remove a cost must move a recorded
//! number, and a regression that quietly adds one is caught the same way. The
//! counts are exact deterministic counts, not timings, so one sample is the
//! whole distribution and the comparison is equality, not a band.
//!
//! These fixtures are not in the parity corpus (the corpus walk does not
//! recurse into `examples/fixtures/`), so this gate also carries their
//! leak-balance check.

use std::fmt::Write as _;
use std::path::Path;
use std::{env, fs};

use prism::error::Error;
use prism::{build_on, default_roots, Config};

use crate::support::{
    require_cc, source, stat_build_counters, ALLOCATED_SUFFIX, ALLOC_STATS, CHECK_LEAKS,
    LEAKED_SUFFIX, REUSED_SUFFIX, REUSE_STATS,
};

/// The committed golden this gate diffs against.
const BASELINE_MANIFEST: &str = "tests/optimizer_baseline.txt";
/// Set to regenerate the manifest from a reviewed run instead of diffing it.
const BASELINE_ACCEPT: &str = "PRISM_ACCEPT_OPTIMIZER_BASELINE";

/// The fixture programs this gate measures: every runnable optimization
/// fixture. The arena promotion trio is deliberately absent; its counters are
/// pinned by the promotion oracle in `perf_gate.rs`.
const FIXTURES: &[&str] = &[
    "examples/fixtures/compiler/ctor_cross_call.pr",
    "examples/fixtures/compiler/deep_immutable.pr",
    "examples/fixtures/compiler/exact_size_filter.pr",
    "examples/fixtures/compiler/exact_size_map.pr",
    "examples/fixtures/compiler/ho_once_wrapper.pr",
    "examples/fixtures/compiler/iter_callback.pr",
    "examples/fixtures/compiler/known_closure.pr",
    "examples/fixtures/compiler/opaque_kill.pr",
    "examples/fixtures/compiler/unboxed_cross.pr",
    "examples/fixtures/compiler/vec128_cross.pr",
];

const MANIFEST_HEADER: &str = r"# Resource baselines for the optimization fixtures. One
# `<program>\t<interpreter steps>\t<native cells allocated>\t<cells reused>` line
# per fixture, sorted. Checked exactly (the counts are deterministic): a decrease
# is an optimization win the baseline has not recorded yet, an increase is a cost
# regression no other gate sees. Review the diff, then regenerate with
# PRISM_ACCEPT_OPTIMIZER_BASELINE=1. Do not hand-edit.
";

/// One fixture's measured baseline row.
struct BaselineRow {
    label: &'static str,
    interp_steps: i64,
    native_cells: i64,
    reused_cells: i64,
}

fn quiet_cfg() -> Config {
    let mut cfg = Config::from_env();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = false);
    cfg
}

fn measure(label: &'static str) -> BaselineRow {
    let full = source(Path::new(label));
    let counters = stat_build_counters(
        &full,
        label,
        &[CHECK_LEAKS, ALLOC_STATS, REUSE_STATS],
        &[LEAKED_SUFFIX, ALLOCATED_SUFFIX, REUSED_SUFFIX],
        |src, bin| -> Result<(), Error> {
            build_on(src, &default_roots(Path::new(".")), bin, &quiet_cfg())
        },
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        counters[0], 0,
        "{label}: native run leaked {} cells",
        counters[0]
    );
    let reference = prism::interpret(&full).unwrap_or_else(|e| panic!("{label}: interpret: {e:?}"));
    BaselineRow {
        label,
        interp_steps: i64::try_from(reference.steps).unwrap_or(i64::MAX),
        native_cells: counters[1],
        reused_cells: counters[2],
    }
}

fn render(rows: &[BaselineRow]) -> String {
    let mut out = String::from(MANIFEST_HEADER);
    for r in rows {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}",
            r.label, r.interp_steps, r.native_cells, r.reused_cells
        );
    }
    out
}

#[test]
fn optimizer_fixture_costs_match_baseline() {
    require_cc();
    let rows: Vec<BaselineRow> = FIXTURES.iter().map(|f| measure(f)).collect();
    // The anti-vacuity floor: the staged cost is real today, whatever its exact
    // count. The constructor fixture must materialize heap cells; a fixture
    // that reads as free no longer stages anything, and no accept run may
    // record that silently.
    let ctor = rows
        .iter()
        .find(|r| r.label.ends_with("ctor_cross_call.pr"));
    assert!(
        ctor.is_some_and(|r| r.native_cells > 0),
        "ctor_cross_call allocates nothing; the fixture no longer stages its cost"
    );
    let rendered = render(&rows);
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(BASELINE_MANIFEST);
    if env::var_os(BASELINE_ACCEPT).is_some() {
        fs::write(&path, rendered).expect("write optimizer baseline");
        return;
    }
    let golden = fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read {BASELINE_MANIFEST}: {e}; regenerate with {BASELINE_ACCEPT}=1 from a \
             native-capable run"
        )
    });
    assert_eq!(
        golden, rendered,
        "optimization-fixture resource costs moved. A decrease is an unrecorded win, an \
         increase is a cost regression; review the diff, then regenerate with {BASELINE_ACCEPT}=1"
    );
}
