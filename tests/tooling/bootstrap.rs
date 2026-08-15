use std::path::Path;
use std::process::Command;

use serde_json::Value;

/// The pure first-order fixture and the coverage it is pinned at: one
/// declaration out of reach, over a list.
const PURE_FIXTURE: &str = "tests/fixtures/bootstrap/t1.pr";
const PURE_SUPPORTED: u64 = 45;
const PURE_TOTAL: u64 = 48;
const PURE_UNCOVERED: &[(&str, &str)] = &[("later", "list")];

/// The effect-row fixture and its pinned coverage: one declaration out of
/// reach, over an effect applied to a type argument.
const ROW_FIXTURE: &str = "tests/fixtures/bootstrap/t2.pr";
const ROW_SUPPORTED: u64 = 64;
const ROW_TOTAL: u64 = 66;
const ROW_UNCOVERED: &[(&str, &str)] = &[("later", "effect-row-applied")];

/// The handler fixture and its pinned coverage: two declarations out of reach,
/// a partial handler and a named handler instance, both of which hide which
/// effect a clause discharges.
const HANDLER_FIXTURE: &str = "tests/fixtures/bootstrap/t3.pr";
const HANDLER_SUPPORTED: u64 = 131;
const HANDLER_TOTAL: u64 = 145;
const HANDLER_UNCOVERED: &[(&str, &str)] = &[
    ("partial_cover", "handle-partial"),
    ("named_instance", "handle-named"),
];

fn check(fixture: &str) -> Value {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .args(["bootstrap", "check", fixture, "--json"])
        .output()
        .expect("run bootstrap check");
    assert!(
        output.status.success(),
        "bootstrap check failed on {fixture}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("bootstrap JSON")
}

/// The report's shape, its parity verdict, and the contract it speaks, checked
/// the same way for every fixture.
fn assert_parity(report: &Value, supported: u64, total: u64, uncovered: &[(&str, &str)]) {
    assert_eq!(report["schema"], "prism-bootstrap-check-v2");
    assert_eq!(report["scheme_contract"], prism::SCHEME_CANON_CONTRACT);
    assert_eq!(report["authority"], "rust");
    assert_eq!(report["shadow"], "prism-t1");
    assert_eq!(report["status"], "parity");
    assert!(report["first_divergence"].is_null());
    assert_eq!(
        report["coverage"]["supported_nodes"].as_u64(),
        Some(supported)
    );
    assert_eq!(report["coverage"]["total_nodes"].as_u64(), Some(total));
    assert!(supported < total);
    let rows = report["unsupported"].as_array().expect("unsupported");
    assert_eq!(rows.len(), uncovered.len());
    for (row, (function, kind)) in rows.iter().zip(uncovered) {
        assert_eq!(row["function"], *function);
        assert_eq!(row["kind"], *kind);
    }
    let facts = report["facts"].as_array().expect("facts");
    assert!(facts
        .iter()
        .all(|fact| fact["agrees"].as_bool() == Some(true)));
    // The stamped contract holds live: every authoritative spelling in the
    // report is already its own canonical form.
    for rust in facts.iter().filter_map(|fact| fact["rust"].as_str()) {
        assert_eq!(prism::canonical_scheme(rust), rust);
    }
}

#[test]
fn bootstrap_check_reports_parity_and_coverage() {
    assert_parity(
        &check(PURE_FIXTURE),
        PURE_SUPPORTED,
        PURE_TOTAL,
        PURE_UNCOVERED,
    );
}

/// Effect rows are checked, not skipped: the shadow infers what a declaration
/// performs and agrees with the authority on the spelling.
#[test]
fn bootstrap_check_agrees_on_effect_rows() {
    let report = check(ROW_FIXTURE);
    assert_parity(&report, ROW_SUPPORTED, ROW_TOTAL, ROW_UNCOVERED);
    // The row is what is under test, so pin the spellings that carry one: an
    // annotation narrowed to what the body performs, a row inferred without an
    // annotation, and a body that performs nothing staying pure.
    assert_eq!(scheme(&report, "wider"), "() -> Int ! {Tick}");
    assert_eq!(scheme(&report, "inferred"), "(Int) -> Int ! {Tick}");
    assert_eq!(scheme(&report, "still_pure"), "(Int) -> Int");
    assert_eq!(scheme(&report, "both"), "(Int) -> Unit ! {Say, Tick}");
}

/// Handlers are checked, not skipped: installing one subtracts the effects its
/// clauses cover from the row, and only what survives is still performed.
#[test]
fn bootstrap_check_agrees_on_handlers() {
    let report = check(HANDLER_FIXTURE);
    assert_parity(&report, HANDLER_SUPPORTED, HANDLER_TOTAL, HANDLER_UNCOVERED);
    // Discharge is what is under test, so pin the spellings that turn on it: a
    // handled effect leaving the row entirely, an unhandled one staying in it,
    // and a clause's own effects landing where the handler is installed.
    assert_eq!(scheme(&report, "discharged"), "() -> Int");
    assert_eq!(scheme(&report, "nested"), "() -> Int");
    assert_eq!(scheme(&report, "leftover"), "() -> Unit ! {Say}");
    assert_eq!(scheme(&report, "clause_performs"), "() -> Int ! {Say}");
}

/// The authority's spelling for one declaration of a report.
fn scheme(report: &Value, name: &str) -> String {
    report["facts"]
        .as_array()
        .expect("facts")
        .iter()
        .find(|fact| fact["name"] == name)
        .and_then(|fact| fact["rust"].as_str())
        .unwrap_or_else(|| panic!("no fact for {name}"))
        .to_owned()
}
