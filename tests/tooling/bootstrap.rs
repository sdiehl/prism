use std::fs;
use std::path::Path;
use std::process::Command;

use serde_json::Value;

/// The pure first-order fixture and its pinned fail-closed boundary: a list,
/// three rank-n paths, and a higher-kinded application stay uncovered.
const PURE_FIXTURE: &str = "tests/fixtures/bootstrap/t1.pr";
const PURE_SUPPORTED: u64 = 81;
const PURE_TOTAL: u64 = 94;
const PURE_UNCOVERED: &[(&str, &str)] = &[
    ("later", "list"),
    ("nested", "nested-forall"),
    ("higher_kinded", "higher-kinded-application"),
    ("annotated_nested", "nested-forall"),
    ("rankn_field", "nested-forall"),
];

/// The effect-row fixture and its pinned coverage: operation schemes or label
/// arguments the shadow cannot represent remain explicit, named refusals.
const ROW_FIXTURE: &str = "tests/fixtures/bootstrap/t2.pr";
const ROW_SUPPORTED: u64 = 133;
const ROW_TOTAL: u64 = 163;
const ROW_UNCOVERED: &[(&str, &str)] = &[
    ("nested_open", "effect-row-open"),
    ("annotated_open", "effect-row-open"),
    ("make_runner", "effect-row-open"),
    ("strays", "external-operation"),
    ("run_pure", "external-operation"),
    ("make_task", "row-kinded-data-argument"),
    ("task_id", "row-kinded-data-argument"),
    ("launch_tick", "external-operation"),
    ("unboxed_label", "unboxed-type"),
    ("usage_label", "usage-qualified-type"),
];

const BARE_ROW_LABEL_FIXTURE: &str = "tests/fixtures/bootstrap/t2_bare_row_label.pr";

/// The handler fixture and its pinned coverage. Exhaustive anonymous and named
/// handlers are checked, and partial handlers are checked through operation-use
/// evidence: a walk over the handled body records which operations it is known
/// to perform, and a partial handler discharges an effect exactly when every
/// known use is covered by a clause.
const HANDLER_FIXTURE: &str = "tests/fixtures/bootstrap/t3.pr";
const HANDLER_SUPPORTED: u64 = 299;
const HANDLER_TOTAL: u64 = 299;
const HANDLER_UNCOVERED: &[(&str, &str)] = &[];

/// A byte copy of the pure fixture, in a directory that also defines the two
/// modules the shadow itself imports.
const HOSTILE_FIXTURE: &str = "tests/fixtures/bootstrap/hostile/t1.pr";
/// The report field that legitimately differs between the two copies.
const SOURCE_FIELD: &str = "source";

fn check(fixture: &str) -> Value {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .env_remove("PRISM_TOOL_PACKAGES_ROOT")
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
    if uncovered.is_empty() {
        assert_eq!(supported, total);
    } else {
        assert!(supported < total);
    }
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
    let report = check(PURE_FIXTURE);
    assert_parity(&report, PURE_SUPPORTED, PURE_TOTAL, PURE_UNCOVERED);
    // A written type variable is one of the declaration's quantifiers, so the
    // canonical spelling places it by position rather than by the name it was
    // written with.
    assert_eq!(scheme(&report, "ident"), "forall $0. ($0) -> $0");
    assert_eq!(
        scheme(&report, "swap"),
        "forall $0 $1. (($0, $1)) -> ($1, $0)"
    );
    assert_eq!(
        scheme(&report, "use_fn"),
        "forall $0 $1. (($0) -> $1, $0) -> $1"
    );
    // The order of those quantifiers is itself part of the spelling, and this
    // is the case that can tell the two orders apart: `y` is inferred and `a`
    // is written, so the inferred binder is first and the written one second.
    assert_eq!(
        scheme(&report, "mixed_pair"),
        "forall $0 $1. ($1, $0) -> ($1, $0)"
    );
    // `z` is encountered before `a`, despite sorting after it.
    assert_eq!(
        scheme(&report, "written_order"),
        "forall $0 $1. ($0, $1) -> ($0, $1)"
    );
    // The alias cannot escape the parameter's monomorphic class, while an
    // independently owned local identity remains polymorphic.
    assert_eq!(scheme(&report, "leaked"), "(Bool) -> Int");
    assert_eq!(scheme(&report, "kept_poly"), "(Int) -> (Int, Bool)");
    assert_eq!(scheme(&report, "duplicate"), "forall $0. ($0) -> ($0, $0)");
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
    // An effect applied to a type argument, which is where a row stops being a
    // set of names: the argument is written here, inferred and quantified in
    // `borrowed`, and positional in `use_pair`, where `Pair(Int, Bool)` is what
    // makes `left` the one that answers with an `Int`.
    assert_eq!(scheme(&report, "later"), "() -> Int ! {Cell(Int)}");
    assert_eq!(
        scheme(&report, "callback_cell"),
        "forall $0. (() -> Unit ! {$0}) -> Unit ! {Cell(() -> Unit ! {$0})}"
    );
    assert_eq!(
        scheme(&report, "borrowed"),
        "forall $0. () -> $0 ! {Cell($0)}"
    );
    assert_eq!(
        scheme(&report, "marked"),
        "forall $0. () -> Unit ! {Mark($0)}"
    );
    assert_eq!(scheme(&report, "unmarked"), "() -> Unit");
    assert_eq!(
        scheme(&report, "nat_label"),
        "() -> Unit ! {Mark(Sized(3))}"
    );
    assert_eq!(
        scheme(&report, "use_pair"),
        "() -> (Bool, Int) ! {Pair(Int, Bool)}"
    );
    assert_eq!(
        scheme(&report, "borrowed_pair"),
        "forall $0 $1. () -> ($0, $1) ! {Pair($1, $0)}"
    );
    assert_eq!(
        scheme(&report, "ticked_cell"),
        "() -> Int ! {Cell(Int), Tick}"
    );
    assert_eq!(scheme(&report, "holds"), "() -> Unit ! {Loose(Int)}");
    // Written row variables are branded after inference. One spelling shares
    // within a declaration, different spellings and declarations stay fresh,
    // and widening can add body effects before that brand becomes rigid.
    assert_eq!(
        scheme(&report, "relay"),
        "forall $0 $1 $2. (($1) -> $2 ! {Tick, $0}, $1) -> $2 ! {Tick, $0}"
    );
    assert_eq!(
        scheme(&report, "relay2"),
        "forall $0 $1 $2. ($1, ($1) -> $2 ! {$0}) -> $2 ! {$0}"
    );
    assert_eq!(
        scheme(&report, "two_rows"),
        "forall $0 $1. ((Int) -> Int ! {$0}, (Bool) -> Bool ! {$1}) -> \
         ((Int) -> Int ! {$0}, (Bool) -> Bool ! {$1})"
    );
    let same_row = "forall $0. ((Int) -> Int ! {$0}, Int) -> Int ! {$0}";
    assert_eq!(scheme(&report, "same_row_one"), same_row);
    assert_eq!(scheme(&report, "same_row_two"), same_row);
    assert_eq!(
        scheme(&report, "widened"),
        "forall $0. ((Int) -> Int ! {Say, Tick, $0}, Int) -> Int ! {Say, Tick, $0}"
    );
    // The unused callback tail is hidden only from display. Passing an
    // effectful callback still instantiates the structural row binder.
    assert_eq!(scheme(&report, "no_call"), "(() -> Unit) -> Unit ! {Tick}");
    assert_eq!(scheme(&report, "no_call_effectful"), "() -> Unit ! {Tick}");
    assert_eq!(
        scheme(&report, "shifted"),
        "forall $0 $1 $2. (() -> Unit, ($1) -> $2 ! {$0}, $1) -> $2 ! {$0}"
    );
}

/// A lowercase row name in label position is not an implicit open tail. The
/// compiler must reject it before the bootstrap shadow is asked for evidence.
#[test]
fn bootstrap_open_row_requires_tail_syntax() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .env_remove("PRISM_TOOL_PACKAGES_ROOT")
        .args(["check", BARE_ROW_LABEL_FIXTURE])
        .output()
        .expect("check bare row label fixture");
    assert!(
        !output.status.success(),
        "bare row label unexpectedly checked"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[E5001]") && stderr.contains("unknown effect `e`"),
        "unexpected diagnostic for bare row label:\n{stderr}"
    );
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
    assert_eq!(scheme(&report, "named_instance"), "() -> Int");
    assert_eq!(scheme(&report, "applied_handler"), "forall $0. ($0) -> $0");
    assert_eq!(
        scheme(&report, "function_valued_handler"),
        "(() -> Int ! {Cell(Int)}) -> Int"
    );
    assert_eq!(scheme(&report, "nested_applied_scope"), "() -> String");
    assert_eq!(scheme(&report, "named_consistent"), "() -> Int");
    assert_eq!(
        scheme(&report, "named_ambient"),
        "() -> (Int, String) ! {Cell(String)}"
    );
    // Partial discharge turns on operation-use evidence, so pin all three
    // sides of the rule: a use its clauses do not cover retains the effect, a
    // covered use discharges it, and a use hidden behind a declared row is
    // opaque and retains it.
    assert_eq!(scheme(&report, "partial_cover"), "() -> Int ! {Store}");
    assert_eq!(scheme(&report, "partial_covered"), "() -> Int");
    assert_eq!(scheme(&report, "partial_opaque"), "() -> Int ! {Store}");
    assert_eq!(scheme(&report, "named_operation_shadow"), "() -> Int");
    assert_eq!(
        scheme(&report, "anonymous_outer_operation_shadow"),
        "() -> Unit"
    );
    assert_eq!(scheme(&report, "named_outer_operation_shadow"), "() -> Int");
    assert_eq!(scheme(&report, "named_explicit_instance"), "() -> Int");
}

/// The compiler, not the checked project, chooses the shadow that judges it.
///
/// Module resolution is first-hit and a source directory root precedes the
/// embedded standard library, so a target that defines `Tc` or `Syntax.Codec`
/// would supply the shadow's own checker and decoder if the shadow resolved
/// against the target's search path. The same program checked with those
/// modules present and absent must produce the same report.
#[test]
fn bootstrap_shadow_ignores_target_modules_named_like_its_own() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(
        fs::read(root.join(PURE_FIXTURE)).expect("pure fixture"),
        fs::read(root.join(HOSTILE_FIXTURE)).expect("hostile fixture"),
        "the hostile copy must stay a byte copy of {PURE_FIXTURE}, or the two \
         reports differ for an uninteresting reason"
    );

    let mut hostile = check(HOSTILE_FIXTURE);
    assert_parity(&hostile, PURE_SUPPORTED, PURE_TOTAL, PURE_UNCOVERED);

    // Everything but the file it was run on is identical, so no field of the
    // verdict can drift with a module the target happened to define.
    let mut pure = check(PURE_FIXTURE);
    for report in [&mut pure, &mut hostile] {
        report
            .as_object_mut()
            .expect("report object")
            .remove(SOURCE_FIELD);
    }
    assert_eq!(pure, hostile);
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
