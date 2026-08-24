use std::fs;
use std::path::Path;
use std::process::{self, Command};

use serde_json::Value;

const PURE_FIXTURE: &str = "tests/fixtures/bootstrap/t1.pr";
const ROW_FIXTURE: &str = "tests/fixtures/bootstrap/t2.pr";

#[test]
fn bootstrap_batch_prepares_once_and_evaluates_each_target_fresh() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .env("PRISM_TIME_COMPILE", "1")
        .env_remove("PRISM_TOOL_PACKAGES_ROOT")
        .args(["bootstrap", "check", PURE_FIXTURE, ROW_FIXTURE, "--json"])
        .output()
        .expect("run bootstrap batch");
    assert!(
        output.status.success(),
        "bootstrap batch failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let reports: Value = serde_json::from_slice(&output.stdout).expect("bootstrap batch JSON");
    let reports = reports.as_array().expect("batch report array");
    assert_eq!(reports.len(), 2);
    assert!(reports.iter().all(|report| report["status"] == "parity"));

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stderr
            .matches("bootstrap-time\tchecker_front_prepare\t")
            .count(),
        1
    );
    assert_eq!(
        stderr.matches("bootstrap-time\ttarget_artifacts\t").count(),
        2
    );
    assert_eq!(stderr.matches("bootstrap-time\tshadow_eval\t").count(), 2);
}

#[test]
fn target_modules_cannot_supply_the_checker_or_its_codec() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let hostile =
        std::env::temp_dir().join(format!("prism_bootstrap_hostile_modules_{}", process::id()));
    if hostile.exists() {
        fs::remove_dir_all(&hostile).expect("clear stale hostile fixture");
    }
    fs::create_dir_all(hostile.join("Syntax")).expect("create hostile fixture");
    fs::copy(root.join(PURE_FIXTURE), hostile.join("main.pr")).expect("copy target program");
    fs::write(hostile.join("Tc.pr"), "not valid Prism source\n").expect("write hostile Tc");
    fs::write(
        hostile.join("Syntax").join("Codec.pr"),
        "not valid Prism source\n",
    )
    .expect("write hostile Syntax.Codec");

    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .env("PRISM_TOOL_PACKAGES_ROOT", root.join("packages"))
        .arg("bootstrap")
        .arg("check")
        .arg(hostile.join("main.pr"))
        .arg("--json")
        .output()
        .expect("run checker with hostile target modules");
    fs::remove_dir_all(&hostile).expect("remove hostile fixture");

    assert!(
        output.status.success(),
        "target module shadowed compiler-owned code: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("bootstrap JSON");
    assert_eq!(report["status"], "parity");
}
