use std::path::Path;
use std::process::Command;

use serde_json::Value;

#[test]
fn bootstrap_check_reports_parity_and_coverage() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(root)
        .args([
            "bootstrap",
            "check",
            "tests/fixtures/bootstrap/t1.pr",
            "--json",
        ])
        .output()
        .expect("run bootstrap check");
    assert!(
        output.status.success(),
        "bootstrap check failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("bootstrap JSON");
    assert_eq!(report["schema"], "prism-bootstrap-check-v1");
    assert_eq!(report["authority"], "rust");
    assert_eq!(report["shadow"], "prism-t1");
    assert_eq!(report["status"], "parity");
    assert!(report["first_divergence"].is_null());
    let supported = report["coverage"]["supported_nodes"]
        .as_u64()
        .expect("supported node count");
    let total = report["coverage"]["total_nodes"]
        .as_u64()
        .expect("total node count");
    assert!(supported < total);
    assert_eq!(report["unsupported"][0]["function"], "later");
    assert_eq!(report["unsupported"][0]["kind"], "list");
    assert!(report["facts"]
        .as_array()
        .expect("facts")
        .iter()
        .all(|fact| fact["agrees"].as_bool() == Some(true)));
}
