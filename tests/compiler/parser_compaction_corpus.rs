//! Structural gate for the independent parser-compaction corpus.
//!
//! The Python driver owns byte hashing and the generated ledgers. These tests
//! use its read-only `check` mode and assert both completed receipts and the
//! pending depth and mutation ledgers.

use std::path::Path;
use std::process::Command;

#[path = "parser_compaction_entry_adapter.rs"]
#[allow(clippy::redundant_pub_crate)]
mod entry_adapter;

// The shared adapter is also compiled as a standalone binary by the corpus
// acceptance driver. Keep its binary entry live when this file includes it as
// an integration-test module.
const _: fn() = entry_adapter::main;

const ORACLE: &str = "46886c1fa7064e4809020c1b788b3ee3531d6a63";

fn check(section: &str) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new("python3")
        .current_dir(root)
        .arg("scripts/parser-compaction-corpus.py")
        .arg("check")
        .arg("--oracle")
        .arg(ORACLE)
        .arg("--section")
        .arg(section)
        .output()
        .unwrap_or_else(|error| panic!("run parser-compaction checker: {error}"));
    assert!(
        output.status.success(),
        "parser-compaction {section} check failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

fn tranche3_plan() -> serde_json::Value {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new("python3")
        .current_dir(root)
        .arg("scripts/parser-compaction-corpus.py")
        .arg("tranche3-plan")
        .arg("--oracle")
        .arg(ORACLE)
        .output()
        .unwrap_or_else(|error| panic!("run parser-compaction tranche-3 plan: {error}"));
    assert!(
        output.status.success(),
        "parser-compaction tranche-3 plan failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    serde_json::from_slice(&output.stdout).expect("decode parser-compaction tranche-3 plan")
}

fn mutation_sample() -> serde_json::Value {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let bytes = std::fs::read(root.join("tests/fixtures/parser/compaction/mutation-sample.json"))
        .expect("read parser-compaction mutation sample");
    serde_json::from_slice(&bytes).expect("decode parser-compaction mutation sample")
}

#[test]
fn parser_compaction_corpus() {
    check("corpus");
}

#[test]
fn parser_compaction_coverage() {
    check("coverage");
}

#[test]
fn parser_compaction_mutations() {
    check("mutations");
}

#[test]
fn parser_compaction_mutation_sample_receipt() {
    let sample = mutation_sample();
    assert_eq!(
        sample["status"],
        "reviewed-local-rust-reproduction-not-content-addressed"
    );
    assert_eq!(sample["totals"]["scheduled"], 32);
    assert_eq!(sample["totals"]["applicable"], 24);
    assert_eq!(sample["totals"]["handwritten_exact"], 21);
    assert_eq!(sample["totals"]["handwritten_mismatch"], 3);
    assert_eq!(
        sample["candidates"]
            .as_array()
            .expect("mutation candidates")
            .len(),
        24
    );
    let witnesses = sample["witnesses"].as_array().expect("mutation witnesses");
    assert_eq!(witnesses.len(), 6);
    let mut exact = witnesses
        .iter()
        .filter(|witness| witness["status"] == "exact")
        .map(|witness| witness["source"].as_str().expect("witness source"))
        .collect::<Vec<_>>();
    exact.sort_unstable();
    assert_eq!(
        exact,
        [
            "mutations/minimized/pattern-record-wrong-close.pr",
            "mutations/minimized/type-truncated-annotation.pr",
            "mutations/minimized/vertical-elif-newline-delete.pr",
        ]
    );
    let mut pending = witnesses
        .iter()
        .filter(|witness| witness["status"] == "expected-delta")
        .map(|witness| witness["source"].as_str().expect("witness source"))
        .collect::<Vec<_>>();
    pending.sort_unstable();
    assert_eq!(
        pending,
        [
            "mutations/minimized/cross-retired-effect-order.pr",
            "mutations/minimized/vertical-elif-missing-operator.pr",
            "mutations/minimized/vertical-try-prefix-swap.pr",
        ]
    );
    let candidates = sample["candidates"]
        .as_array()
        .expect("mutation candidates");
    for id in [
        "type-064-a3ec50f39aec",
        "pattern-320-def1263f2e60",
        "vertical-448-56c9fc85615f",
        "cross-000-80a9a1b38680",
    ] {
        let candidate = candidates
            .iter()
            .find(|candidate| candidate["id"] == id)
            .unwrap_or_else(|| panic!("missing resolved mutation candidate {id}"));
        assert_eq!(candidate["handwritten_status"], "exact");
    }
}

#[test]
fn parser_compaction_entries() {
    entry_adapter::check_committed_receipt(Path::new(env!("CARGO_MANIFEST_DIR")));
    check("entries");
}

#[test]
fn parser_compaction_vertical() {
    check("vertical");
}

#[test]
fn parser_compaction_depth() {
    check("depth");
}

#[test]
fn parser_compaction_tranche3_infrastructure() {
    let plan = tranche3_plan();
    assert_eq!(
        plan["depth"]["status"],
        "generators-implemented-boundaries-unmeasured"
    );
    assert_eq!(plan["depth"]["declared_axis_count"], 13);
    let axes = plan["depth"]["axes"].as_array().expect("depth axes");
    assert_eq!(axes.len(), 13);
    assert!(axes
        .iter()
        .all(|axis| axis["boundary_status"] == "uncalibrated"));
    let lanes = plan["mutations"]["lanes"]
        .as_array()
        .expect("mutation lanes");
    assert_eq!(lanes.len(), 4);
    assert!(lanes.iter().all(|lane| lane["generated"] == 512));
    assert!(lanes
        .iter()
        .all(|lane| lane["applicable"].as_u64().unwrap_or(0) > 0));
}
