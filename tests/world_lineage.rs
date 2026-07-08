//! CLI-level world-timeline regressions over the committed fixture.
//!
//! `tests/fixtures/world.plineage` is a hand-shaped two-branch timeline: branch 0
//! runs the Conway rule over ticks 0..4, and branch 1 forks unperturbed at tick 2
//! under a second rule. It is the shape contract the browser emitter targets and
//! the Rust decoder accepts; these cases drive `prism lineage show/why/verify` over
//! it so a change to the world node/edge vocabulary that breaks the CLI is caught.

use std::path::Path;
use std::process::Command;

const FIXTURE: &str = "tests/fixtures/world.plineage";
// The HighLife tip: branch 1, tick 4. Its full content-hash id and a prefix a user
// would copy from the resident (which shows truncated hashes).
const TIP: &str = "f844444444444444444444444444444444444444444444444444444444444444";
const TIP_PREFIX: &str = "f84";

const fn prism_bin() -> &'static str {
    env!("CARGO_BIN_EXE_prism")
}

fn run(args: &[&str]) -> (bool, String) {
    let output = Command::new(prism_bin())
        .args(args)
        .output()
        .expect("runs prism");
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    (output.status.success(), text)
}

#[test]
fn fixture_exists() {
    assert!(
        Path::new(FIXTURE).exists(),
        "the committed world fixture must exist"
    );
}

#[test]
fn show_summarizes_the_timeline() {
    let (ok, out) = run(&["lineage", "show", FIXTURE]);
    assert!(ok, "show succeeds: {out}");
    assert!(out.contains("world timeline (7 states)"), "{out}");
    assert!(out.contains("B3/S23"), "names the Conway law: {out}");
    assert!(out.contains("B36/S23"), "names the HighLife law: {out}");
    assert!(
        out.contains("from branch 0 at tick 2"),
        "names the fork: {out}"
    );
}

#[test]
fn why_walks_a_state_back_through_law_and_fork() {
    let (ok, out) = run(&["lineage", "why", FIXTURE, TIP]);
    assert!(ok, "why succeeds: {out}");
    assert!(out.contains("branch 1, tick 4"), "names the state: {out}");
    // The two compressed runs and the crossed fork.
    assert!(
        out.contains("ticks 3..4 on branch 1 under B36/S23"),
        "{out}"
    );
    assert!(out.contains("ticks 0..2 on main under B3/S23"), "{out}");
    assert!(
        out.contains("crossed fork from branch 0 at tick 2"),
        "{out}"
    );
}

#[test]
fn why_accepts_a_truncated_hash_prefix() {
    let (ok, out) = run(&["lineage", "why", FIXTURE, TIP_PREFIX]);
    assert!(ok, "a page-copied prefix resolves: {out}");
    assert!(out.contains("branch 1, tick 4"), "{out}");
}

#[test]
fn verify_reports_structural_only() {
    let (ok, out) = run(&["lineage", "verify", FIXTURE]);
    assert!(ok, "structural verify exits 0: {out}");
    assert!(
        out.contains("verify structurally") && out.contains("re-derivation is not implemented"),
        "verify is explicit about being structural: {out}"
    );
    assert!(out.contains("2 law(s), 7 state(s), 1 fork(s)"), "{out}");
}
