//! The gauntlet's cost ledger, joined against the workflows it describes.
//!
//! A ledger that is read but never joined records what the suite looked like on
//! the day it was written. Both sides here are live: the job set comes out of
//! the workflow files at run time and the arm is derived from each workflow's
//! own triggers, so a job added, renamed, retired, or moved between arms fails
//! the join instead of leaving a row that still reads plausibly. The budget half
//! is checked against the numbers the ledger itself carries, which means the
//! file cannot record a figure over the cap and call it within one.
//!
//! What this cannot check is that a recorded timing is still true; that half
//! carries its provenance in the ledger's header and is refreshed by hand.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

/// The ledger, relative to the repository root.
const LEDGER: &str = "tests/lane_ledger.txt";
/// Every workflow the forge runs; the job set is read from all of them, so a new
/// workflow is covered the moment it exists.
const WORKFLOW_DIR: &str = ".github/workflows";
const WORKFLOW_EXT: &str = "yml";
/// Wall clock a single job cell may take on the per-change arm. A change's
/// latency is its slowest cell rather than the sum, so the cap is per cell.
const BUDGET_SECONDS: u64 = 2700;
/// The workflow column of a lane that is declared but not yet built.
const PLANNED_WORKFLOW: &str = "-";
const FIELDS: usize = 6;

/// When a job runs, derived from its workflow's triggers rather than declared.
const ARM_PER_CHANGE: &str = "per-change";
const ARM_PATH_GATED: &str = "path-gated";
const ARM_POST_MERGE: &str = "post-merge";
const ARM_NIGHTLY: &str = "nightly";
const ARM_RELEASE: &str = "release";
const ARMS: &[&str] = &[
    ARM_PER_CHANGE,
    ARM_PATH_GATED,
    ARM_POST_MERGE,
    ARM_NIGHTLY,
    ARM_RELEASE,
];

/// How a row stands against the budget.
const VERDICT_WITHIN: &str = "within";
const VERDICT_OVER: &str = "over-budget";
const VERDICT_UNBUDGETED: &str = "unbudgeted";
const VERDICT_PLANNED: &str = "planned";

/// Triggers, as they are spelled in a workflow's `on:` block.
const ON_KEY: &str = "on";
const JOBS_KEY: &str = "jobs";
const TRIGGER_PULL_REQUEST: &str = "pull_request";
const TRIGGER_PUSH: &str = "push";
const TRIGGER_SCHEDULE: &str = "schedule";
const TRIGGER_RELEASE: &str = "release";
const FILTER_PATHS: &str = "paths";
const FILTER_TAGS: &str = "tags";
/// A mapping key sits two spaces in under its top-level parent.
const NESTED_INDENT: usize = 2;

struct Row {
    workflow: String,
    job: String,
    arm: String,
    cells: u64,
    seconds: u64,
    verdict: String,
}

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn rows() -> Vec<Row> {
    let path = repo_root().join(LEDGER);
    let text =
        fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    text.lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with('#'))
        .map(|line| {
            let field: Vec<&str> = line.split('\t').collect();
            assert_eq!(field.len(), FIELDS, "{LEDGER}: malformed row `{line}`");
            Row {
                workflow: field[0].to_string(),
                job: field[1].to_string(),
                arm: field[2].to_string(),
                cells: field[3].parse().expect("cell count"),
                seconds: field[4].parse().expect("slowest cell seconds"),
                verdict: field[5].to_string(),
            }
        })
        .collect()
}

/// The lines of the top-level block introduced by `key`, comments dropped.
fn block<'a>(text: &'a str, key: &str) -> Vec<&'a str> {
    let opener = format!("{key}:");
    text.lines()
        .skip_while(|line| *line != opener)
        .skip(1)
        .take_while(|line| line.starts_with(' ') || line.trim().is_empty())
        .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .collect()
}

/// The name a mapping key introduces at `indent`, if this line is one. A key
/// carrying its value inline (`tags: ['v*']`) names the same thing as one
/// opening a block, so both forms count.
fn key_at(line: &str, indent: usize) -> Option<&str> {
    let depth = line.len() - line.trim_start().len();
    if depth != indent {
        return None;
    }
    let (name, _) = line.trim().split_once(':')?;
    let named = !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
    named.then_some(name)
}

fn jobs(text: &str) -> BTreeSet<String> {
    block(text, JOBS_KEY)
        .into_iter()
        .filter_map(|line| key_at(line, NESTED_INDENT))
        .map(str::to_string)
        .collect()
}

/// The arm a workflow's triggers put its jobs on. A pull-request trigger gates a
/// change and outranks the rest; a path filter under it narrows the gate to the
/// changes that touch those paths rather than removing it.
fn arm(text: &str) -> &'static str {
    let mut trigger = "";
    let mut filters: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for line in block(text, ON_KEY) {
        if let Some(name) = key_at(line, NESTED_INDENT) {
            trigger = name;
            filters.entry(name).or_default();
        } else if let Some(name) = key_at(line, NESTED_INDENT * 2) {
            filters.entry(trigger).or_default().insert(name);
        }
    }
    let filtered = |name: &str, filter: &str| {
        filters
            .get(name)
            .is_some_and(|under| under.contains(filter))
    };
    if filters.contains_key(TRIGGER_PULL_REQUEST) {
        if filtered(TRIGGER_PULL_REQUEST, FILTER_PATHS) {
            return ARM_PATH_GATED;
        }
        return ARM_PER_CHANGE;
    }
    if filters.contains_key(TRIGGER_SCHEDULE) {
        return ARM_NIGHTLY;
    }
    if filters.contains_key(TRIGGER_RELEASE) || filtered(TRIGGER_PUSH, FILTER_TAGS) {
        return ARM_RELEASE;
    }
    assert!(
        filters.contains_key(TRIGGER_PUSH),
        "a workflow with none of the known triggers has no arm: {filters:?}"
    );
    ARM_POST_MERGE
}

/// Every workflow file, by name, with its text.
fn workflows() -> BTreeMap<String, String> {
    let dir = repo_root().join(WORKFLOW_DIR);
    let mut out = BTreeMap::new();
    for entry in fs::read_dir(&dir).unwrap_or_else(|e| panic!("reading {}: {e}", dir.display())) {
        let path = entry.expect("workflow entry").path();
        if path.extension().is_some_and(|ext| ext == WORKFLOW_EXT) {
            let name = path
                .file_name()
                .expect("workflow file name")
                .to_string_lossy()
                .into_owned();
            out.insert(name, fs::read_to_string(&path).expect("workflow text"));
        }
    }
    assert!(!out.is_empty(), "no workflows under {}", dir.display());
    out
}

fn live_jobs() -> BTreeSet<(String, String)> {
    workflows()
        .into_iter()
        .flat_map(|(name, text)| {
            jobs(&text)
                .into_iter()
                .map(move |job| (name.clone(), job))
                .collect::<Vec<_>>()
        })
        .collect()
}

// A job with no row runs at a cost nobody declared, and a row with no job
// describes a lane that no longer exists. Both are the same failure seen from
// opposite ends, so the join asserts set equality rather than containment.
#[test]
fn every_job_declares_exactly_one_row() {
    let mut declared: BTreeSet<(String, String)> = BTreeSet::new();
    for row in rows().iter().filter(|r| r.verdict != VERDICT_PLANNED) {
        let key = (row.workflow.clone(), row.job.clone());
        assert!(
            declared.insert(key),
            "{LEDGER}: duplicate row for {row_job} in {workflow}",
            row_job = row.job,
            workflow = row.workflow
        );
    }
    assert_eq!(
        declared,
        live_jobs(),
        "the cost ledger and {WORKFLOW_DIR} disagree about which jobs exist: update {LEDGER}"
    );
}

// The arm is a fact about the workflow's triggers, so the ledger states it and
// the workflow decides it. A job promoted from post-merge to per-change without
// its row moving would otherwise keep a budget exemption it no longer has.
#[test]
fn declared_arms_match_the_triggers() {
    let live = workflows();
    for row in rows().iter().filter(|r| r.verdict != VERDICT_PLANNED) {
        let text = live
            .get(&row.workflow)
            .unwrap_or_else(|| panic!("{LEDGER}: no workflow {}", row.workflow));
        assert_eq!(
            row.arm,
            arm(text),
            "{}: {} declares the wrong arm",
            row.workflow,
            row.job
        );
    }
}

// The verdict is a function of the budget and the row's own number, so a lane
// crossing the cap flips a word in a reviewed diff instead of passing quietly.
#[test]
fn verdicts_follow_the_budget() {
    for row in rows().iter().filter(|r| r.verdict != VERDICT_PLANNED) {
        assert!(
            row.cells >= 1 && row.seconds >= 1,
            "{}: {} records no observation",
            row.workflow,
            row.job
        );
        let expected = if row.arm != ARM_PER_CHANGE {
            VERDICT_UNBUDGETED
        } else if row.seconds <= BUDGET_SECONDS {
            VERDICT_WITHIN
        } else {
            VERDICT_OVER
        };
        assert_eq!(
            row.verdict, expected,
            "{}: {} at {}s on the {} arm",
            row.workflow, row.job, row.seconds, row.arm
        );
    }
}

// A planned lane is a declaration, not a description: the moment it runs
// anywhere it owes a workflow, an arm the triggers agree with, and a number.
#[test]
fn planned_lanes_name_no_live_job() {
    let live: BTreeSet<String> = live_jobs().into_iter().map(|(_, job)| job).collect();
    for row in rows().iter().filter(|r| r.verdict == VERDICT_PLANNED) {
        assert_eq!(
            row.workflow, PLANNED_WORKFLOW,
            "{}: planned lanes name no workflow",
            row.job
        );
        assert!(
            !live.contains(&row.job),
            "{}: runs now, so it owes a measured row",
            row.job
        );
        assert!(
            row.cells == 0 && row.seconds == 0,
            "{}: planned lanes carry no observation",
            row.job
        );
    }
}

#[test]
fn every_row_names_a_known_arm() {
    for row in rows() {
        assert!(
            ARMS.contains(&row.arm.as_str()),
            "{}: unknown arm {}",
            row.job,
            row.arm
        );
    }
}
