//! Persisted query-fact regressions: deterministic graph bytes, previous vs
//! current cutoff explanations, offline explanation after source deletion,
//! malformed and version-mismatched ledger rejection, and completion-order
//! independence of the serialized facts.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{SystemTime, UNIX_EPOCH};

use prism::default_roots;
use prism::lineage::{
    FactGraph, FactInput, FactLedger, FactOutcome, FactRecorder, FactScope, QueryFact, QueryKind,
    FACT_DECISION_KIND,
};
use prism::store::disk::Store;

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let mut path = std::env::temp_dir();
        path.push(format!("prism-facts-{tag}-{}-{nanos}-{n}", process::id()));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn why_recompiled(source: &Path, store: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(["lineage", "why-recompiled"])
        .arg(source)
        .env("PRISM_STORE_PATH", store)
        .env("PRISM_COMPILER_CACHE", "1")
        .env_remove("PRISM_STORE")
        .output()
        .expect("runs prism lineage why-recompiled")
}

fn stdout_of(output: &Output) -> String {
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn sample_fact(kind: QueryKind, identity: &str, source: &str) -> QueryFact {
    QueryFact {
        kind,
        identity: identity.to_string(),
        inputs: vec![
            FactInput {
                name: "compiler".to_string(),
                identity: "c0".to_string(),
            },
            FactInput {
                name: "source".to_string(),
                identity: source.to_string(),
            },
        ],
        output: Some(format!("out-{source}")),
        outcome: FactOutcome::Write,
        reasons: vec!["input `source` changed".to_string()],
    }
}

// A spread over the shared fact type's whole kind family: every explanation
// kind serializes through the identical model.
fn kind_family_facts() -> Vec<QueryFact> {
    [
        (QueryKind::Module, "<root>"),
        (QueryKind::Module, "Greet"),
        (QueryKind::Optimizer, "scc-main"),
        (QueryKind::Effect, "whole-program"),
        (QueryKind::BackendScc, "main"),
        (QueryKind::ClosurePlan, "closure-adapters"),
        (QueryKind::Object, "main.o"),
        (QueryKind::Link, "app"),
    ]
    .into_iter()
    .map(|(kind, identity)| sample_fact(kind, identity, "s1"))
    .collect()
}

fn ledger_bytes(store: &Store, scope: &FactScope) -> Vec<u8> {
    store
        .get_decision(FACT_DECISION_KIND, scope.locator())
        .unwrap()
        .expect("a recorded ledger")
}

#[test]
fn fact_graph_bytes_are_deterministic_over_repeated_runs() {
    let tmp = TempDir::new("determinism");
    let scope = FactScope::of_roots(&default_roots(&tmp.path));
    let facts = kind_family_facts();

    let graph_once = FactGraph::new(facts.clone()).to_json_string().unwrap();
    let graph_twice = FactGraph::new(facts.clone()).to_json_string().unwrap();
    assert_eq!(graph_once, graph_twice);

    let store_a = Store::open_or_create(tmp.path.join("a")).unwrap();
    let store_b = Store::open_or_create(tmp.path.join("b")).unwrap();
    let recorder_a = FactRecorder::new();
    for fact in &facts {
        recorder_a.record(fact.clone());
    }
    recorder_a.commit(&store_a, &scope).unwrap();
    let recorder_b = FactRecorder::new();
    for fact in facts.iter().rev() {
        recorder_b.record(fact.clone());
    }
    recorder_b.commit(&store_b, &scope).unwrap();
    assert_eq!(
        ledger_bytes(&store_a, &scope),
        ledger_bytes(&store_b, &scope),
        "identical fact sets must persist byte-identically"
    );

    // A repeated identical run rotates previous == current and stays stable.
    for store in [&store_a, &store_b] {
        let recorder = FactRecorder::new();
        for fact in &facts {
            recorder.record(fact.clone());
        }
        recorder.commit(store, &scope).unwrap();
    }
    assert_eq!(
        ledger_bytes(&store_a, &scope),
        ledger_bytes(&store_b, &scope)
    );
    let ledger = FactLedger::load(&store_a, &scope).unwrap();
    assert_eq!(ledger.previous, ledger.current);
}

#[test]
fn module_cutoff_is_explained_from_previous_and_current_graphs() {
    let tmp = TempDir::new("cutoff");
    let store_path = tmp.path.join("store");
    let main = tmp.path.join("main.pr");
    let greet = tmp.path.join("Greet.pr");
    fs::write(&main, "import Greet\n\nfn main() : Int = Greet.greet(41)\n").unwrap();
    fs::write(&greet, "pub fn greet(x : Int) : Int = x + 1\n").unwrap();

    let first = stdout_of(&why_recompiled(&main, &store_path));
    assert!(
        first.contains("recompiled Greet: no previous successful module query"),
        "first build has no previous fact: {first}"
    );
    assert!(first.contains("recompiled <root>: no previous successful module query"));

    // A body-only edit: the tokens move, the public interface digest does not.
    fs::write(&greet, "pub fn greet(x : Int) : Int = x + 2\n").unwrap();
    let second = stdout_of(&why_recompiled(&main, &store_path));
    assert!(
        second.contains(
            "recompiled Greet: module tokens changed; public interface remained unchanged"
        ),
        "cutoff must name the token change and the held interface: {second}"
    );
    assert!(
        second.contains("reused <root>"),
        "an unchanged importer must be reused across the cutoff: {second}"
    );

    // The persisted graphs agree: the previous and current Greet facts differ
    // in their source inputs while the output identity held, so the recorded
    // outcome is a cutoff.
    let store = Store::open_or_create(&store_path).unwrap();
    let scope = FactScope::of_roots(&default_roots(&tmp.path));
    let ledger = FactLedger::load(&store, &scope).unwrap();
    let current = ledger
        .current
        .get(QueryKind::Module, "Greet")
        .expect("a current Greet fact");
    let previous = ledger
        .previous
        .get(QueryKind::Module, "Greet")
        .expect("a previous Greet fact");
    assert_eq!(current.outcome, FactOutcome::Cutoff);
    assert_eq!(current.output, previous.output);
    assert_ne!(current.inputs, previous.inputs);
}

#[test]
fn offline_explanation_survives_source_deletion() {
    let tmp = TempDir::new("offline");
    let store_path = tmp.path.join("store");
    let main = tmp.path.join("main.pr");
    fs::write(&main, "fn main() : Int = 42\n").unwrap();

    stdout_of(&why_recompiled(&main, &store_path));
    let warm = stdout_of(&why_recompiled(&main, &store_path));
    assert!(warm.contains("reused <root>"), "second run reuses: {warm}");

    fs::remove_file(&main).unwrap();
    let offline = stdout_of(&why_recompiled(&main, &store_path));
    assert!(
        offline.contains("reused <root>"),
        "persisted facts must explain the last run without sources: {offline}"
    );
}

#[test]
fn malformed_and_version_mismatched_ledgers_are_rejected() {
    let tmp = TempDir::new("malformed");
    let store_path = tmp.path.join("store");
    let main = tmp.path.join("main.pr");
    fs::write(&main, "fn main() : Int = 42\n").unwrap();
    stdout_of(&why_recompiled(&main, &store_path));

    let store = Store::open_or_create(&store_path).unwrap();
    let scope = FactScope::of_roots(&default_roots(&tmp.path));

    // Well-formed decisions envelope, unreadable document.
    store
        .put_decision(FACT_DECISION_KIND, scope.locator(), b"not json")
        .unwrap();
    let err = FactLedger::load(&store, &scope).unwrap_err().to_string();
    assert!(
        err.contains("malformed"),
        "malformed body is refused: {err}"
    );
    let rejected = why_recompiled(&main, &store_path);
    assert!(
        !rejected.status.success(),
        "a malformed ledger must fail the command, not be misread"
    );

    // Well-formed document of a version this reader does not speak.
    store
        .put_decision(
            FACT_DECISION_KIND,
            scope.locator(),
            br#"{"format":"prism-query-fact-ledger-v0","previous":[],"current":[]}"#,
        )
        .unwrap();
    let err = FactLedger::load(&store, &scope).unwrap_err().to_string();
    assert!(
        err.contains("prism-query-fact-ledger-v0"),
        "a foreign version is named, never misread: {err}"
    );
    assert!(!why_recompiled(&main, &store_path).status.success());

    // A wrong decisions-layer header line is refused below the document level.
    let record = find_file_named(&store_path, scope.locator()).expect("a persisted ledger file");
    fs::write(&record, b"prism-query-decision-v9\n{}").unwrap();
    assert!(FactLedger::load(&store, &scope).is_err());
    assert!(!why_recompiled(&main, &store_path).status.success());
}

fn find_file_named(root: &Path, name: &str) -> Option<PathBuf> {
    for entry in fs::read_dir(root).ok()? {
        let path = entry.ok()?.path();
        if path.is_dir() {
            if let Some(found) = find_file_named(&path, name) {
                return Some(found);
            }
        } else if path.file_name().is_some_and(|file| file == name) {
            return Some(path);
        }
    }
    None
}

#[test]
fn parallel_completion_order_keeps_stable_bytes() {
    let tmp = TempDir::new("parallel");
    let scope = FactScope::of_roots(&default_roots(&tmp.path));
    let facts = kind_family_facts();

    let reference = Store::open_or_create(tmp.path.join("reference")).unwrap();
    let recorder = FactRecorder::new();
    for fact in &facts {
        recorder.record(fact.clone());
    }
    recorder.commit(&reference, &scope).unwrap();
    let expected = ledger_bytes(&reference, &scope);

    for round in 0..4 {
        let store = Store::open_or_create(tmp.path.join(format!("round-{round}"))).unwrap();
        let recorder = Arc::new(FactRecorder::new());
        let handles: Vec<_> = facts
            .chunks(2)
            .map(|chunk| {
                let recorder = Arc::clone(&recorder);
                let chunk = chunk.to_vec();
                thread::spawn(move || {
                    for fact in chunk.into_iter().rev() {
                        recorder.record(fact);
                    }
                })
            })
            .collect();
        for handle in handles {
            handle.join().unwrap();
        }
        recorder.commit(&store, &scope).unwrap();
        assert_eq!(
            ledger_bytes(&store, &scope),
            expected,
            "completion order must not reach the serialized facts"
        );
    }
}
