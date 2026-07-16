use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::patch::SurfaceTerm;
use prism::{BehaviorCase, BehaviorCorpus};
use serde_json::Value;

const SOURCE: &str = "fn patch_leaf(x : Int) : Int = x + 1\n\nfn main() = println(patch_leaf(4))\n";
const REPLACEMENT: &str = "fn patch_leaf(x : Int) : Int = x + 2\n";

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let count = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |duration| duration.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "prism-patch-{tag}-{}-{nanos}-{count}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run(store: &Path, args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(args)
        .env("PRISM_STORE_PATH", store)
        .output()
        .unwrap()
}

fn success_json(output: &std::process::Output) -> Value {
    assert!(
        output.status.success(),
        "stderr:\n{}\nstdout:\n{}",
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn cli_fetch_apply_commit_is_atomic_and_reproducible() {
    let temp = TempDir::new("cli");
    let source = temp.path.join("main.pr");
    let replacement = temp.path.join("replacement.pr");
    let artifact = temp.path.join("patch.json");
    let store = temp.path.join("store");
    fs::write(&source, SOURCE).unwrap();
    fs::write(&replacement, REPLACEMENT).unwrap();

    let fetched = success_json(&run(
        &store,
        &["patch", "fetch", source.to_str().unwrap(), "patch_leaf"],
    ));
    assert_eq!(fetched["format"], "prism-patch-fetch-v1");
    assert_eq!(fetched["rendered"], REPLACEMENT.replace("+ 2", "+ 1"));

    let created = run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    );
    assert!(created.status.success());
    fs::write(&artifact, &created.stdout).unwrap();

    let first = run(
        &store,
        &[
            "patch",
            "apply",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
        ],
    );
    let second = run(
        &store,
        &[
            "patch",
            "apply",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
        ],
    );
    assert!(first.status.success());
    assert_eq!(
        first.stdout, second.stdout,
        "judgment bytes are deterministic"
    );
    let report: Value = serde_json::from_slice(&first.stdout).unwrap();
    assert_eq!(report["tier"]["level"], 2);
    assert_eq!(report["importer_cone"][0]["name"], "main");
    assert_eq!(fs::read_to_string(&source).unwrap(), SOURCE);

    let committed = success_json(&run(&store, &["patch", "commit", source.to_str().unwrap()]));
    assert_eq!(committed["format"], "prism-patch-commit-v1");
    assert!(fs::read_to_string(&source).unwrap().contains("x + 2"));
    let after = success_json(&run(
        &store,
        &["patch", "fetch", source.to_str().unwrap(), "patch_leaf"],
    ));
    assert_eq!(after["core_hash"], report["core_hash_after"]);

    let stale = run(
        &store,
        &[
            "patch",
            "apply",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
        ],
    );
    assert!(!stale.status.success());
    let refusal: Value = serde_json::from_slice(&stale.stdout).unwrap();
    assert_eq!(refusal["format"], "prism-patch-refusal-v1");
    assert_eq!(refusal["code"], "stale-namespace");
}

#[test]
fn behavior_receipt_names_worlds_and_first_divergence() {
    let temp = TempDir::new("behavior");
    let source = temp.path.join("main.pr");
    let replacement = temp.path.join("replacement.pr");
    let artifact = temp.path.join("patch.json");
    let corpus = temp.path.join("corpus.json");
    let store = temp.path.join("store");
    fs::write(&source, SOURCE).unwrap();
    fs::write(&replacement, REPLACEMENT).unwrap();
    fs::write(
        &corpus,
        serde_json::to_vec(&serde_json::json!({
            "format": "prism-patch-behavior-corpus-v1",
            "cases": [{"name": "default", "stdin": "", "args": []}]
        }))
        .unwrap(),
    )
    .unwrap();
    let created = success_json(&run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    ));
    fs::write(&artifact, serde_json::to_vec(&created).unwrap()).unwrap();
    let receipt = success_json(&run(
        &store,
        &[
            "patch",
            "behavior",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
            corpus.to_str().unwrap(),
        ],
    ));
    assert_eq!(receipt["format"], "prism-patch-behavior-v1");
    assert_eq!(receipt["relation"], "behavior-changing");
    assert_eq!(receipt["cases"][0]["name"], "default");
    assert_ne!(
        receipt["cases"][0]["before_trace"],
        receipt["cases"][0]["after_trace"]
    );
    assert_eq!(receipt["first_divergence"]["case"], "default");
    assert_eq!(receipt["first_divergence"]["index"], 0);
    assert_eq!(receipt["base_namespace"], created["base_namespace"]);
    assert_ne!(
        receipt["base_namespace"]["digest"],
        receipt["result_namespace"]["digest"]
    );
}

#[test]
fn behavior_receipt_accepts_equivalence_and_refuses_ambient_host_inputs() {
    let temp = TempDir::new("behavior-boundaries");
    let source = temp.path.join("main.pr");
    let replacement = temp.path.join("replacement.pr");
    let artifact = temp.path.join("patch.json");
    let corpus = temp.path.join("corpus.json");
    let store = temp.path.join("store");
    fs::write(&source, SOURCE).unwrap();
    fs::write(&replacement, "fn patch_leaf(y : Int) : Int = y + 1\n").unwrap();
    fs::write(
        &corpus,
        serde_json::to_vec(&serde_json::json!({
            "format": "prism-patch-behavior-corpus-v1",
            "cases": [{"name": "default"}]
        }))
        .unwrap(),
    )
    .unwrap();
    let created = success_json(&run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    ));
    fs::write(&artifact, serde_json::to_vec(&created).unwrap()).unwrap();
    let receipt = success_json(&run(
        &store,
        &[
            "patch",
            "behavior",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
            corpus.to_str().unwrap(),
        ],
    ));
    assert_eq!(receipt["relation"], "equivalent-on-corpus");
    assert!(receipt["first_divergence"].is_null());

    let output_path = temp.path.join("must-not-exist.txt");
    let ambient_source = format!(
        "fn patch_leaf(x : Int) : Int = x + 1\n\nfn main() =\n  write_file(\"{}\", \"bad\")\n  println(patch_leaf(4))\n",
        output_path.display()
    );
    fs::write(&source, ambient_source).unwrap();
    let ambient_created = success_json(&run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    ));
    fs::write(&artifact, serde_json::to_vec(&ambient_created).unwrap()).unwrap();
    let refused = run(
        &store,
        &[
            "patch",
            "behavior",
            source.to_str().unwrap(),
            artifact.to_str().unwrap(),
            corpus.to_str().unwrap(),
        ],
    );
    assert!(!refused.status.success());
    let refusal: Value = serde_json::from_slice(&refused.stdout).unwrap();
    assert_eq!(refusal["code"], "ambient-behavior-input");
    assert!(!output_path.exists());
}

#[test]
fn unrelated_world_move_refuses_a_definition_fresh_patch() {
    let temp = TempDir::new("world-stale");
    let source = temp.path.join("main.pr");
    let replacement = temp.path.join("replacement.pr");
    let artifact = temp.path.join("patch.json");
    let store = temp.path.join("store");
    fs::write(&source, SOURCE).unwrap();
    fs::write(&replacement, REPLACEMENT).unwrap();
    let created = success_json(&run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    ));
    fs::write(&artifact, serde_json::to_vec(&created).unwrap()).unwrap();
    let moved = SOURCE.replace("println(patch_leaf(4))", "println(patch_leaf(5))");
    fs::write(&source, moved).unwrap();
    let args = [
        "patch",
        "apply",
        source.to_str().unwrap(),
        artifact.to_str().unwrap(),
    ];
    let output = run(&store, &args);
    let repeated = run(&store, &args);
    assert!(!output.status.success());
    assert_eq!(output.stdout, repeated.stdout);
    let refusal: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(refusal["code"], "stale-namespace");
    assert_eq!(refusal["patch"], created["digest"]);
    assert_eq!(refusal["base_namespace"], created["base_namespace"]);
    assert_eq!(refusal["digest"].as_str().unwrap().len(), 64);
}

#[test]
fn stdio_payloads_equal_cli_payloads() {
    let temp = TempDir::new("stdio");
    let source = temp.path.join("main.pr");
    let replacement = temp.path.join("replacement.pr");
    let artifact_file = temp.path.join("patch.json");
    let corpus_file = temp.path.join("corpus.json");
    let store = temp.path.join("store");
    fs::write(&source, SOURCE).unwrap();
    fs::write(&replacement, REPLACEMENT).unwrap();
    let corpus = BehaviorCorpus::new(vec![BehaviorCase {
        name: "default".to_string(),
        stdin: String::new(),
        args: Vec::new(),
    }])
    .unwrap();
    fs::write(&corpus_file, serde_json::to_vec(&corpus).unwrap()).unwrap();

    let cli_fetch = success_json(&run(
        &store,
        &["patch", "fetch", source.to_str().unwrap(), "patch_leaf"],
    ));
    let cli_impact = success_json(&run(
        &store,
        &["patch", "impact", source.to_str().unwrap(), "patch_leaf"],
    ));
    let cli_create = success_json(&run(
        &store,
        &[
            "patch",
            "create",
            source.to_str().unwrap(),
            "patch_leaf",
            replacement.to_str().unwrap(),
        ],
    ));
    fs::write(&artifact_file, serde_json::to_vec(&cli_create).unwrap()).unwrap();
    let cli_submit = success_json(&run(
        &store,
        &[
            "patch",
            "submit",
            source.to_str().unwrap(),
            artifact_file.to_str().unwrap(),
        ],
    ));
    let cli_behavior = success_json(&run(
        &store,
        &[
            "patch",
            "behavior",
            source.to_str().unwrap(),
            artifact_file.to_str().unwrap(),
            corpus_file.to_str().unwrap(),
        ],
    ));
    let cli_discard = success_json(&run(
        &store,
        &["patch", "discard", source.to_str().unwrap()],
    ));
    let repeated_submit = success_json(&run(
        &store,
        &[
            "patch",
            "submit",
            source.to_str().unwrap(),
            artifact_file.to_str().unwrap(),
        ],
    ));
    assert_eq!(repeated_submit, cli_submit);
    let cli_commit = success_json(&run(&store, &["patch", "commit", source.to_str().unwrap()]));
    fs::write(&source, SOURCE).unwrap();

    let mut child = Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(["patch", "serve", source.to_str().unwrap()])
        .env("PRISM_STORE_PATH", &store)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let requests = [
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 1,
            "verb": "fetch",
            "target": "patch_leaf",
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 2,
            "verb": "impact",
            "target": "patch_leaf",
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 3,
            "verb": "create",
            "target": "patch_leaf",
            "replacement": REPLACEMENT,
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 4,
            "verb": "submit",
            "patch": cli_create,
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 5,
            "verb": "behavior",
            "patch": cli_create,
            "corpus": corpus,
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 6,
            "verb": "discard",
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 7,
            "verb": "submit",
            "patch": cli_create,
        }),
        serde_json::json!({
            "protocol": "prism-patch-protocol-v1",
            "id": 8,
            "verb": "commit",
        }),
    ];
    let input = child.stdin.as_mut().unwrap();
    for request in requests {
        serde_json::to_writer(&mut *input, &request).unwrap();
        input.write_all(b"\n").unwrap();
    }
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let responses = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(responses.len(), 8);
    assert!(responses.iter().all(|response| response["ok"] == true));
    assert_eq!(responses[0]["payload"], cli_fetch);
    assert_eq!(responses[1]["payload"], cli_impact);
    assert_eq!(responses[2]["payload"], cli_create);
    assert_eq!(responses[3]["payload"], cli_submit);
    assert_eq!(responses[4]["payload"], cli_behavior);
    assert_eq!(responses[5]["payload"], cli_discard);
    assert_eq!(responses[6]["payload"], cli_submit);
    assert_eq!(responses[7]["payload"], cli_commit);
}

fn repository_prism_sources(root: &Path, out: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(root)
        .unwrap_or_else(|error| panic!("{}: {error}", root.display()))
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if name.starts_with('.') || matches!(name, "target" | "node_modules" | "dist" | "pkg") {
                continue;
            }
            repository_prism_sources(&path, out);
        } else if path.extension().is_some_and(|extension| extension == "pr") {
            out.push(path);
        }
    }
}

#[test]
fn term_round_trip_law_holds_over_valid_source_corpus() {
    let mut paths = Vec::new();
    repository_prism_sources(Path::new("."), &mut paths);
    assert!(!paths.is_empty(), "repository Prism corpus is empty");
    for path in paths {
        let source = fs::read_to_string(&path).unwrap();
        let Ok(_) = prism::parse::parse(&source) else {
            continue;
        };
        let terms = prism::patch::extract_terms(&source)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        for term in terms {
            let name = term.name.clone();
            let rendered = term.render().unwrap_or_else(|error| {
                panic!("{}:{name}: {error}", path.display());
            });
            let encoded = SurfaceTerm::from_source(&rendered).unwrap();
            assert_eq!(term, encoded, "{}:{name}", path.display());
        }
    }
}
