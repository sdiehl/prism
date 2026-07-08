//! Build-lineage sidecar regressions.
//!
//! The non-trivial Prism programs live under `tests/projects/lineage*`; the test
//! copies those fixtures into temp dirs rather than embedding source strings in
//! the Rust case body.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

use prism::core::HASH_SCHEME;
use prism::lineage::{
    read_lineage, verify, write_sidecar, BuildLineage, BuildLineageInput, BuildRequest,
    LineageArtifact, LineageGraph, Node, NodeId, NodeKind, Variant, LINEAGE_GRAPH_FORMAT,
};
use prism::resolve::SourceBundleIdentity;
use prism::{Config, Root};

const TRIVIAL_SOURCE: &str = "fn main() = ()\n";

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
        path.push(format!("prism-lineage-{tag}-{}-{nanos}-{n}", process::id()));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("projects")
        .join(name)
}

fn copy_dir(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).unwrap();
    for entry in fs::read_dir(src).unwrap() {
        let entry = entry.unwrap();
        let from = entry.path();
        let to = dst.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&from, &to);
        } else {
            fs::copy(&from, &to).unwrap();
        }
    }
}

fn build(project: &Path) -> Value {
    let prism = env!("CARGO_BIN_EXE_prism");
    let output = Command::new(prism)
        .arg("build")
        .arg(project)
        .env_remove("PRISM_STORE")
        .output()
        .expect("runs prism build");
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = fs::read_to_string(project.join("target").join("lineage.plineage")).unwrap();
    serde_json::from_str(&text).unwrap()
}

const fn prism_bin() -> &'static str {
    env!("CARGO_BIN_EXE_prism")
}

// The id of the single node of `kind` in a serialized graph.
fn node_id(graph: &Value, kind: &str) -> String {
    graph["nodes"]
        .as_array()
        .expect("nodes array")
        .iter()
        .find(|node| node["kind"].as_str() == Some(kind))
        .and_then(|node| node["id"].as_str())
        .unwrap_or_else(|| panic!("no {kind} node"))
        .to_string()
}

#[test]
fn project_build_writes_stable_graph_and_source_changes_move_source_root() {
    let tmp = TempDir::new("project");
    let project = tmp.path.join("lineage");
    copy_dir(&fixture("lineage"), &project);

    let first = build(&project);
    let second = build(&project);
    assert_eq!(first, second, "same inputs must produce identical lineage");
    assert_eq!(first["format"].as_str(), Some("prism-lineage-graph-v1"));
    assert_eq!(first["variant"].as_str(), Some("build"));

    let artifact = project.join("target").join("lineage");
    let json = Command::new(prism_bin())
        .arg("lineage")
        .arg("show")
        .arg(&artifact)
        .arg("--json")
        .output()
        .expect("runs prism lineage show --json");
    assert!(json.status.success());
    let read_back: Value = serde_json::from_slice(&json.stdout).unwrap();
    assert_eq!(
        read_back, first,
        "`lineage show --json` must echo the sidecar graph"
    );

    let human = Command::new(prism_bin())
        .arg("lineage")
        .arg("show")
        .arg(&artifact)
        .output()
        .expect("runs prism lineage show");
    assert!(human.status.success());
    assert!(
        String::from_utf8_lossy(&human.stdout).contains("why: artifact exists because"),
        "human lineage should explain why the artifact exists"
    );

    let verified = Command::new(prism_bin())
        .arg("lineage")
        .arg("verify")
        .arg(&artifact)
        .output()
        .expect("runs prism lineage verify");
    assert!(
        verified.status.success(),
        "a fresh build must verify: {}",
        String::from_utf8_lossy(&verified.stderr)
    );

    fs::copy(
        fixture("lineage_changed").join("src").join("Greet.pr"),
        project.join("src").join("Greet.pr"),
    )
    .unwrap();
    let changed = build(&project);
    assert_ne!(
        node_id(&first, "source-root"),
        node_id(&changed, "source-root"),
        "source edit must move the source-root node id"
    );
    assert_eq!(
        node_id(&first, "stdlib-root"),
        node_id(&changed, "stdlib-root"),
        "source edit must not move the stdlib-root node id"
    );
}

#[test]
fn changed_artifact_byte_fails_verification_and_names_the_artifact() {
    let tmp = TempDir::new("verify");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"artifact bytes").unwrap();

    let lineage = sample_lineage("std", "pkg", &artifact);
    let sidecar = write_sidecar(&artifact, &lineage).unwrap();
    let graph = read_lineage(&sidecar).unwrap();
    assert_eq!(
        verify(&graph, tmp.path.as_path()).unwrap().checked,
        1,
        "the recorded artifact must verify before tampering"
    );

    fs::write(&artifact, b"artifact bytez").unwrap();
    let err = verify(&graph, tmp.path.as_path()).unwrap_err().to_string();
    assert!(err.contains("artifact"), "error names the artifact: {err}");
    assert!(err.contains("changed"), "error reports a mismatch: {err}");
}

#[test]
fn missing_artifact_is_a_distinct_verification_error() {
    let tmp = TempDir::new("missing");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"present at record time").unwrap();
    let lineage = sample_lineage("std", "pkg", &artifact);
    let sidecar = write_sidecar(&artifact, &lineage).unwrap();
    let graph = read_lineage(&sidecar).unwrap();

    fs::remove_file(&artifact).unwrap();
    let err = verify(&graph, tmp.path.as_path()).unwrap_err().to_string();
    assert!(err.contains("missing"), "missing file is distinct: {err}");
}

#[test]
fn artifact_verification_preserves_recorded_subdirectories() {
    let tmp = TempDir::new("artifact-subdir");
    fs::write(tmp.path.join("out"), b"artifact bytes").unwrap();
    let digest = blake3::hash(b"artifact bytes").to_hex().to_string();
    let graph = LineageGraph {
        format: LINEAGE_GRAPH_FORMAT.to_string(),
        variant: Variant::Build,
        nodes: vec![Node {
            id: NodeId(format!("blake3:{digest}")),
            kind: NodeKind::Artifact(LineageArtifact {
                kind: "native-binary".to_string(),
                path: "a/out".to_string(),
                digest_scheme: "blake3".to_string(),
                digest,
                bytes: b"artifact bytes".len() as u64,
            }),
        }],
        edges: Vec::new(),
    };

    let err = verify(&graph, tmp.path.as_path()).unwrap_err().to_string();
    assert!(
        err.contains("missing"),
        "must not verify by basename: {err}"
    );

    fs::create_dir_all(tmp.path.join("a")).unwrap();
    fs::write(tmp.path.join("a").join("out"), b"artifact bytes").unwrap();
    assert_eq!(verify(&graph, tmp.path.as_path()).unwrap().checked, 1);
}

#[test]
fn v1_adapter_round_trips_to_the_same_graph() {
    let tmp = TempDir::new("adapter");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"adapter bytes").unwrap();
    let lineage = sample_lineage("std", "pkg", &artifact);

    let v1 = lineage.to_json();
    assert_eq!(v1["format"].as_str(), Some("prism-build-lineage-v1"));
    let lifted = LineageGraph::from_v1(&v1).unwrap();
    assert_eq!(
        lifted,
        lineage.to_graph(),
        "an old sidecar must lift to the graph a fresh build emits"
    );
}

#[test]
fn graph_serialization_is_byte_deterministic() {
    let tmp = TempDir::new("determinism");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"deterministic bytes").unwrap();
    let lineage = sample_lineage("std", "pkg", &artifact);

    let once = lineage.to_graph().to_json_string().unwrap();
    let twice = lineage.to_graph().to_json_string().unwrap();
    assert_eq!(once, twice, "identical inputs must serialize byte-for-byte");
}

#[test]
fn std_and_package_roots_are_explicit_graph_nodes() {
    let tmp = TempDir::new("roots");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"artifact").unwrap();

    let graph_a =
        serde_json::to_value(sample_lineage("std-a", "pkg-a", &artifact).to_graph()).unwrap();
    let graph_b =
        serde_json::to_value(sample_lineage("std-b", "pkg-b", &artifact).to_graph()).unwrap();

    assert_ne!(
        node_id(&graph_a, "stdlib-root"),
        node_id(&graph_b, "stdlib-root"),
        "a different Std root must move the stdlib-root node id"
    );
    assert_ne!(
        node_id(&graph_a, "package-root"),
        node_id(&graph_b, "package-root"),
        "a different package root must move the package-root node id"
    );
}

fn sample_lineage(std_root: &str, package_root: &str, artifact: &Path) -> BuildLineage {
    let roots = lineage_roots(std_root, package_root);
    let cfg = Config::default();
    BuildLineage::collect(BuildLineageInput {
        request: BuildRequest::project(Path::new("prism.toml"), Path::new("src/main.pr")),
        source: TRIVIAL_SOURCE,
        roots: &roots,
        cfg: &cfg,
        backend: "llvm",
        artifacts: vec![("native-binary", artifact.to_path_buf())],
        cache: None,
        diagnostics: Vec::new(),
    })
    .unwrap()
}

fn lineage_roots(std_root: &str, package_root: &str) -> Vec<Root> {
    vec![
        Root::identified_source_bundle(
            "<package StorePkg>".to_string(),
            SourceBundleIdentity::package("StorePkg", HASH_SCHEME, package_root),
            BTreeMap::new(),
        ),
        Root::identified_source_bundle(
            "<stdlib>".to_string(),
            SourceBundleIdentity::stdlib(HASH_SCHEME, std_root),
            BTreeMap::new(),
        ),
    ]
}
