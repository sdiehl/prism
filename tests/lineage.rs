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
use prism::lineage::{BuildLineage, BuildLineageInput, BuildRequest};
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

#[test]
fn project_build_writes_stable_lineage_and_source_changes_move_source_root() {
    let tmp = TempDir::new("project");
    let project = tmp.path.join("lineage");
    copy_dir(&fixture("lineage"), &project);

    let first = build(&project);
    let second = build(&project);
    assert_eq!(first, second, "same inputs must produce identical lineage");
    let artifact = project.join("target").join("lineage");
    let json = Command::new(prism_bin())
        .arg("lineage")
        .arg(&artifact)
        .arg("--json")
        .output()
        .expect("runs prism lineage --json");
    assert!(json.status.success());
    let read_back: Value = serde_json::from_slice(&json.stdout).unwrap();
    assert_eq!(read_back, first);
    let human = Command::new(prism_bin())
        .arg("lineage")
        .arg(&artifact)
        .output()
        .expect("runs prism lineage");
    assert!(human.status.success());
    assert!(
        String::from_utf8_lossy(&human.stdout).contains("why: artifact exists because"),
        "human lineage should explain why the artifact exists"
    );

    fs::copy(
        fixture("lineage_changed").join("src").join("Greet.pr"),
        project.join("src").join("Greet.pr"),
    )
    .unwrap();
    let changed = build(&project);
    assert_ne!(
        first["inputs"]["source"]["root"], changed["inputs"]["source"]["root"],
        "source edit must move the recorded source root"
    );
    assert_eq!(
        first["inputs"]["stdlib"]["root"], changed["inputs"]["stdlib"]["root"],
        "source edit must not move the recorded Std root"
    );
}

#[test]
fn std_and_package_roots_are_explicit_lineage_fields() {
    let tmp = TempDir::new("roots");
    let artifact = tmp.path.join("artifact");
    fs::write(&artifact, b"artifact").unwrap();

    let roots_a = lineage_roots("std-a", "pkg-a");
    let roots_b = lineage_roots("std-b", "pkg-b");
    let cfg = Config::default();
    let request = BuildRequest::project(Path::new("prism.toml"), Path::new("src/main.pr"));

    let lineage_a = BuildLineage::collect(BuildLineageInput {
        request: request.clone(),
        source: TRIVIAL_SOURCE,
        roots: &roots_a,
        cfg: &cfg,
        backend: "llvm",
        artifacts: vec![("native-binary", artifact.clone())],
        cache: None,
        diagnostics: Vec::new(),
    })
    .unwrap()
    .to_json();
    let lineage_b = BuildLineage::collect(BuildLineageInput {
        request,
        source: TRIVIAL_SOURCE,
        roots: &roots_b,
        cfg: &cfg,
        backend: "llvm",
        artifacts: vec![("native-binary", artifact)],
        cache: None,
        diagnostics: Vec::new(),
    })
    .unwrap()
    .to_json();

    assert_ne!(
        lineage_a["inputs"]["stdlib"]["root"],
        lineage_b["inputs"]["stdlib"]["root"]
    );
    assert_ne!(
        lineage_a["inputs"]["packages"][0]["root"],
        lineage_b["inputs"]["packages"][0]["root"]
    );
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
