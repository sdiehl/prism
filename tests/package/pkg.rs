//! The package manager: manifest forms, the lockfile, and the Merkle-DAG
//! resolver over a real content-addressed store.
//!
//! The manifest and lock formats have their own unit round-trips beside their
//! code; this file is the integration layer, where a multi-definition program is
//! committed to a temp store and the resolver's closure is checked against the
//! dependency graph the commit wrote. It also pins the missing-hash diagnostic
//! (it must name the hash and the edge that wanted it), the `prism pkg why` trace, and
//! the container-reification reservation (the two homes of the
//! representation-affecting class list must agree).

use std::collections::BTreeSet;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::Digest;
use prism::core::HASH_SCHEME;
use prism::flags::SignMode;
use prism::pkg::lock::{Lock, LockEntry};
use prism::pkg::resolve::{resolve_closure, trace, ResolveError};
use prism::pkg::std_source::encode_source_bundle;
use prism::pkg::transport::{DiskTransport, Transport};
use prism::pkg::trust::{serialize_index, IndexRow, SignedArtifact, INDEX_KIND_SOURCE};
use prism::pkg::{package_source_roots, std_pin_status, stdlib_root, StdPin};
use prism::project::{hash_pin, load_project, DepSource, Dependency};
use prism::resolve::{SourceBundleArtifactKind, SourceBundleKind, SourceBundleOrigin};
use prism::store::coherence::is_representation_affecting;
use prism::store::disk::Store;
use prism::{commit_to_store, default_roots, with_custom_prelude, with_prelude, Config, DynFlags};
use serde_json::Value;

// A multi-definition program with a deliberate dependency chain, `pkg_`-prefixed
// to stay clear of the prelude: main -> top -> {mid, leaf}, mid -> leaf.
const PROG: &str = r"fn pkg_leaf(n : Int) : Int = n + 1
fn pkg_mid(n : Int) : Int = pkg_leaf(n) * 2
fn pkg_top(n : Int) : Int =
  let m = pkg_mid(n)
  m + pkg_leaf(n)
fn main() = println(pkg_top(3))
";
const STORE_PKG_NAME: &str = "StorePkg";
const STORE_PKG_SOURCE: &str = "pub fn answer() : Int = 41\n";
const STORE_PKG_ORIGIN: &str = "example.invalid/StorePkg";
const STORE_PKG_OTHER_ORIGIN: &str = "example.invalid/OtherStorePkg";
const STORE_PKG_TAG: &str = "v1";
// The usage-gate golden a package commits at its root (mirrors bin/prism.rs's
// PACKAGE_USAGE_SUMMARY, which the binary crate does not export to tests): the
// markdown projection of the usage summary.
const USAGE_SUMMARY_GOLDEN: &str = "usage-summary.md";

// --- temp store scaffolding ---------------------------------------------

struct TempDir {
    path: PathBuf,
}

#[test]
fn spectra_path_dependencies_include_the_typst_package_transitively() {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let spectra = load_project(&workspace.join("packages/spectra")).expect("loads Spectra");
    let example =
        load_project(&workspace.join("examples/spectra-deck")).expect("loads Spectra example");
    let spectra_src = workspace
        .join("packages/spectra/src")
        .canonicalize()
        .expect("Spectra source path");
    let typst_src = workspace
        .join("packages/typst/src")
        .canonicalize()
        .expect("Typst source path");
    let canonical = |paths: &[PathBuf]| {
        paths
            .iter()
            .map(|path| path.canonicalize().expect("dependency source path"))
            .collect::<Vec<_>>()
    };

    assert_eq!(canonical(&spectra.dep_src_dirs), vec![typst_src.clone()]);
    assert_eq!(
        canonical(&example.dep_src_dirs),
        vec![spectra_src, typst_src]
    );
}

#[test]
fn spectra_facade_checks_with_its_transitive_typst_dependency() {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(workspace.join("examples/spectra-deck"))
        .output()
        .expect("checks Spectra example");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let mut path = std::env::temp_dir();
        path.push(format!(
            "prism-pkg-{tag}-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn root(&self) -> PathBuf {
        self.path.join("store")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn pkg_init_prompts_and_creates_minimal_package() {
    let tmp = TempDir::new("init");
    let mut child = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("init")
        .current_dir(&tmp.path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawns prism pkg init");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(b"demo_pkg\ndemo-dir\n")
        .expect("writes init answers");
    let out = child.wait_with_output().expect("waits for init");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("package name: "), "{stdout}");
    assert!(stdout.contains("directory name: "), "{stdout}");
    assert!(stdout.contains("created package `demo_pkg`"), "{stdout}");

    let project = tmp.path.join("demo-dir");
    assert!(project.join("prism.toml").is_file());
    let main = project.join("src").join("main.pr");
    assert!(main.is_file());
    let manifest = fs::read_to_string(project.join("prism.toml")).unwrap();
    assert!(manifest.contains("name = \"demo_pkg\""));
    assert!(manifest.contains("entry = \"src/main.pr\""));
    assert_eq!(
        fs::read_to_string(&main).unwrap(),
        "fn main() = println(\"Hello World from Prism! Taste the rainbow.\")\n"
    );

    let check = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .current_dir(&project)
        .output()
        .expect("runs prism check");
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );

    let run = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(".")
        .current_dir(&project)
        .output()
        .expect("runs generated package");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout),
        "Hello World from Prism! Taste the rainbow.\n=> ()\n"
    );
}

fn store_cfg(root: PathBuf) -> Config {
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(root);
    cfg.flags.quiet = true;
    cfg
}

// Commit the program to a fresh store and return the store handle. The store's
// own name index is the source of full content hashes (the `core-hash` dump
// abbreviates to a prefix and is not a store key).
fn commit(tmp: &TempDir) -> Store {
    let cfg = store_cfg(tmp.root());
    commit_to_store(&with_prelude(PROG), &default_roots(Path::new(".")), &cfg)
        .expect("commit_to_store");
    Store::open_or_create(tmp.root()).unwrap()
}

// The full content hash a definition is keyed by in the store, read from the
// store's name index (name to full hash), matched on the unqualified tail.
fn hash(store: &Store, name: &str) -> String {
    let found = store
        .names()
        .unwrap()
        .into_iter()
        .find(|(n, _)| n.rsplit(['.', '@']).next() == Some(name));
    match found {
        Some((_, h)) => h,
        None => panic!("no store hash for {name}"),
    }
}

// --- resolver closure correctness ---------------------------------------

#[test]
fn resolver_closure_is_the_transitive_merkle_set() {
    let tmp = TempDir::new("closure");
    let store = commit(&tmp);
    let root = hash(&store, "pkg_top");
    let transport = DiskTransport::open(tmp.root()).unwrap();

    let closure = resolve_closure(&transport, std::slice::from_ref(&root)).expect("resolve");

    // pkg_top pulls in pkg_mid and pkg_leaf transitively; the closure names all
    // three, plus every stdlib definition they reach (arithmetic lives in the
    // prelude). We assert the target names are present rather than an exact set,
    // since the prelude closure is large and not the thing under test.
    for name in ["pkg_top", "pkg_mid", "pkg_leaf"] {
        let h = hash(&store, name);
        assert!(
            closure.hashes.contains(&h),
            "closure is missing {name} ({h})"
        );
    }
    // Every object the closure names is actually present in the store (the walk
    // only admits hashes it could fetch).
    for h in &closure.hashes {
        assert!(store.has(h), "closure names an absent object {h}");
    }
    // The forward edges of pkg_top reach pkg_mid and pkg_leaf directly.
    let top_edges: BTreeSet<&String> = closure.edges[&root].iter().collect();
    assert!(top_edges.contains(&hash(&store, "pkg_mid")));
    assert!(top_edges.contains(&hash(&store, "pkg_leaf")));
}

#[test]
fn a_missing_hash_names_the_hash_and_the_edge_that_wanted_it() {
    // Resolve pkg_top from an empty store: its own object is the missing root, so
    // the error names it with no requesting edge.
    let empty = TempDir::new("missing-root");
    let source = TempDir::new("missing-src");
    let src_store = commit(&source);
    let root = hash(&src_store, "pkg_top");
    let empty_transport = DiskTransport::open(empty.root()).unwrap();

    let err = resolve_closure(&empty_transport, std::slice::from_ref(&root)).unwrap_err();
    match err {
        ResolveError::Missing { hash, wanted_by } => {
            assert_eq!(hash, root);
            assert_eq!(wanted_by, None, "a pinned root has no requesting edge");
        }
        ResolveError::Transport(msg) => panic!("expected Missing, got Transport({msg})"),
    }

    // Now delete a leaf object from a committed store and resolve from the top:
    // the leaf is missing and the error names the edge (a dependent) that pulled
    // it in.
    let tmp = TempDir::new("missing-leaf");
    let store = commit(&tmp);
    let top = hash(&store, "pkg_top");
    let leaf = hash(&store, "pkg_leaf");
    delete_object(&tmp.root(), &leaf);
    // Reopen so the deletion is visible.
    let transport = DiskTransport::open(tmp.root()).unwrap();

    let err = resolve_closure(&transport, &[top]).unwrap_err();
    match err {
        ResolveError::Missing { hash, wanted_by } => {
            assert_eq!(hash, leaf, "the deleted leaf is the missing hash");
            assert!(
                wanted_by.is_some(),
                "a transitive miss must name the edge that wanted it"
            );
        }
        ResolveError::Transport(msg) => panic!("expected Missing, got Transport({msg})"),
    }
}

#[test]
fn why_traces_a_root_to_a_transitive_dependency() {
    let tmp = TempDir::new("why");
    let store = commit(&tmp);
    let root = hash(&store, "pkg_top");
    let transport = DiskTransport::open(tmp.root()).unwrap();
    let closure = resolve_closure(&transport, std::slice::from_ref(&root)).expect("resolve");

    let leaf = hash(&store, "pkg_leaf");
    let chain =
        trace(&closure, std::slice::from_ref(&root), &leaf).expect("leaf is in the closure");
    assert_eq!(chain.first(), Some(&root), "the trace starts at the root");
    assert_eq!(chain.last(), Some(&leaf), "the trace ends at the target");
    // Every step of the chain is a real forward edge.
    for pair in chain.windows(2) {
        assert!(
            closure.edges[&pair[0]].contains(&pair[1]),
            "{} -> {} is not an edge",
            pair[0],
            pair[1]
        );
    }
}

// --- reservation: the two homes of the representation-affecting list ------

#[test]
fn representation_affecting_classes_are_reserved_for_ord_and_hash() {
    // The container docstrings in Data/Map.pr and Data/Set.pr promise a container
    // will carry its canonical Ord/Hash instance hash across assemblies. This is
    // the compiler-side home of that class list; the test fails loudly if the two
    // drift apart.
    assert!(is_representation_affecting("Ord"));
    assert!(is_representation_affecting("Hash"));
    // A representation-neutral class is safe to mix and must stay out of the set.
    assert!(!is_representation_affecting("Show"));
    assert!(!is_representation_affecting("Functor"));
}

// Remove a single anonymous object from the store, so a resolve over it hits a
// genuine local miss. The object path is sharded by the first two hex nibbles,
// mirroring the store's own layout.
fn delete_object(root: &Path, hash: &str) {
    let (shard, rest) = hash.split_at(2);
    let path = root.join("objects").join(shard).join(rest);
    fs::remove_file(&path).expect("object present before deletion");
}

// --- the Std ring: pin the standard-library root and check a build against it --

// The standard library ships as a pinned content-addressed root through the
// store. A lockfile records that root; a later build recomputes the embedded
// stdlib's root and compares. The three outcomes (unpinned, agree, disagree) are
// the whole distribution story the store supports today: a disagreement is named
// exactly, so two programs pinning different Std roots are told apart the same way
// two dependency hashes are, rather than silently coexisting.
#[test]
fn std_root_pins_and_verifies() {
    let root = stdlib_root().expect("embedded stdlib elaborates");
    // A blake3 hex digest: non-empty and stable across two computations.
    assert!(!root.is_empty());
    assert_eq!(root, stdlib_root().unwrap());

    // Unpinned: a lock with no Std line runs against the embedded stdlib.
    let bare = Lock::default();
    assert_eq!(std_pin_status(&bare).unwrap(), StdPin::Unpinned);

    // Pinned against this compiler's stdlib: the build is on the same Std.
    let mut pinned = Lock::default();
    pinned.pin_std(root.clone());
    assert_eq!(std_pin_status(&pinned).unwrap(), StdPin::Match);

    // Pinned against a different Std: the disagreement names both roots.
    let mut stale = Lock::default();
    stale.pin_std("0000000000000000".to_string());
    match std_pin_status(&stale).unwrap() {
        StdPin::Mismatch { pinned, embedded } => {
            assert_eq!(pinned, "0000000000000000");
            assert_eq!(embedded, root);
        }
        other => panic!("expected a mismatch, got {other:?}"),
    }
}

#[test]
fn foreign_std_lock_scheme_is_an_error() {
    let lock = Lock {
        std_root: Some("deadbeef".to_string()),
        std_scheme: Some("future-scheme".to_string()),
        ..Lock::default()
    };

    let err = prism::pkg::std_pin_status(&lock).unwrap_err().to_string();
    assert!(err.contains("Std root"));
    assert!(err.contains("future-scheme"));
}

#[test]
fn stale_std_pin_loads_source_bundle_from_store() {
    let tmp = TempDir::new("std-source");
    let module_src = "pub fn answer() : Int = 42\n";
    let bundle = encode_source_bundle([("StoreOnly", module_src)]);
    let root = blake3::hash(&bundle).to_hex().to_string();
    let store = Store::open_or_create(tmp.root()).unwrap();
    store.put(&root, &bundle).unwrap();

    let mut lock = Lock::default();
    lock.pin_std(root);
    let std_root = prism::pkg::stdlib_source_root(&lock, &tmp.root()).unwrap();
    let roots = prism::project_roots_with_std(Path::new("/no/project/src"), &[], std_root);
    let src = with_custom_prelude("", "import StoreOnly (answer)\nfn main() = answer()\n");

    let checked = prism::check_on(&src, &roots).expect("store-served std module resolves");
    assert!(checked.decls.iter().any(|d| d.name == "main"));
}

#[test]
fn stale_std_pin_rejects_corrupt_store_bytes() {
    let tmp = TempDir::new("std-source-corrupt");
    let bundle = encode_source_bundle([("StoreOnly", "pub fn answer() : Int = 42\n")]);
    let root = blake3::hash(&bundle).to_hex().to_string();
    let store = Store::open_or_create(tmp.root()).unwrap();
    store.put(&root, b"corrupt source bundle").unwrap();

    let mut lock = Lock::default();
    lock.pin_std(root.clone());
    let err = prism::pkg::stdlib_source_root(&lock, &tmp.root())
        .unwrap_err()
        .to_string();

    assert!(err.contains("stdlib source bundle hash mismatch"));
    assert!(err.contains(&root));
}

#[test]
fn project_check_uses_locked_std_source_bundle() {
    let tmp = TempDir::new("std-project");
    let project = tmp.path.join("project");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(
        project.join("prism.toml"),
        r#"[package]
name = "p"
prelude = "src/Prelude.pr"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    fs::write(project.join("src").join("Prelude.pr"), "").unwrap();
    fs::write(
        project.join("src").join("main.pr"),
        "import StoreOnly (answer)\nfn main() = answer()\n",
    )
    .unwrap();

    let module_src = "pub fn answer() : Int = 42\n";
    let bundle = encode_source_bundle([("StoreOnly", module_src)]);
    let root = blake3::hash(&bundle).to_hex().to_string();
    let store = Store::open_or_create(tmp.root()).unwrap();
    store.put(&root, &bundle).unwrap();
    let mut lock = Lock::default();
    lock.pin_std(root);
    fs::write(project.join("prism.lock"), lock.render().unwrap()).unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .output()
        .expect("runs prism check");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.stdout.is_empty(),
        "successful `prism check` should be quiet, stdout:\n{}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(
        out.stderr.is_empty(),
        "successful `prism check` should be quiet, stderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn store_package_bundle(store_root: &Path, module: &str, src: &str) -> String {
    let bundle = encode_source_bundle([(module, src)]);
    let root = blake3::hash(&bundle).to_hex().to_string();
    let store = Store::open_or_create(store_root).unwrap();
    store.put(&root, &bundle).unwrap();
    root
}

fn write_package_project(project: &Path, dep_source: &str) {
    write_named_package_project(project, "app", dep_source);
}

fn write_named_package_project(project: &Path, name: &str, dep_source: &str) {
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(
        project.join("prism.toml"),
        format!(
            r#"[package]
name = "{name}"

[bin]
entry = "src/main.pr"

[dependencies]
StorePkg = {dep_source}
"#
        ),
    )
    .unwrap();
    fs::copy(
        project_fixture("store_pkg_app").join("src").join("main.pr"),
        project.join("src").join("main.pr"),
    )
    .unwrap();
}

fn tzdb_package() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/packages/tzdb"))
}

fn project_fixture(name: &str) -> PathBuf {
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
        if from.is_dir() {
            copy_dir(&from, &to);
        } else {
            fs::copy(&from, &to).unwrap();
        }
    }
}

#[test]
fn run_uses_hash_pinned_package_source_bundle() {
    let tmp = TempDir::new("hash-package");
    let project = tmp.path.join("app");
    let root = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    write_package_project(&project, &format!("{:?}", hash_pin(&root)));

    let mut lock = Lock::default();
    lock.set(LockEntry {
        name: STORE_PKG_NAME.to_string(),
        scheme: HASH_SCHEME.to_string(),
        hash: Digest::from(root.clone()),
        source: DepSource::Hash(root),
    });
    fs::write(project.join("prism.lock"), lock.render().unwrap()).unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .output()
        .expect("runs prism run");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("42"));
}

#[test]
fn package_source_roots_carry_bundle_identity() {
    let tmp = TempDir::new("package-root-identity");
    let root = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    let dependencies = vec![Dependency {
        name: STORE_PKG_NAME.to_string(),
        source: DepSource::Hash(root.clone()),
    }];
    let mut lock = Lock::default();
    lock.set(LockEntry {
        name: STORE_PKG_NAME.to_string(),
        scheme: HASH_SCHEME.to_string(),
        hash: Digest::from(root.clone()),
        source: dependencies[0].source.clone(),
    });

    let roots =
        package_source_roots(&lock, &dependencies, &tmp.root(), &DynFlags::default()).unwrap();
    let identity = roots[0].source_bundle_identity().unwrap();
    assert_eq!(identity.root, root);
    assert_eq!(identity.scheme, HASH_SCHEME);
    assert_eq!(identity.artifact_kind, SourceBundleArtifactKind::Package);
    assert!(matches!(
        &identity.kind,
        SourceBundleKind::Package { name, origin }
            if name == STORE_PKG_NAME && origin == &SourceBundleOrigin::HashPin
    ));
}

#[test]
fn git_package_source_roots_carry_origin_identity() {
    let tmp = TempDir::new("git-package-root-identity");
    let root = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    let dependencies = vec![Dependency {
        name: STORE_PKG_NAME.to_string(),
        source: DepSource::Git {
            url: STORE_PKG_ORIGIN.to_string(),
            version: STORE_PKG_TAG.to_string(),
        },
    }];
    let mut lock = Lock::default();
    lock.set(LockEntry {
        name: STORE_PKG_NAME.to_string(),
        scheme: HASH_SCHEME.to_string(),
        hash: Digest::from(root.clone()),
        source: dependencies[0].source.clone(),
    });
    let transport = DiskTransport::open(tmp.root()).unwrap();
    let body = serialize_index(&[IndexRow {
        origin: STORE_PKG_ORIGIN.to_string(),
        name: STORE_PKG_NAME.to_string(),
        tag: STORE_PKG_TAG.to_string(),
        scheme: HASH_SCHEME.to_string(),
        kind: INDEX_KIND_SOURCE.to_string(),
        root: Digest::from(root.clone()),
    }]);
    transport
        .publish_index(&SignedArtifact { body, sig: None })
        .unwrap();
    let flags = DynFlags {
        sign_mode: SignMode::Unsigned,
        ..DynFlags::default()
    };

    let roots = package_source_roots(&lock, &dependencies, &tmp.root(), &flags).unwrap();
    let identity = roots[0].source_bundle_identity().unwrap();
    assert_eq!(identity.root, root);
    assert_eq!(identity.scheme, HASH_SCHEME);
    assert_eq!(identity.artifact_kind, SourceBundleArtifactKind::Package);
    assert!(matches!(
        &identity.kind,
        SourceBundleKind::Package { name, origin }
            if name == STORE_PKG_NAME
                && origin == &SourceBundleOrigin::Git(STORE_PKG_ORIGIN.to_string())
    ));
}

#[test]
fn git_package_requires_an_authenticated_index_pointer() {
    let tmp = TempDir::new("git-package");
    let project = tmp.path.join("app");
    let root = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    write_package_project(
        &project,
        &format!("{{ git = \"{STORE_PKG_ORIGIN}\", version = \"{STORE_PKG_TAG}\" }}"),
    );

    let source = DepSource::Git {
        url: STORE_PKG_ORIGIN.to_string(),
        version: STORE_PKG_TAG.to_string(),
    };
    let mut lock = Lock::default();
    lock.set(LockEntry {
        name: STORE_PKG_NAME.to_string(),
        scheme: HASH_SCHEME.to_string(),
        hash: Digest::from(root.clone()),
        source,
    });
    fs::write(project.join("prism.lock"), lock.render().unwrap()).unwrap();

    let missing_index = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .output()
        .expect("runs prism check");
    assert!(!missing_index.status.success());
    assert!(String::from_utf8_lossy(&missing_index.stderr).contains("signed package index"));

    let transport = DiskTransport::open(tmp.root()).unwrap();
    let wrong_origin = serialize_index(&[IndexRow {
        origin: STORE_PKG_OTHER_ORIGIN.to_string(),
        name: STORE_PKG_NAME.to_string(),
        tag: STORE_PKG_TAG.to_string(),
        scheme: HASH_SCHEME.to_string(),
        kind: INDEX_KIND_SOURCE.to_string(),
        root: Digest::from(root.clone()),
    }]);
    transport
        .publish_index(&SignedArtifact {
            body: wrong_origin,
            sig: None,
        })
        .unwrap();

    let wrong_dev_index = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism run");
    assert!(!wrong_dev_index.status.success());
    assert!(
        String::from_utf8_lossy(&wrong_dev_index.stderr).contains(&format!(
            "no pointer for {STORE_PKG_ORIGIN} {STORE_PKG_NAME}@{STORE_PKG_TAG}"
        ))
    );

    let body = serialize_index(&[IndexRow {
        origin: STORE_PKG_ORIGIN.to_string(),
        name: STORE_PKG_NAME.to_string(),
        tag: STORE_PKG_TAG.to_string(),
        scheme: HASH_SCHEME.to_string(),
        kind: INDEX_KIND_SOURCE.to_string(),
        root: Digest::from(root),
    }]);
    transport
        .publish_index(&SignedArtifact { body, sig: None })
        .unwrap();

    let trusted_dev_index = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism run");
    assert!(
        trusted_dev_index.status.success(),
        "{}",
        String::from_utf8_lossy(&trusted_dev_index.stderr)
    );
    assert!(String::from_utf8_lossy(&trusted_dev_index.stdout).contains("42"));
}

#[test]
fn package_resolution_rejects_foreign_lock_scheme() {
    let tmp = TempDir::new("foreign-lock-scheme");
    let root = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    let dependencies = vec![Dependency {
        name: STORE_PKG_NAME.to_string(),
        source: DepSource::Hash(root.clone()),
    }];
    let mut lock = Lock::default();
    lock.set(LockEntry {
        name: STORE_PKG_NAME.to_string(),
        scheme: "future-scheme".to_string(),
        hash: Digest::from(root),
        source: dependencies[0].source.clone(),
    });

    let err = package_source_roots(&lock, &dependencies, &tmp.root(), &DynFlags::default())
        .unwrap_err()
        .to_string();
    assert!(err.contains(&format!("dependency `{STORE_PKG_NAME}`")));
    assert!(err.contains("future-scheme"));
}

#[test]
fn why_rejects_foreign_lock_scheme_before_using_hashes() {
    let tmp = TempDir::new("why-foreign-lock-scheme");
    let project = tmp.path.join("app");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(
        project.join("prism.toml"),
        r#"[package]
name = "app"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    fs::write(project.join("src").join("main.pr"), "fn main() = ()\n").unwrap();
    fs::write(
        project.join("prism.lock"),
        format!("prism-lock\tv2\n{STORE_PKG_NAME}\tfuture-scheme\tdeadbeef\thash deadbeef\n"),
    )
    .unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("why")
        .arg(STORE_PKG_NAME)
        .current_dir(&project)
        .output()
        .expect("runs prism pkg why");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains(&format!("dependency `{STORE_PKG_NAME}`")),
        "{stderr}"
    );
    assert!(stderr.contains("future-scheme"), "{stderr}");
}

#[test]
fn signed_index_resolution_rejects_foreign_scheme() {
    let tmp = TempDir::new("foreign-index-scheme");
    let transport = DiskTransport::open(tmp.root()).unwrap();
    let body = serialize_index(&[IndexRow {
        origin: STORE_PKG_ORIGIN.to_string(),
        name: STORE_PKG_NAME.to_string(),
        tag: STORE_PKG_TAG.to_string(),
        scheme: "future-scheme".to_string(),
        kind: INDEX_KIND_SOURCE.to_string(),
        root: Digest::from("00".repeat(32)),
    }]);
    transport
        .publish_index(&SignedArtifact { body, sig: None })
        .unwrap();
    let flags = DynFlags {
        sign_mode: SignMode::Unsigned,
        ..DynFlags::default()
    };

    let err = prism::pkg::signed_index_pointer(
        STORE_PKG_ORIGIN,
        STORE_PKG_NAME,
        STORE_PKG_TAG,
        &tmp.root(),
        &flags,
    )
    .unwrap_err()
    .to_string();
    assert!(err.contains("foreign hash scheme"));
    assert!(err.contains("future-scheme"));
}

#[test]
fn publish_add_and_run_git_package_end_to_end() {
    let tmp = TempDir::new("publish-add-run");
    let package = tmp.path.join("StorePkg.pr");
    fs::write(&package, "pub fn answer() : Int = 41\n").unwrap();

    let publish = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("publish")
        .arg(&package)
        .arg("--tag")
        .arg("v1")
        .arg("--name")
        .arg("StorePkg")
        .arg("--origin")
        .arg("example.invalid/StorePkg")
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism pkg publish");
    assert!(
        publish.status.success(),
        "{}",
        String::from_utf8_lossy(&publish.stderr)
    );

    let project = tmp.path.join("app");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(
        project.join("prism.toml"),
        r#"[package]
name = "app"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    fs::write(
        project.join("src").join("main.pr"),
        "import StorePkg (answer)\nfn main() : Unit ! {IO} = println(show_int(answer() + 1))\n",
    )
    .unwrap();

    let add = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("add")
        .arg("example.invalid/StorePkg@v1")
        .current_dir(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism pkg add");
    assert!(
        add.status.success(),
        "{}",
        String::from_utf8_lossy(&add.stderr)
    );
    let lock = fs::read_to_string(project.join("prism.lock")).unwrap();
    assert!(lock.contains("StorePkg"));
    assert!(fs::read_to_string(project.join("prism.toml"))
        .unwrap()
        .contains("example.invalid/StorePkg"));

    let run = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism run");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(String::from_utf8_lossy(&run.stdout).contains("42"));
}

#[test]
fn repo_tzdb_package_publishes_and_runs_end_to_end() {
    let tmp = TempDir::new("tzdb-seed");
    let publish = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("publish")
        .arg(tzdb_package())
        .arg("--tag")
        .arg("v0")
        .arg("--name")
        .arg("Tzdb")
        .arg("--origin")
        .arg("example.invalid/Tzdb")
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism pkg publish");
    assert!(
        publish.status.success(),
        "{}",
        String::from_utf8_lossy(&publish.stderr)
    );

    let project = tmp.path.join("tz-app");
    copy_dir(&project_fixture("tzdb_app"), &project);

    let add = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("add")
        .arg("example.invalid/Tzdb@v0")
        .current_dir(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism pkg add");
    assert!(
        add.status.success(),
        "{}",
        String::from_utf8_lossy(&add.stderr)
    );

    let run = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(&project)
        .env("PRISM_STORE_PATH", tmp.root())
        .env("PRISM_SIGN_MODE", "unsigned")
        .output()
        .expect("runs prism run");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(String::from_utf8_lossy(&run.stdout).contains("1970-01-01T09:00:00Z Asia/Tokyo"));
}

#[test]
fn check_world_reports_real_package_roots_by_digest() {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("packages"))
        .arg("--json")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["format"], "prism-check-world-v1");
    assert_eq!(report["validation"]["scope"], "typecheck-only");
    assert_eq!(report["validation"]["checks"]["typecheck"], "passed");
    assert_eq!(report["validation"]["checks"]["doctests"], "not-run");
    assert_eq!(report["validation"]["checks"]["replay"], "not-run");
    assert_eq!(report["validation"]["checks"]["native"], "not-run");
    assert_eq!(report["compatibility"]["verdict"], "compatible");
    let packages = report["packages"].as_object().unwrap();
    let tzdb = packages
        .values()
        .find(|package| package["name"] == "tzdb")
        .expect("tzdb package is reported");
    assert_eq!(tzdb["lineage"]["inputs"]["source"]["scheme"], HASH_SCHEME);
    assert_eq!(tzdb["lineage"]["inputs"]["stdlib"]["scheme"], HASH_SCHEME);
    assert!(tzdb["lineage"]["compiler"]["identity"]
        .as_str()
        .unwrap()
        .contains("backend=check"));
}

#[test]
fn check_world_reports_package_identity_conflicts() {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(project_fixture("check_world_duplicate"))
        .arg("--json")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["compatibility"]["verdict"], "incompatible");
    let duplicate_roots = report["compatibility"]["duplicate_packages"]["dup"]
        .as_array()
        .expect("duplicate package roots are reported");
    assert_eq!(duplicate_roots.len(), 2);
    assert!(report["compatibility"]["problems"]
        .as_array()
        .unwrap()
        .iter()
        .any(|problem| problem.as_str().unwrap().contains("package name `dup`")));
}

#[test]
fn check_world_reports_dependency_root_conflicts() {
    let tmp = TempDir::new("check-world-dep-conflict");
    let root_a = store_package_bundle(&tmp.root(), STORE_PKG_NAME, STORE_PKG_SOURCE);
    let root_b = store_package_bundle(&tmp.root(), STORE_PKG_NAME, "pub fn answer() : Int = 42\n");
    let app_a = tmp.path.join("world").join("app-a");
    let app_b = tmp.path.join("world").join("app-b");
    write_named_package_project(&app_a, "app-a", &format!("{:?}", hash_pin(&root_a)));
    write_named_package_project(&app_b, "app-b", &format!("{:?}", hash_pin(&root_b)));

    for (project, root) in [(&app_a, root_a), (&app_b, root_b)] {
        let mut lock = Lock::default();
        lock.set(LockEntry {
            name: STORE_PKG_NAME.to_string(),
            scheme: HASH_SCHEME.to_string(),
            hash: Digest::from(root.clone()),
            source: DepSource::Hash(root),
        });
        fs::write(project.join("prism.lock"), lock.render().unwrap()).unwrap();
    }

    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(tmp.path.join("world"))
        .arg("--json")
        .env("PRISM_STORE_PATH", tmp.root())
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["compatibility"]["verdict"], "incompatible");
    let roots = report["compatibility"]["dependency_root_conflicts"]["hash-pin/StorePkg"]
        .as_array()
        .expect("dependency conflict roots are reported");
    assert_eq!(roots.len(), 2);
}

#[test]
fn check_world_strict_fails_on_incompatible_universe() {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(project_fixture("check_world_duplicate"))
        .arg("--strict")
        .output()
        .expect("runs prism pkg check-world");
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.contains("validation: typecheck-only"), "{stdout}");
    assert!(stdout.contains("doctests: not-run"), "{stdout}");
    assert!(stdout.contains("compatibility: incompatible"), "{stdout}");
    assert!(
        stderr.contains("incompatible package universe"),
        "stderr:\n{stderr}"
    );
}

fn check_world_fixture() -> Value {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("check_world_tzdb.json");
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

// The one tzdb package entry in a check-world report, keyed by source-root digest
// but found by name (the digest is path-independent, so a fixture generated from a
// relative path and a live report from an absolute one agree on it).
fn tzdb_entry(report: &Value) -> Value {
    report["packages"]
        .as_object()
        .unwrap()
        .values()
        .find(|p| p["name"] == "tzdb")
        .expect("tzdb package is reported")
        .clone()
}

fn run_docs(args: &[&std::ffi::OsStr]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("docs")
        .args(args)
        .output()
        .expect("runs prism docs")
}

#[test]
fn docs_manifest_round_trips_and_rejects_stale_and_drifted_inputs() {
    let tmp = TempDir::new("docs-manifest");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    let _ = fs::remove_dir_all(project.join("docs"));
    let out = project.join("docs");

    // Generation writes the manifest beside the pages, and it verifies clean.
    let gen = run_docs(&[project.as_os_str(), "--out".as_ref(), out.as_ref()]);
    assert!(
        gen.status.success(),
        "{}",
        String::from_utf8_lossy(&gen.stderr)
    );
    assert!(out.join("docs.plineage").is_file(), "manifest is written");
    let ok = run_docs(&[
        project.as_os_str(),
        "--out".as_ref(),
        out.as_ref(),
        "--verify-manifest".as_ref(),
    ]);
    assert!(
        ok.status.success(),
        "{}",
        String::from_utf8_lossy(&ok.stderr)
    );

    // A tampered page fails verification, naming the changed page by digest.
    let page = out.join("tzdb.md");
    let mut bytes = fs::read_to_string(&page).unwrap();
    bytes.push_str("\n<!-- tampered -->\n");
    fs::write(&page, bytes).unwrap();
    let stale = run_docs(&[
        project.as_os_str(),
        "--out".as_ref(),
        out.as_ref(),
        "--verify-manifest".as_ref(),
    ]);
    assert!(
        !stale.status.success(),
        "a stale page must fail verification"
    );
    assert!(
        String::from_utf8_lossy(&stale.stderr).contains("changed"),
        "stderr:\n{}",
        String::from_utf8_lossy(&stale.stderr)
    );

    // Restore the page, then move a source root: verification fails on the drifted
    // input rather than silently documenting against a new one.
    let regen = run_docs(&[project.as_os_str(), "--out".as_ref(), out.as_ref()]);
    assert!(regen.status.success());
    let entry = project.join("src").join("Tzdb.pr");
    let mutated = fs::read_to_string(&entry)
        .unwrap()
        .replace("offset_minutes = 540", "offset_minutes = 541");
    fs::write(&entry, mutated).unwrap();
    let drifted = run_docs(&[
        project.as_os_str(),
        "--out".as_ref(),
        out.as_ref(),
        "--verify-manifest".as_ref(),
    ]);
    assert!(
        !drifted.status.success(),
        "a moved source root must fail manifest verification"
    );
    assert!(
        String::from_utf8_lossy(&drifted.stderr).contains("moved"),
        "stderr:\n{}",
        String::from_utf8_lossy(&drifted.stderr)
    );
}

#[test]
fn check_world_reports_per_package_gates_and_public_surface() {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(tzdb_package())
        .arg("--json")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    let live = tzdb_entry(&report);
    let fixture = tzdb_entry(&check_world_fixture());

    // Every per-package gate reads back with the committed status: the seed commits
    // a docs manifest and a doctest (both verified/run) and no examples or replay.
    assert_eq!(live["gates"], fixture["gates"], "per-package gates drifted");
    assert_eq!(live["gates"]["check"], "passed");
    assert_eq!(live["gates"]["docs"], "passed");
    assert_eq!(live["gates"]["doctests"], "passed");
    assert_eq!(live["gates"]["example"], "not-run");
    assert_eq!(live["gates"]["replay"], "not-run");

    // The public surface reads back by digest, name-sorted. Names and scheme are
    // pinned against the fixture; the hashes are exercised for movement by the
    // baseline test below rather than frozen here.
    let names = |entry: &Value| -> Vec<String> {
        entry["public_api"]
            .as_array()
            .unwrap()
            .iter()
            .map(|d| d["name"].as_str().unwrap().to_string())
            .collect()
    };
    assert_eq!(
        names(&live),
        names(&fixture),
        "public surface names drifted"
    );
    assert!(
        live["public_api"]
            .as_array()
            .unwrap()
            .iter()
            .all(|d| d["scheme"] == HASH_SCHEME && d["hash"].is_string()),
        "every public def carries a scheme-tagged hash"
    );
    assert!(names(&live).contains(&"asia_tokyo".to_string()));
    assert!(names(&live).contains(&"Zone".to_string()));
}

#[test]
fn check_world_names_moved_public_definition_against_baseline() {
    let tmp = TempDir::new("check-world-public-surface");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    // The committed docs manifest no longer matches the mutated source; drop it so
    // the docs gate is honestly not-run and the report focuses on the surface diff.
    let _ = fs::remove_dir_all(project.join("docs"));
    let entry = project.join("src").join("Tzdb.pr");
    let mutated = fs::read_to_string(&entry)
        .unwrap()
        .replace("offset_minutes = 540", "offset_minutes = 541");
    fs::write(&entry, mutated).unwrap();

    let baseline = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("check_world_tzdb.json");
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(&project)
        .arg("--baseline")
        .arg(&baseline)
        .arg("--json")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    let changes = &tzdb_entry(&report)["public_api_changes"];
    assert_eq!(changes["changed"], true);
    let moved = changes["moved"].as_array().expect("moved defs are named");
    let asia = moved
        .iter()
        .find(|m| m["name"] == "asia_tokyo")
        .expect("the mutated definition is named as moved");
    assert_ne!(
        asia["old"], asia["new"],
        "a moved definition names both digests"
    );
    // Named by digest, never by path: the change carries hashes, not file names.
    assert!(asia["old"].is_string() && asia["new"].is_string());
}

// The usage gate has three reported states. `tzdb` commits a `usage-summary.md`
// golden, so it reads back `passed` with no drift line.
#[test]
fn usage_gate_passes_on_committed_golden() {
    let report = check_world_json(tzdb_package());
    let gates = &tzdb_entry(&report)["gates"];
    assert_eq!(gates["usage"], "passed");
    assert!(
        gates.get("usage_drift").is_none(),
        "a passing usage gate carries no drift line: {gates}"
    );
}

// A golden that no longer matches the regenerated summary reports `failed` and names
// the first differing line. Because the gate is report-only, drift never fails strict
// mode: `--strict` still exits zero.
#[test]
fn usage_gate_reports_drift_with_named_line_yet_never_fails_strict() {
    let tmp = TempDir::new("usage-gate-drift");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    drift_usage_golden(&project);

    let report = check_world_json(&project);
    let gates = &tzdb_entry(&report)["gates"];
    assert_eq!(gates["usage"], "failed");
    let drift = gates["usage_drift"].as_str().expect("drift line is named");
    assert!(
        drift.starts_with("line ")
            && drift.contains("| utc")
            && drift.contains("YES")
            && drift.contains("no "),
        "drift names the first differing markdown line with both sides quoted: {drift:?}"
    );

    // Report-only: a drifted usage gate does not fail strict mode the way the other
    // gates do.
    let strict = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(&project)
        .arg("--strict")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        strict.status.success(),
        "usage drift must not fail strict mode:\n{}",
        String::from_utf8_lossy(&strict.stderr)
    );
}

// A package that commits no golden reports `not-run`, with no drift line.
#[test]
fn usage_gate_is_not_run_without_a_golden() {
    let tmp = TempDir::new("usage-gate-not-run");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    fs::remove_file(project.join(USAGE_SUMMARY_GOLDEN)).unwrap();

    let report = check_world_json(&project);
    let gates = &tzdb_entry(&report)["gates"];
    assert_eq!(gates["usage"], "not-run");
    assert!(gates.get("usage_drift").is_none());
}

// Flip the `utc` row's noalloc cell in the committed golden so it drifts from the
// regenerated summary. The replacement is the same width as the original, so the
// table alignment is untouched and the first drifted line is the corrupted row.
fn drift_usage_golden(project: &Path) {
    let golden = project.join(USAGE_SUMMARY_GOLDEN);
    let corrupted: String = fs::read_to_string(&golden)
        .unwrap()
        .lines()
        .map(|l| {
            if l.starts_with("| utc ") {
                l.replacen(" no ", " YES", 1)
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(&golden, corrupted).unwrap();
}

fn accept_usage(path: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("accept-usage")
        .arg(path)
        .output()
        .expect("runs prism pkg accept-usage")
}

// Run `pkg check-world` against `path` with extra flags, returning the raw output so
// a test can assert on the exit status.
fn check_world_exit(path: &Path, flags: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(path)
        .args(flags)
        .output()
        .expect("runs prism pkg check-world")
}

// `pkg accept-usage` writes the summary a package commits, and the gate reads it
// straight back as `passed`. The write is byte-stable: accepting an unchanged
// package a second time rewrites identical bytes, so a committed golden never churns.
#[test]
fn accept_usage_writes_a_gate_passing_and_byte_stable_summary() {
    let tmp = TempDir::new("accept-usage");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    let golden = project.join(USAGE_SUMMARY_GOLDEN);
    fs::remove_file(&golden).unwrap();

    let out = accept_usage(&project);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(golden.is_file(), "accept-usage writes the summary");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("usage-summary.md"),
        "the confirmation names the file"
    );

    let gates = &tzdb_entry(&check_world_json(&project))["gates"];
    assert_eq!(
        gates["usage"], "passed",
        "a freshly accepted summary passes"
    );

    let first = fs::read(&golden).unwrap();
    accept_usage(&project);
    assert_eq!(
        first,
        fs::read(&golden).unwrap(),
        "a second accept rewrites identical bytes"
    );
}

// A drifted golden reads back `failed`; `accept-usage` regenerates it in place and
// the gate returns to `passed`.
#[test]
fn accept_usage_heals_a_drifted_summary() {
    let tmp = TempDir::new("accept-usage-heal");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    drift_usage_golden(&project);
    assert_eq!(
        tzdb_entry(&check_world_json(&project))["gates"]["usage"],
        "failed"
    );

    accept_usage(&project);
    assert_eq!(
        tzdb_entry(&check_world_json(&project))["gates"]["usage"],
        "passed"
    );
}

// `--strict-usage` promotes a usage drift to a strict failure; plain `--strict`
// still ignores it (usage is report-only by default).
#[test]
fn strict_usage_promotes_drift_to_a_strict_failure() {
    let tmp = TempDir::new("strict-usage");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    drift_usage_golden(&project);

    assert!(
        check_world_exit(&project, &["--strict"]).status.success(),
        "plain --strict leaves usage report-only"
    );
    assert!(
        !check_world_exit(&project, &["--strict", "--strict-usage"])
            .status
            .success(),
        "--strict-usage makes a drifted summary fail strict mode"
    );
}

// A package that commits no summary is `not-run`, never fatal, under either strict
// mode: missing means the package has not opted in.
#[test]
fn missing_usage_summary_is_never_fatal() {
    let tmp = TempDir::new("missing-usage");
    let project = tmp.path.join("tzdb");
    copy_dir(tzdb_package(), &project);
    fs::remove_file(project.join(USAGE_SUMMARY_GOLDEN)).unwrap();

    assert_eq!(
        tzdb_entry(&check_world_json(&project))["gates"]["usage"],
        "not-run"
    );
    assert!(check_world_exit(&project, &["--strict"]).status.success());
    assert!(
        check_world_exit(&project, &["--strict", "--strict-usage"])
            .status
            .success(),
        "a missing summary is not opted in, so --strict-usage does not fail on it"
    );
}

// The check-world JSON names the artifact format the golden is compared under and
// the whole-program tier the summary is headed by.
#[test]
fn check_world_json_names_usage_format_and_tier() {
    let gates = &tzdb_entry(&check_world_json(tzdb_package()))["gates"];
    assert_eq!(gates["usage_format"], "usage-summary-md");
    assert_eq!(gates["usage_tier"], "whole-program-free-monad");
}

// Run `pkg check-world --json` against `path` and parse the report.
fn check_world_json(path: &Path) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("pkg")
        .arg("check-world")
        .arg(path)
        .arg("--json")
        .output()
        .expect("runs prism pkg check-world");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}
