//! On-disk store: layout, immutability, atomicity, indexes, and the warm-cache
//! end-to-end invariant (a second commit of an unchanged program writes zero
//! anonymous objects).

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::store::disk::{
    resolve_store_path, CanonicalKey, DefMeta, Store, VerifiedRecord, Written,
};
use prism::{commit_to_store, default_roots, with_prelude, Config};

// A unique scratch directory removed on drop, so a test never touches the real
// user cache and leaves nothing behind.
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
        path.push(format!(
            "prism-store-{tag}-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn store_root(&self) -> PathBuf {
        self.path.join("store")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// A representative full-length hex hash and a second distinct one.
const H1: &str = "ab00112233445566778899aabbccddeeff00112233445566778899aabbccddee";
const H2: &str = "cd00112233445566778899aabbccddeeff00112233445566778899aabbccddee";

#[test]
fn put_get_round_trips_and_reports_new_then_hit() {
    let tmp = TempDir::new("roundtrip");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    assert_eq!(store.put(H1, b"hello").unwrap(), Written::New);
    assert_eq!(store.get(H1).unwrap(), b"hello");
    assert!(store.has(H1));
    assert!(!store.has(H2));
    // Re-putting identical bytes is a hit, not a rewrite.
    assert_eq!(store.put(H1, b"hello").unwrap(), Written::Hit);
}

#[test]
fn immutability_rejects_a_different_rewrite() {
    let tmp = TempDir::new("immutable");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"first").unwrap();
    // Same hash, different bytes: corruption, a hard error, never a silent
    // overwrite. The original bytes survive.
    assert!(store.put(H1, b"second").is_err());
    assert_eq!(store.get(H1).unwrap(), b"first");
}

#[test]
fn objects_are_sharded_by_first_hash_byte() {
    let tmp = TempDir::new("shard");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"x").unwrap();
    let expected = tmp
        .store_root()
        .join("objects")
        .join(&H1[..2])
        .join(&H1[2..]);
    assert!(expected.exists(), "object not at sharded path {expected:?}");
}

#[test]
fn a_leftover_temp_file_is_ignored() {
    let tmp = TempDir::new("atomic");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"real").unwrap();
    // Simulate a writer killed mid-rename: a stray temp in the object shard dir.
    let shard = tmp.store_root().join("objects").join(&H1[..2]);
    fs::write(shard.join(".tmp.9999.0.0"), b"garbage").unwrap();
    // A reopened store still reads the real object and never mistakes the temp
    // for content (readers only open the exact hash path).
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    assert_eq!(store.get(H1).unwrap(), b"real");
    assert!(store.has(H1));
}

#[test]
fn metadata_round_trips_and_is_mutable() {
    let tmp = TempDir::new("meta");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    let m = DefMeta {
        name: "Data.Map.insert".into(),
        ty: "(k, v, Map k v) -> Map k v ! <>".into(),
        doc: "insert a binding".into(),
    };
    store.put_meta(H1, &m).unwrap();
    assert_eq!(store.get_meta(H1).unwrap(), Some(m));
    // The metadata layer is mutable: a rename repoints without a new object.
    let renamed = DefMeta {
        name: "Data.Map.set".into(),
        ty: "(k, v, Map k v) -> Map k v ! <>".into(),
        doc: "insert a binding".into(),
    };
    store.put_meta(H1, &renamed).unwrap();
    assert_eq!(store.get_meta(H1).unwrap().unwrap().name, "Data.Map.set");
    assert_eq!(store.get_meta(H2).unwrap(), None);
}

#[test]
fn name_and_dep_indexes_round_trip() {
    let tmp = TempDir::new("index");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    let mut names = std::collections::BTreeMap::new();
    names.insert("map".to_string(), H1.to_string());
    names.insert("filter".to_string(), H2.to_string());
    store.bind_names(&names).unwrap();
    assert_eq!(store.lookup_name("map").unwrap().as_deref(), Some(H1));
    assert_eq!(store.names().unwrap().len(), 2);
    // A re-bind repoints the name (O(1) rename over metadata).
    let mut rebind = std::collections::BTreeMap::new();
    rebind.insert("map".to_string(), H2.to_string());
    store.bind_names(&rebind).unwrap();
    assert_eq!(store.lookup_name("map").unwrap().as_deref(), Some(H2));

    let mut edges = std::collections::BTreeMap::new();
    edges.insert(
        H1.to_string(),
        std::iter::once(H2.to_string()).collect::<std::collections::BTreeSet<_>>(),
    );
    store.add_dependents(&edges).unwrap();
    assert!(store.dependents(H1).unwrap().contains(H2));
    assert!(store.dependents(H2).unwrap().is_empty());
}

#[test]
fn canonical_and_verified_reserved_layers_round_trip() {
    let tmp = TempDir::new("reserved");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    let key = CanonicalKey {
        class: "Ord".into(),
        head: "Int".into(),
    };
    assert_eq!(store.canonical(&key).unwrap(), None);
    store.set_canonical(&key, H1).unwrap();
    assert_eq!(store.canonical(&key).unwrap().as_deref(), Some(H1));

    let rec = VerifiedRecord {
        kind: "parity".into(),
        scheme: "prism-core-hash-v1".into(),
        identity: "compiler=unit-test;target=test;backend=llvm;".into(),
        passed: true,
    };
    store.put_verified(H1, &rec).unwrap();
    let got = store.verified(H1).unwrap();
    assert_eq!(got, vec![rec]);
}

#[test]
fn a_foreign_scheme_stamp_is_refused() {
    let tmp = TempDir::new("scheme");
    let root = tmp.store_root();
    fs::create_dir_all(&root).unwrap();
    // A store stamped with a scheme this build does not speak must not open.
    fs::write(root.join("VERSION"), "some-other-scheme\nprism-store-v1\n").unwrap();
    assert!(Store::open_or_create(&root).is_err());
}

#[test]
fn reopening_a_valid_store_succeeds() {
    let tmp = TempDir::new("reopen");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"x").unwrap();
    drop(store);
    // The stamp this build wrote is the stamp this build accepts.
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    assert_eq!(store.get(H1).unwrap(), b"x");
}

#[test]
fn resolve_path_prefers_the_explicit_override() {
    let p = Path::new("/tmp/some/store");
    assert_eq!(resolve_store_path(Some(p)), p);
}

#[test]
fn second_commit_of_an_unchanged_program_writes_zero_objects() {
    let tmp = TempDir::new("e2e");
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(tmp.store_root());

    let src = with_prelude("fn double(x : Int) : Int = x * 2\n");
    let roots = default_roots(Path::new("."));

    let first = commit_to_store(&src, &roots, &cfg).unwrap();
    let second = commit_to_store(&src, &roots, &cfg).unwrap();

    assert!(
        first.objects_written > 0,
        "cold commit should write objects, wrote {first:?}"
    );
    assert_eq!(
        second.objects_written, 0,
        "warm commit must write zero objects, got {second:?}"
    );
    assert_eq!(
        second.objects_hit,
        first.objects_written + first.objects_hit
    );
}
