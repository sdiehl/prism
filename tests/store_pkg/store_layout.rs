//! On-disk store: layout, immutability, atomicity, indexes, and the warm-cache
//! end-to-end invariant (a second commit of an unchanged program writes zero
//! anonymous objects).

use std::fs;
use std::path::Path;
use std::sync::Mutex;
use std::time::{Duration, SystemTime};

use prism::core::HASH_SCHEME;
use prism::store::disk::{
    resolve_store_path, CanonicalKey, DefMeta, GcProgress, Store, StoreHash, VerifiedRecord,
    Written, OBJECT_SHARD_BUDGET, QUERY_SHARD_BUDGET,
};
use prism::{commit_to_store, default_roots, with_prelude, Config};

use crate::support::TempDir;

// Backdate a file's mtime so gc's age cutoff treats it as old, independent of
// wall-clock delays between test setup and the `gc` call.
fn backdate(path: &Path, age: Duration) {
    fs::File::open(path)
        .unwrap()
        .set_modified(SystemTime::now() - age)
        .unwrap();
}

// A representative full-length hex hash and a second distinct one.
const H1: &str = "ab00112233445566778899aabbccddeeff00112233445566778899aabbccddee";
const H2: &str = "cd00112233445566778899aabbccddeeff00112233445566778899aabbccddee";

// A query binding's on-disk home: sharded on the key's first two hex
// characters like every other layer, under one directory per kind.
fn query_path(root: &Path, kind: &str, key: &str) -> std::path::PathBuf {
    root.join("queries")
        .join(kind)
        .join(&key[..2])
        .join(&key[2..])
}

#[test]
fn store_hash_rejects_noncanonical_text() {
    assert!(StoreHash::new(H1).is_ok());
    assert!(StoreHash::new("AB").is_err());
    assert!(StoreHash::new("xz").is_err());
    assert!(StoreHash::new("a").is_err());
}

#[test]
fn put_get_round_trips_and_reports_new_then_hit() {
    let tmp = TempDir::new("store", "roundtrip");
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
    let tmp = TempDir::new("store", "immutable");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"first").unwrap();
    // Same hash, different bytes: corruption, a hard error, never a silent
    // overwrite. The original bytes survive.
    assert!(store.put(H1, b"second").is_err());
    assert_eq!(store.get(H1).unwrap(), b"first");
}

#[test]
fn concurrent_divergent_object_writers_cannot_overwrite() {
    let tmp = TempDir::new("store", "object-race");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let mut threads = Vec::new();
    for bytes in [b"first".as_slice(), b"second".as_slice()] {
        let store = store.clone();
        let barrier = barrier.clone();
        threads.push(std::thread::spawn(move || {
            barrier.wait();
            store.put(H1, bytes)
        }));
    }
    let results = threads
        .into_iter()
        .map(|thread| thread.join().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
    let stored = store.get(H1).unwrap();
    assert!(stored == b"first" || stored == b"second");
}

#[test]
fn objects_are_sharded_by_first_hash_byte() {
    let tmp = TempDir::new("store", "shard");
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
    let tmp = TempDir::new("store", "atomic");
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
    let tmp = TempDir::new("store", "meta");
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
    let tmp = TempDir::new("store", "index");
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
fn compiler_query_index_is_typed_and_immutable() {
    let tmp = TempDir::new("store", "queries");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    assert_eq!(store.get_query("linked-native", H1).unwrap(), None);
    store.put(H2, b"native-output").unwrap();
    store.put_query("linked-native", H1, H2).unwrap();
    assert_eq!(
        store.get_query("linked-native", H1).unwrap().as_deref(),
        Some(H2)
    );
    store.put_query("linked-native", H1, H2).unwrap();
    assert!(store.put_query("linked-native", H1, H1).is_err());
    assert!(store.put_query("../escape", H1, H2).is_err());
}

#[test]
fn concurrent_identical_query_writers_converge() {
    let tmp = TempDir::new("store", "query-concurrent");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();
    let mut threads = Vec::new();
    for _ in 0..8 {
        let store = store.clone();
        threads.push(std::thread::spawn(move || {
            store.put_query("linked-native", H1, H2).unwrap();
        }));
    }
    for thread in threads {
        thread.join().unwrap();
    }
    assert_eq!(
        store.get_query("linked-native", H1).unwrap().as_deref(),
        Some(H2)
    );
}

#[test]
fn malformed_query_entry_is_never_a_hit() {
    let tmp = TempDir::new("store", "query-corrupt");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    let path = query_path(&tmp.store_root(), "linked-native", H1);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, b"not-a-query\n").unwrap();
    assert!(store.get_query("linked-native", H1).is_err());
}

#[test]
fn query_bindings_are_sharded_and_layout_stamped() {
    let tmp = TempDir::new("store", "query-sharded");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();
    store.put_query("linked-native", H1, H2).unwrap();

    // The binding lives at the sharded path, no flat sibling beside it, and
    // the layer carries its own layout stamp (independent of the store-wide
    // VERSION file, which must not move for a query layout change).
    assert!(query_path(&tmp.store_root(), "linked-native", H1).is_file());
    assert!(!tmp
        .store_root()
        .join("queries")
        .join("linked-native")
        .join(H1)
        .exists());
    let stamp = fs::read_to_string(tmp.store_root().join("queries").join("LAYOUT")).unwrap();
    assert_eq!(stamp, "prism-query-layout-v2\n");
}

#[test]
fn pre_shard_flat_binding_reads_empty_and_gc_retires_it() {
    let tmp = TempDir::new("store", "query-pre-shard");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();

    // A relic of the flat pre-sharding layout: a well-formed binding written
    // directly under the kind directory, fresher than any gc cutoff.
    let relic = tmp
        .store_root()
        .join("queries")
        .join("linked-native")
        .join(H1);
    fs::create_dir_all(relic.parent().unwrap()).unwrap();
    fs::write(&relic, format!("prism-query-index-v1\n{H2}\n")).unwrap();

    // The sharded read path never opens it: the binding is an ordinary miss.
    assert_eq!(store.get_query("linked-native", H1).unwrap(), None);

    // Gc retires it regardless of age (bulk invalidation, not migration), and
    // the relic never marks its output live: the object survives here only
    // because it is still fresh.
    let stats = store.gc(Duration::from_hours(24), false).unwrap();
    assert_eq!(stats.queries_removed, 1);
    assert!(!relic.exists());
    assert!(store.has(H2));
}

#[test]
fn an_overfull_query_shard_sheds_its_oldest_bindings_on_publish() {
    let tmp = TempDir::new("store", "query-evict");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();

    // Keys crafted into one shard, published oldest-first; each binding is
    // backdated to a distinct age so the eviction order is deterministic
    // regardless of filesystem timestamp resolution.
    let total = QUERY_SHARD_BUDGET.cap + 2;
    let keys: Vec<String> = (0..total).map(|i| format!("ab{i:062x}")).collect();
    for (i, key) in keys.iter().enumerate() {
        store.put_query("linked-native", key, H2).unwrap();
        backdate(
            &query_path(&tmp.store_root(), "linked-native", key),
            Duration::from_secs((total - i) as u64),
        );
    }

    // The publish that pushed the shard past its cap trimmed it back to the
    // low-water mark (plus the entry just published), oldest bindings first.
    let evicted = QUERY_SHARD_BUDGET.cap + 1 - QUERY_SHARD_BUDGET.low;
    let shard = tmp
        .store_root()
        .join("queries")
        .join("linked-native")
        .join("ab");
    assert_eq!(
        fs::read_dir(&shard).unwrap().count(),
        QUERY_SHARD_BUDGET.low + 1
    );
    // An evicted binding is an ordinary miss, never an error.
    assert_eq!(store.get_query("linked-native", &keys[0]).unwrap(), None);
    assert_eq!(
        store
            .get_query("linked-native", &keys[evicted - 1])
            .unwrap(),
        None
    );
    assert_eq!(
        store
            .get_query("linked-native", &keys[evicted])
            .unwrap()
            .as_deref(),
        Some(H2)
    );
    assert_eq!(
        store
            .get_query("linked-native", &keys[total - 1])
            .unwrap()
            .as_deref(),
        Some(H2)
    );
}

#[test]
fn an_overfull_object_shard_sheds_oldest_and_a_hit_refreshes_age() {
    let tmp = TempDir::new("store", "object-evict");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    // A hit refreshes the stored object's age, keeping a re-derived object
    // ahead of cold generations when its shard evicts.
    store.put(H1, b"hot").unwrap();
    let hot = tmp
        .store_root()
        .join("objects")
        .join(&H1[..2])
        .join(&H1[2..]);
    backdate(&hot, Duration::from_hours(24));
    assert_eq!(store.put(H1, b"hot").unwrap(), Written::Hit);
    let age = SystemTime::now()
        .duration_since(fs::metadata(&hot).unwrap().modified().unwrap())
        .unwrap_or_default();
    assert!(age < Duration::from_hours(1));

    // Same shape as the query-shard test, one layer down: overfilling one
    // object shard trims it back to its low-water mark, oldest first, and an
    // evicted object simply reads as absent.
    let total = OBJECT_SHARD_BUDGET.cap + 2;
    let hashes: Vec<String> = (0..total).map(|i| format!("ef{i:062x}")).collect();
    for (i, hash) in hashes.iter().enumerate() {
        store.put(hash, b"generation").unwrap();
        backdate(
            &tmp.store_root()
                .join("objects")
                .join(&hash[..2])
                .join(&hash[2..]),
            Duration::from_secs((total - i) as u64),
        );
    }
    let evicted = OBJECT_SHARD_BUDGET.cap + 1 - OBJECT_SHARD_BUDGET.low;
    let shard = tmp.store_root().join("objects").join("ef");
    assert_eq!(
        fs::read_dir(&shard).unwrap().count(),
        OBJECT_SHARD_BUDGET.low + 1
    );
    assert!(!store.has(&hashes[0]));
    assert!(!store.has(&hashes[evicted - 1]));
    assert!(store.has(&hashes[evicted]));
    assert!(store.has(&hashes[total - 1]));
}

#[test]
fn canonical_and_verified_reserved_layers_round_trip() {
    let tmp = TempDir::new("store", "reserved");
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
        scheme: HASH_SCHEME.into(),
        identity: "compiler=unit-test;target=test;backend=llvm;".into(),
        passed: true,
    };
    store.put_verified(H1, &rec).unwrap();
    let got = store.verified(H1).unwrap();
    assert_eq!(got, vec![rec]);
}

#[test]
fn a_foreign_scheme_stamp_is_refused() {
    let tmp = TempDir::new("store", "scheme");
    let root = tmp.store_root();
    fs::create_dir_all(&root).unwrap();
    // A store stamped with a scheme this build does not speak must not open.
    fs::write(root.join("VERSION"), "some-other-scheme\nprism-store-v1\n").unwrap();
    assert!(Store::open_or_create(&root).is_err());
}

#[test]
fn reopening_a_valid_store_succeeds() {
    let tmp = TempDir::new("store", "reopen");
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
    let tmp = TempDir::new("store", "e2e");
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

#[test]
fn unboxed_program_commits_without_panicking() {
    let tmp = TempDir::new("store", "unboxed");
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(tmp.store_root());

    let src = with_prelude(
        "fn point() : #{ x : Int, y : Int } = #{ x = 1, y = 2 }\n\nfn main() : Int = point().#x + point().#y\n",
    );
    let roots = default_roots(Path::new("."));

    let stats = commit_to_store(&src, &roots, &cfg).expect("unboxed program commits");
    assert!(stats.objects_written > 0);
}

#[test]
fn gc_removes_a_stale_unreferenced_object() {
    let tmp = TempDir::new("store", "gc-stale-object");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"stale").unwrap();
    let path = tmp
        .store_root()
        .join("objects")
        .join(&H1[..2])
        .join(&H1[2..]);
    backdate(&path, Duration::from_hours(48));

    let stats = store.gc(Duration::from_hours(24), false).unwrap();

    assert_eq!(stats.objects_removed, 1);
    assert_eq!(stats.bytes_removed, 5);
    assert!(!store.has(H1));
}

#[test]
fn gc_dry_run_never_touches_the_filesystem() {
    let tmp = TempDir::new("store", "gc-dry-run");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"stale").unwrap();
    let path = tmp
        .store_root()
        .join("objects")
        .join(&H1[..2])
        .join(&H1[2..]);
    backdate(&path, Duration::from_hours(48));

    let stats = store.gc(Duration::from_hours(24), true).unwrap();

    assert_eq!(
        stats.objects_removed, 1,
        "dry run still predicts what it would remove"
    );
    assert!(store.has(H1), "dry run must not delete anything");
}

#[test]
fn gc_spares_an_object_still_bound_by_a_live_query() {
    let tmp = TempDir::new("store", "gc-live-query");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();
    store.put_query("linked-native", H1, H2).unwrap();
    // Age the object, not the query binding: a fresh binding must keep an old
    // object alive, proving the sweep consults liveness and not just an
    // object's own mtime.
    let object_path = tmp
        .store_root()
        .join("objects")
        .join(&H2[..2])
        .join(&H2[2..]);
    backdate(&object_path, Duration::from_hours(48));

    let stats = store.gc(Duration::from_hours(24), false).unwrap();

    assert_eq!(stats.objects_removed, 0);
    assert!(store.has(H2));
    assert_eq!(
        store.get_query("linked-native", H1).unwrap().as_deref(),
        Some(H2)
    );
}

#[test]
fn gc_spares_a_ref_protected_object_regardless_of_age() {
    let tmp = TempDir::new("store", "gc-ref-protected");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"pinned").unwrap();
    store.set_ref("pkg-root-test", H1).unwrap();
    // Age both the object and the ref index itself: unlike a query binding, a
    // `refs` entry never expires on its own; only `remove_ref` drops it.
    let object_path = tmp
        .store_root()
        .join("objects")
        .join(&H1[..2])
        .join(&H1[2..]);
    backdate(&object_path, Duration::from_hours(48));
    backdate(
        &tmp.store_root().join("index").join("refs"),
        Duration::from_hours(48),
    );

    let stats = store.gc(Duration::from_hours(24), false).unwrap();

    assert_eq!(stats.objects_removed, 0);
    assert!(store.has(H1));
}

#[test]
fn gc_prunes_a_stale_query_binding() {
    let tmp = TempDir::new("store", "gc-stale-query");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H2, b"native-output").unwrap();
    store.put_query("linked-native", H1, H2).unwrap();
    let binding_path = query_path(&tmp.store_root(), "linked-native", H1);
    backdate(&binding_path, Duration::from_hours(48));

    let stats = store.gc(Duration::from_hours(24), false).unwrap();

    assert_eq!(stats.queries_removed, 1);
    assert_eq!(store.get_query("linked-native", H1).unwrap(), None);
    // The now-dangling object the pruned binding pointed to is itself
    // unreferenced but still fresh, so this same pass leaves it alone.
    assert!(store.has(H2));
}

#[test]
fn gc_spares_a_fresh_unreferenced_object() {
    let tmp = TempDir::new("store", "gc-fresh");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"just written").unwrap();

    let stats = store.gc(Duration::from_hours(24), false).unwrap();

    assert_eq!(stats.objects_removed, 0);
    assert!(store.has(H1));
}

#[test]
fn an_overfull_meta_shard_sheds_its_oldest_blobs_on_publish() {
    let tmp = TempDir::new("store", "meta-evict");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    // Same shape as the object-shard test: metadata rides the object budget,
    // so overfilling one meta shard trims it back to the low-water mark and
    // an evicted blob simply reads as absent (its facts are re-derived).
    let total = OBJECT_SHARD_BUDGET.cap + 2;
    let hashes: Vec<String> = (0..total).map(|i| format!("ef{i:062x}")).collect();
    let m = DefMeta {
        name: "Data.Map.get".into(),
        ty: "Map k v -> k -> Option v".into(),
        doc: String::new(),
    };
    for (i, hash) in hashes.iter().enumerate() {
        store.put_meta(hash, &m).unwrap();
        backdate(
            &tmp.store_root()
                .join("meta")
                .join(&hash[..2])
                .join(&hash[2..]),
            Duration::from_secs((total - i) as u64),
        );
    }
    let evicted = OBJECT_SHARD_BUDGET.cap + 1 - OBJECT_SHARD_BUDGET.low;
    let shard = tmp.store_root().join("meta").join("ef");
    assert_eq!(
        fs::read_dir(&shard).unwrap().count(),
        OBJECT_SHARD_BUDGET.low + 1
    );
    assert_eq!(store.get_meta(&hashes[0]).unwrap(), None);
    assert_eq!(store.get_meta(&hashes[evicted - 1]).unwrap(), None);
    assert_eq!(store.get_meta(&hashes[evicted]).unwrap(), Some(m.clone()));
    assert_eq!(store.get_meta(&hashes[total - 1]).unwrap(), Some(m));
}

#[test]
fn an_object_shard_over_its_byte_budget_sheds_oldest_by_size() {
    let tmp = TempDir::new("store", "object-byte-evict");
    let store = Store::open_or_create(tmp.store_root()).unwrap();

    // Twenty 1 MiB objects in one shard stay far under the entry cap but blow
    // through the 16 MiB byte cap; the publish that crosses it trims oldest
    // entries until the shard is back under the 12 MiB byte low-water mark.
    let payload = vec![0u8; 1 << 20];
    let total = 20;
    let hashes: Vec<String> = (0..total).map(|i| format!("ee{i:062x}")).collect();
    for (i, hash) in hashes.iter().enumerate() {
        store.put(hash, &payload).unwrap();
        backdate(
            &tmp.store_root()
                .join("objects")
                .join(&hash[..2])
                .join(&hash[2..]),
            Duration::from_secs((total - i) as u64),
        );
    }
    // The trigger put's shard held 17 MiB besides the entry just published;
    // trimming to 12 MiB removed the five oldest, and later puts stayed under
    // the cap, so fifteen objects remain.
    let shard = tmp.store_root().join("objects").join("ee");
    assert_eq!(fs::read_dir(&shard).unwrap().count(), 15);
    for gone in &hashes[..5] {
        assert!(!store.has(gone));
    }
    for kept in &hashes[5..] {
        assert!(store.has(kept));
    }
}

#[test]
fn gc_drains_a_retired_object_tree_salvaging_live_and_fresh_entries() {
    let tmp = TempDir::new("store", "gc-retired-drain");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    let root = tmp.store_root();

    // Manufacture what a crashed bulk retirement leaves behind: a renamed
    // objects tree at the store root, its manifest recording the origin, one
    // shard holding a still-referenced entry, a fresh in-flight entry, and a
    // dead one.
    let live = H1;
    let fresh = format!("ab{:062x}", 0x1111);
    let dead = format!("ab{:062x}", 0xdead);
    store.set_ref("pkg-root-test", live).unwrap();
    let tree = root.join(".retired.test");
    let shard = tree.join("ab");
    fs::create_dir_all(&shard).unwrap();
    fs::write(
        tree.join(".retired-manifest"),
        "prism-store-retired-v1\nobjects\n",
    )
    .unwrap();
    let two_hours = Duration::from_hours(2);
    fs::write(shard.join(&live[2..]), b"referenced").unwrap();
    backdate(&shard.join(&live[2..]), two_hours);
    fs::write(shard.join(&fresh[2..]), b"in-flight").unwrap();
    fs::write(shard.join(&dead[2..]), b"dead").unwrap();
    backdate(&shard.join(&dead[2..]), two_hours);

    let phases = Mutex::new(Vec::new());
    let stats = store
        .gc_with_progress(Duration::from_hours(24), false, &|beat: &GcProgress| {
            phases.lock().unwrap().push(beat.phase.clone());
        })
        .unwrap();

    // The referenced entry and the fresh one came back into the live layer;
    // the dead one is gone with the tree.
    assert!(store.has(live));
    assert!(store.has(&fresh));
    assert!(!store.has(&dead));
    assert!(!tree.exists());
    assert_eq!(stats.salvaged, 2);
    assert_eq!(stats.objects_removed, 1);
    let phases = phases.into_inner().unwrap();
    assert!(
        phases.iter().any(|phase| phase == "drain objects"),
        "drain phase must report progress, saw {phases:?}"
    );
}

#[test]
fn census_counts_every_layer_by_name() {
    let tmp = TempDir::new("store", "census");
    let store = Store::open_or_create(tmp.store_root()).unwrap();
    store.put(H1, b"one").unwrap();
    store.put(H2, b"two").unwrap();
    store
        .put_meta(
            H1,
            &DefMeta {
                name: "main".into(),
                ty: "() -> Int".into(),
                doc: String::new(),
            },
        )
        .unwrap();
    store.put_query("linked-native", H1, H2).unwrap();

    let census = store.census().unwrap();
    assert_eq!(census.files("objects"), 2);
    assert_eq!(census.files("meta"), 1);
    assert_eq!(census.files("queries/linked-native"), 1);
    assert_eq!(census.files("no-such-layer"), 0);
    assert!(census.total() >= 4);
}
