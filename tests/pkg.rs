//! The package manager: manifest forms, the lockfile, and the Merkle-DAG
//! resolver over a real content-addressed store.
//!
//! The manifest and lock formats have their own unit round-trips beside their
//! code; this file is the integration layer, where a multi-definition program is
//! committed to a temp store and the resolver's closure is checked against the
//! dependency graph the commit wrote. It also pins the missing-hash diagnostic
//! (it must name the hash and the edge that wanted it), the `prism why` trace, and
//! the container-reification reservation (the two homes of the
//! representation-affecting class list must agree).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::pkg::resolve::{resolve_closure, trace, ResolveError};
use prism::pkg::transport::DiskTransport;
use prism::store::coherence::is_representation_affecting;
use prism::store::disk::Store;
use prism::{commit_to_store, default_roots, with_prelude, Config};

// A multi-definition program with a deliberate dependency chain, `pkg_`-prefixed
// to stay clear of the prelude: main -> top -> {mid, leaf}, mid -> leaf.
const PROG: &str = "\
fn pkg_leaf(n : Int) : Int = n + 1
fn pkg_mid(n : Int) : Int = pkg_leaf(n) * 2
fn pkg_top(n : Int) : Int =
  let m = pkg_mid(n)
  m + pkg_leaf(n)
fn main() = println(pkg_top(3))
";

// --- temp store scaffolding ---------------------------------------------

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
