//! The from-scratch versus incremental oracle pair.
//!
//! This is the content-addressed analogue of the interpreter/native parity gate,
//! and the half of the `hash_parity` invariant the store completes.
//!
//! `hash_parity` proves *equal hash implies a byte-identical artifact* over
//! curated pairs. This file proves the other half over a real multi-definition
//! program driven two ways: built from scratch into a cold store, and built
//! incrementally by editing one definition against a warm store. The acceptance
//! is threefold:
//!
//!  (a) editing a definition moves exactly that definition and its Merkle
//!      closure (its transitive dependents); every other hash is unchanged, so
//!      an incremental build recompiles the closure and nothing more;
//!  (b) the emitted artifact is byte-identical between a full cold rebuild and
//!      the incremental path (the stored anonymous-Core object per definition,
//!      and the whole-program LLVM IR, which the store never perturbs);
//!  (c) an edit that only reformats or renames a local yields zero hash movement
//!      and writes zero new objects.
//!
//! Verification caching rides on the same identity: a parity pass recorded
//! against a content hash ([`prism::store::verify`]) is reused when a reformat
//! keeps the hash and re-run when a semantic edit moves it, so check cost tracks
//! the Merkle closure rather than the size of the suite.
//!
//! Every assertion is taken in the store's one hashing regime, pre-optimizer
//! elaborated Core: the closure is read from the pre-optimizer dependency graph
//! (`store_def_inputs`) and the per-definition hashes the commit writes (`dump
//! core-hash`), and byte-identity is read from the store's name index and
//! objects. That is deliberate: the store commits the pre-optimizer Core hash
//! (`commit_to_store`, aligned with `dump core-hash` and `store_def_inputs`), so
//! the oracle diffs the same hashes the store keys on, not a second surface that
//! could disagree. Identity is optimizer-independent by design; the optimizer
//! level rides in the verification fingerprint. The store-only assertions compile
//! everywhere; the native build/run demonstration of cached parity is gated on
//! `feature = "native"`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::DepGraph;
use prism::store::disk::{CommitStats, Store};
use prism::{commit_to_store, default_roots, dump, store_def_inputs, with_prelude, Config};

// A multi-definition program with a deliberate dependency chain. `main` calls
// `oc_top`, which calls `oc_mid` and `oc_leaf`; `oc_mid` calls `oc_leaf`. The
// `oc_` prefix keeps the names clear of any prelude definition. Every hash here
// is taken over pre-optimizer elaborated Core, the store's one identity regime,
// so the fixtures are unambiguous whatever the optimizer does.
const P_BASE: &str = r"fn oc_leaf(n : Int) : Int = n + 1
fn oc_mid(n : Int) : Int = oc_leaf(n) * 2
fn oc_top(n : Int) : Int =
  let m = oc_mid(n)
  m + oc_leaf(n)
fn main() = println(oc_top(3))
";

// Edit the leaf's body only: its hash moves, and so must every definition that
// transitively depends on it (`oc_mid`, `oc_top`, `main`).
const P_EDIT_LEAF: &str = r"fn oc_leaf(n : Int) : Int = n + 2
fn oc_mid(n : Int) : Int = oc_leaf(n) * 2
fn oc_top(n : Int) : Int =
  let m = oc_mid(n)
  m + oc_leaf(n)
fn main() = println(oc_top(3))
";

// Edit `oc_mid` only: `oc_leaf` is upstream and must be untouched; the closure is
// `{oc_mid, oc_top, main}`.
const P_EDIT_MID: &str = r"fn oc_leaf(n : Int) : Int = n + 1
fn oc_mid(n : Int) : Int = oc_leaf(n) * 3
fn oc_top(n : Int) : Int =
  let m = oc_mid(n)
  m + oc_leaf(n)
fn main() = println(oc_top(3))
";

// A local-binder rename (`m` becomes `doubled`) with the identical structure:
// alpha-normalization erases binder spelling, so no hash may move.
const P_RENAME_LOCAL: &str = r"fn oc_leaf(n : Int) : Int = n + 1
fn oc_mid(n : Int) : Int = oc_leaf(n) * 2
fn oc_top(n : Int) : Int =
  let doubled = oc_mid(n)
  doubled + oc_leaf(n)
fn main() = println(oc_top(3))
";

// The Merkle closure of these edits, by unqualified definition name.
const LEAF_CLOSURE: [&str; 4] = ["main", "oc_leaf", "oc_mid", "oc_top"];
const MID_CLOSURE: [&str; 3] = ["main", "oc_mid", "oc_top"];

// --- helpers -------------------------------------------------------------

// A unique scratch directory removed on drop; a test never touches the real user
// cache. Mirrors the pattern in `store_layout.rs`.
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
            "prism-oracle-{tag}-{}-{nanos}-{n}",
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

// The per-definition content hashes of a full (prelude-included) program, keyed
// by canonical name: exactly the surface `commit_to_store` keys the store on.
fn core_hashes(full: &str) -> BTreeMap<String, String> {
    dump("core-hash", full)
        .expect("core-hash dump")
        .lines()
        .filter_map(|l| {
            l.split_once("  ")
                .map(|(h, n)| (n.to_string(), h.to_string()))
        })
        .collect()
}

fn hashes_of(prog: &str) -> BTreeMap<String, String> {
    core_hashes(&with_prelude(prog))
}

// The names whose hash differs between two programs, unqualified.
fn moved_names(
    before: &BTreeMap<String, String>,
    after: &BTreeMap<String, String>,
) -> BTreeSet<String> {
    before
        .iter()
        .filter(|(name, hash)| after.get(*name) != Some(*hash))
        .map(|(name, _)| unqualified(name))
        .collect()
}

// The transitive dependents of `name` plus itself, unqualified: the Merkle
// closure a change to `name` must recompile, read from the pre-optimizer
// dependency graph the store's hashes are taken over (`store_def_inputs` is the
// same elaboration surface `commit_to_store` commits).
fn closure_of(prog: &str, name: &str) -> BTreeSet<String> {
    let (core, _, _) = store_def_inputs(&with_prelude(prog)).expect("store_def_inputs");
    let graph = DepGraph::of(&core);
    let matches = graph.resolve(name);
    assert_eq!(matches.len(), 1, "`{name}` is not a unique definition");
    let root = matches[0];
    let mut names: BTreeSet<String> = graph
        .dependents(root)
        .iter()
        .map(|s| unqualified(s.as_str()))
        .collect();
    names.insert(unqualified(name));
    names
}

fn unqualified(name: &str) -> String {
    name.rsplit(['.', '@']).next().unwrap_or(name).to_string()
}

fn expected(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| (*s).to_string()).collect()
}

// A store-committing config rooted at `root`, quiet so the summary line does not
// clutter test output.
fn store_cfg(root: PathBuf) -> Config {
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(root);
    cfg.flags.quiet = true;
    cfg
}

fn commit(prog: &str, cfg: &Config) -> CommitStats {
    commit_to_store(&with_prelude(prog), &default_roots(Path::new(".")), cfg)
        .expect("commit_to_store")
}

// --- (a) the changed set is exactly the Merkle closure -------------------

#[test]
fn an_edit_moves_exactly_the_definition_and_its_dependents() {
    let base = hashes_of(P_BASE);

    // Editing the leaf moves the leaf and everything downstream of it, and the
    // graph-derived closure agrees with the measured set of moved hashes.
    let moved = moved_names(&base, &hashes_of(P_EDIT_LEAF));
    assert_eq!(
        moved,
        closure_of(P_BASE, "oc_leaf"),
        "graph closure disagrees with moved set"
    );
    assert_eq!(
        moved,
        expected(&LEAF_CLOSURE),
        "editing oc_leaf must move its whole closure"
    );

    // Editing a middle definition leaves its upstream leaf untouched.
    let moved_mid = moved_names(&base, &hashes_of(P_EDIT_MID));
    assert_eq!(
        moved_mid,
        expected(&MID_CLOSURE),
        "editing oc_mid moved the wrong set"
    );
    assert!(
        !moved_mid.contains("oc_leaf"),
        "oc_leaf is upstream of oc_mid and must keep its hash"
    );
}

// --- (b) cold rebuild and incremental path emit identical artifacts ------

#[test]
fn cold_and_incremental_builds_emit_byte_identical_objects() {
    // Incremental store: commit the base program, then the edited one, reading
    // the store's own name index across the edit.
    let inc = TempDir::new("inc");
    let inc_cfg = store_cfg(inc.root());
    let inc_store = Store::open_or_create(inc.root()).unwrap();
    let first = commit(P_BASE, &inc_cfg);
    let before = inc_store.names().unwrap();
    let second = commit(P_EDIT_LEAF, &inc_cfg);
    let after = inc_store.names().unwrap();

    // The store rebound exactly the Merkle closure to new hashes and wrote one
    // object per moved definition; nothing outside the closure moved.
    let moved = moved_names(&before, &after);
    assert_eq!(
        moved,
        expected(&LEAF_CLOSURE),
        "incremental edit must rebind exactly the Merkle closure, rebound {moved:?}"
    );
    assert_eq!(
        second.objects_written,
        LEAF_CLOSURE.len(),
        "incremental build must write only the {}-def closure, wrote {second:?}",
        LEAF_CLOSURE.len()
    );
    assert_eq!(
        second.objects_written + second.objects_hit,
        first.objects_written + first.objects_hit,
        "the program has the same definition count cold and warm"
    );

    // Cold rebuild of the edited program into a fresh store.
    let cold = TempDir::new("cold");
    let cold_cfg = store_cfg(cold.root());
    commit(P_EDIT_LEAF, &cold_cfg);
    let cold_store = Store::open_or_create(cold.root()).unwrap();
    let cold_names = cold_store.names().unwrap();

    // The edited program resolves to the identical name-to-hash map whichever
    // path built it, and every stored object is byte-identical. This is the
    // content-addressed parity claim: same hash, same bytes, cold or incremental.
    assert_eq!(
        after, cold_names,
        "cold and incremental name->hash maps differ"
    );
    for hash in cold_names.values() {
        let a = inc_store.get(hash).expect("incremental object present");
        let b = cold_store.get(hash).expect("cold object present");
        assert_eq!(
            a, b,
            "object for hash {hash} differs between the incremental and cold builds"
        );
    }
}

#[cfg(feature = "native")]
#[test]
fn cold_and_incremental_builds_emit_identical_ir() {
    // The store is a passive cache: codegen never reads it, so an incremental
    // build (cache hits for the unchanged closure) must emit the identical
    // whole-program IR a cold build emits.
    use prism::emit_ir;
    let full = with_prelude(P_EDIT_LEAF);
    let cold = emit_ir(&full).expect("cold IR");
    let warm = emit_ir(&full).expect("warm IR");
    assert_eq!(cold, warm, "incremental build perturbed the emitted IR");
}

// --- (c) reformat and local rename are free ------------------------------

#[test]
fn reformatting_and_local_rename_move_no_hash_and_write_no_object() {
    let base = hashes_of(P_BASE);

    // A pure reformat, produced by the formatter itself (guaranteed to preserve
    // the AST), moves no hash.
    let reflow = prism::format(&with_prelude(P_BASE)).expect("format");
    assert_eq!(
        base,
        core_hashes(&reflow),
        "reformatting moved a content hash"
    );

    // Renaming a local binder moves no hash (alpha-normalization).
    assert_eq!(
        base,
        hashes_of(P_RENAME_LOCAL),
        "renaming a local moved a content hash"
    );

    // Committing either variant to a store already holding the original writes
    // zero new objects: identical hashes are cache hits.
    let tmp = TempDir::new("reflow");
    let cfg = store_cfg(tmp.root());
    let first = commit(P_BASE, &cfg);
    assert!(first.objects_written > 0, "cold commit wrote nothing");

    let roots = default_roots(Path::new("."));
    let again = commit_to_store(&reflow, &roots, &cfg).expect("commit reflow");
    assert_eq!(
        again.objects_written, 0,
        "a reformat must write zero new objects, wrote {again:?}"
    );
    let renamed = commit(P_RENAME_LOCAL, &cfg);
    assert_eq!(
        renamed.objects_written, 0,
        "a local rename must write zero new objects, wrote {renamed:?}"
    );
}

// --- verification caching: recorded parity is reused by hash -------------

// The program's identifying hash: the content hash of `main`, which transitively
// commits to everything `main` runs. A whole-program parity verdict is keyed by
// it, so a reformat (main's hash unchanged) reuses the verdict and a semantic
// edit (main's hash moved) re-runs.
fn main_hash(prog: &str) -> String {
    hashes_of(prog).get("main").expect("main hashed").clone()
}

#[cfg(feature = "native")]
mod cached_parity {
    use super::*;
    use std::cell::Cell;
    use std::process::Command;

    use prism::store::cert::{self, BACKEND_INTERP, BACKEND_LLVM};
    use prism::store::verify::{is_verified, record_pass, CheckKind, VerificationIdentity};

    // Build `prog` native, run it on empty stdin, and diff stdout against the
    // interpreter. Increments `builds` so a caller can prove whether the native
    // path actually ran.
    fn native_parity(prog: &str, builds: &Cell<u64>) -> Result<(), String> {
        builds.set(builds.get() + 1);
        let full = with_prelude(prog);
        let bin = std::env::temp_dir().join(format!(
            "prism_oracle_cached_{}_{}",
            std::process::id(),
            builds.get()
        ));
        let cfg = Config::default();
        prism::build_on(&full, &default_roots(Path::new(".")), &bin, &cfg)
            .map_err(|e| format!("build failed: {e}"))?;
        let out = Command::new(&bin)
            .output()
            .map_err(|e| format!("spawn: {e}"))?;
        let _ = fs::remove_file(&bin);
        let got = String::from_utf8_lossy(&out.stdout);
        let want = prism::interpret(&full)
            .map_err(|e| format!("interp: {e}"))?
            .term;
        if got == want {
            Ok(())
        } else {
            Err(format!("native {got:?} != interp {want:?}"))
        }
    }

    // The cached check: skip the native build when the program's hash already
    // carries a passing parity record, otherwise run and record the pass. Only
    // passes are recorded, so a failure always re-runs.
    fn checked(store: &Store, prog: &str, builds: &Cell<u64>) -> Result<(), String> {
        let hash = main_hash(prog);
        let artifact = Config::default().artifact_identity_for("llvm");
        let identity = VerificationIdentity::from_artifact(&artifact);
        if is_verified(store, &hash, CheckKind::Parity, &identity).unwrap() {
            return Ok(());
        }
        native_parity(prog, builds)?;
        record_pass(store, &hash, CheckKind::Parity, &identity).unwrap();
        // Alongside the verification record, emit the parity certificate the gate
        // stands behind: a `parity-passed` attestation keyed by the program's hash,
        // naming the two backends (interpreter and native LLVM) that agreed.
        cert::emit(
            store,
            &cert::parity_cert(&hash, (BACKEND_INTERP, BACKEND_LLVM)),
        )
        .unwrap();
        Ok(())
    }

    #[test]
    fn a_reformat_reuses_the_verdict_and_a_semantic_edit_reruns() {
        let tmp = TempDir::new("verify");
        let store = Store::open_or_create(tmp.root()).unwrap();
        let builds = Cell::new(0);

        // Cold: no record yet, so the native path runs once and records a pass.
        checked(&store, P_BASE, &builds).expect("base parity");
        assert_eq!(builds.get(), 1, "cold check should build once");

        // Rename a local: the hash is unchanged, so the recorded verdict is
        // reused with zero native rebuilds.
        assert_eq!(
            main_hash(P_BASE),
            main_hash(P_RENAME_LOCAL),
            "local rename moved the hash"
        );
        checked(&store, P_RENAME_LOCAL, &builds).expect("rename parity");
        assert_eq!(
            builds.get(),
            1,
            "a hash-preserving edit must not rebuild native"
        );

        // Semantic edit: the hash moves, so no record vouches for it and the
        // native path runs again.
        assert_ne!(
            main_hash(P_BASE),
            main_hash(P_EDIT_LEAF),
            "edit did not move the hash"
        );
        checked(&store, P_EDIT_LEAF, &builds).expect("edit parity");
        assert_eq!(builds.get(), 2, "a semantic edit must re-run native");
    }

    #[test]
    fn a_failure_is_never_cached() {
        let tmp = TempDir::new("nofailcache");
        let store = Store::open_or_create(tmp.root()).unwrap();
        // No record is written without a pass, so a hash that never verified is
        // not treated as verified.
        let hash = main_hash(P_BASE);
        let artifact = Config::default().artifact_identity_for("llvm");
        let identity = VerificationIdentity::from_artifact(&artifact);
        assert!(!is_verified(&store, &hash, CheckKind::Parity, &identity).unwrap());
    }

    #[test]
    fn a_toolchain_identity_change_retires_the_cached_verdict() {
        let tmp = TempDir::new("verifyid");
        let store = Store::open_or_create(tmp.root()).unwrap();
        let hash = main_hash(P_BASE);
        let llvm_artifact = Config::default().artifact_identity_for("llvm");
        let mlir_artifact = Config::default().artifact_identity_for("mlir");
        let llvm_identity = VerificationIdentity::from_artifact(&llvm_artifact);
        let mlir_identity = VerificationIdentity::from_artifact(&mlir_artifact);

        record_pass(&store, &hash, CheckKind::Parity, &llvm_identity).unwrap();
        assert!(is_verified(&store, &hash, CheckKind::Parity, &llvm_identity).unwrap());
        assert!(!is_verified(&store, &hash, CheckKind::Parity, &mlir_identity).unwrap());
    }

    #[test]
    fn a_source_root_identity_change_retires_the_cached_verdict() {
        let tmp = TempDir::new("verifyroot");
        let store = Store::open_or_create(tmp.root()).unwrap();
        let hash = main_hash(P_BASE);
        let first_artifact = Config::default()
            .artifact_identity_for("llvm")
            .with_source_root("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        let second_artifact = Config::default()
            .artifact_identity_for("llvm")
            .with_source_root("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
        let first_identity = VerificationIdentity::from_artifact(&first_artifact);
        let second_identity = VerificationIdentity::from_artifact(&second_artifact);

        record_pass(&store, &hash, CheckKind::Parity, &first_identity).unwrap();
        assert!(is_verified(&store, &hash, CheckKind::Parity, &first_identity).unwrap());
        assert!(!is_verified(&store, &hash, CheckKind::Parity, &second_identity).unwrap());
    }
}

// --- regime guard: commit and re-hash share one identity surface ---------

// Two programs the Core-to-Core tier demonstrably rewrites: a newtype whose
// wrapper mandatory erasure removes, and a `show` call default specialization
// resolves to a concrete Show dictionary. They were the empirical pre- vs
// post-optimizer divergence repros, so their committed and recomputed hashes
// disagree under any regime split and agree only when both hash pre-optimizer
// elaborated Core.
const P_NEWTYPE: &str = r"newtype Wrap = Wrap(Int)
fn unwrap(w : Wrap) : Int = match w of { Wrap(n) => n }
fn main() = println(unwrap(Wrap(41)))
";
const P_SHOW: &str = r"fn describe(n : Int) : String = show(n)
fn main() = println(describe(7))
";

// The store commit and the `store_def_inputs` re-hash front door must hash over
// the same surface, so every definition `store_def_inputs` recomputes names an
// object the commit actually wrote, even for an optimizer-touched program. If
// the commit ever hashed post-optimizer again while the re-hash stayed
// pre-optimizer, the recomputed hashes would name objects the store never wrote
// and this fails. It keeps the two sites to one regime so they can never silently
// fork again.
#[test]
fn store_commit_and_rehash_agree_for_optimizer_touched_programs() {
    for prog in [P_NEWTYPE, P_SHOW] {
        let full = with_prelude(prog);
        let (_, recomputed, _) = store_def_inputs(&full).expect("store_def_inputs");
        assert!(
            !recomputed.is_empty(),
            "the fixture produced no definitions"
        );

        let tmp = TempDir::new("regime");
        let cfg = store_cfg(tmp.root());
        commit_to_store(&full, &default_roots(Path::new(".")), &cfg).expect("commit_to_store");
        let store = Store::open_or_create(tmp.root()).unwrap();

        for (sym, hash) in &recomputed {
            assert!(
                store.get(hash).is_ok(),
                r"definition `{}` recomputes to pre-optimizer hash {hash}, which the store never committed: the commit regime has forked from store_def_inputs (both must hash pre-optimizer elaborated Core)",
                sym.as_str()
            );
        }
    }
}

// The namespace root names the exact program interface, not just its definition
// bodies: two programs that differ only in a public type's shape must have
// distinct namespace contracts. Folding definitions alone let `Token(Int)` and
// `Token(String)` share one contract, so a published root did not name the value
// schema under it.
#[test]
fn namespace_root_separates_types_of_different_shape() {
    let base = "pub type Token = Token(Int)\nfn main() = println(1)\n";
    let other = "pub type Token = Token(String)\nfn main() = println(1)\n";
    let roots = default_roots(Path::new("."));
    let a = prism::namespace_root(&with_prelude(base), &roots).expect("namespace root a");
    let b = prism::namespace_root(&with_prelude(other), &roots).expect("namespace root b");
    assert_ne!(
        a, b,
        "a public type's shape must move the namespace contract"
    );
}
