// The standard-library fingerprint: one namespace root over every documented
// definition's behavior hash and every datatype/effect's shape digest, anchored
// in the generated docs. These check the core properties end to end: the
// root is reproducible, it is independent of the env-toggled optimizer, it covers
// the whole library (not a reachable subset), and it reaches the committed index
// page.

use std::sync::Mutex;

fn with_stdlib_hash_env_lock(test: impl FnOnce()) {
    static LOCK: Mutex<()> = Mutex::new(());
    let _guard = LOCK.lock().expect("stdlib hash env lock");
    test();
}

#[test]
fn root_is_reproducible() {
    with_stdlib_hash_env_lock(|| {
        let a = prism::stdlib_hash().expect("stdlib hash");
        let b = prism::stdlib_hash().expect("stdlib hash");
        assert_eq!(a.root, b.root);
        // A full BLAKE3 digest, not a truncation.
        assert_eq!(a.root.len(), 64);
        assert_eq!(a.scheme, "prism-core-hash-v1");
        assert_eq!(a.version, env!("CARGO_PKG_VERSION"));
    });
}

// The hash basis is pre-optimization Core, so a committed root must not depend on
// the `Specialize` pass, which the environment can toggle. This is the reason the
// anchor uses pre-opt Core rather than the post-opt `dump core-hash` basis.
#[test]
fn root_is_independent_of_the_optimizer_env() {
    with_stdlib_hash_env_lock(|| {
        let before = prism::stdlib_hash().expect("stdlib hash").root;
        std::env::set_var("PRISM_NO_SPECIALIZE", "1");
        let with = prism::stdlib_hash().expect("stdlib hash").root;
        std::env::remove_var("PRISM_NO_SPECIALIZE");
        assert_eq!(before, with);
    });
}

// The root must cover the whole documented surface: hundreds of functions across
// the prelude and every module, plus the core datatypes and effects as shapes.
#[test]
fn covers_the_whole_library() {
    with_stdlib_hash_env_lock(|| {
        let h = prism::stdlib_hash().expect("stdlib hash");
        assert!(
            h.defs.len() > 200,
            "only {} definitions hashed",
            h.defs.len()
        );
        for name in ["List", "Option", "Result", "Map", "Console", "FileSystem"] {
            assert!(
                h.shapes.contains_key(name),
                "missing shape digest for {name}"
            );
        }
        // Classes get an interface digest, instances an identity digest.
        for name in ["Eq", "Ord", "Show", "Functor", "Monad"] {
            assert!(
                h.classes.contains_key(name),
                "missing class digest for {name}"
            );
        }
        for name in ["eqBool", "ordInt", "functorList", "monadOption"] {
            assert!(
                h.instances.contains_key(name),
                "missing instance digest for {name}"
            );
        }
    });
}

// An instance's identity folds its method behavior hashes, so changing what a
// method does must move the instance digest. This checks the coherence seed.
#[test]
fn instance_digest_folds_method_behavior() {
    use std::collections::BTreeMap;
    let a = prism::core::instance_digest(
        "Eq",
        &prism::syntax::ast::Ty::Con("Bool".into(), vec![]),
        &BTreeMap::from([("eq".to_string(), prism::core::Digest::from("hash-one"))]),
    );
    let b = prism::core::instance_digest(
        "Eq",
        &prism::syntax::ast::Ty::Con("Bool".into(), vec![]),
        &BTreeMap::from([("eq".to_string(), prism::core::Digest::from("hash-two"))]),
    );
    assert_ne!(a, b);
}

// The fingerprint reaches the committed stdlib index page, and CI's existing
// `prism docs --stdlib --check` gate holds it there.
#[test]
fn index_page_carries_the_fingerprint() {
    with_stdlib_hash_env_lock(|| {
        let h = prism::stdlib_hash().expect("stdlib hash");
        let pages = prism::stdlib_pages().expect("stdlib pages");
        let index = pages
            .pages
            .iter()
            .find(|p| p.slug == "index")
            .expect("index page");
        assert!(
            index.markdown.contains(h.root.as_str()),
            "root missing from index"
        );
        assert!(
            index.markdown.contains("Merkle root"),
            "fingerprint card missing from index"
        );
        assert!(
            index.markdown.contains(&format!("Prism v{}", h.version)),
            "compiler version missing from index"
        );
    });
}
