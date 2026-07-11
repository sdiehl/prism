//! Store-level instance coherence: the canonical `(class, head) -> instance-hash`
//! binding written at commit, the cross-program conflict a divergent canonical
//! for one key raises, and the file-world guarantees this rests on (the
//! in-program undesignated overlap is already a hard error; the explicit
//! `using` escape hatch still typechecks).

use std::path::PathBuf;

use prism::store::coherence::is_representation_affecting;
use prism::store::disk::{CanonicalKey, Store};
use prism::{commit_to_store, default_roots, report, with_prelude, Config};

use crate::support::TempDir;

// A config that commits to `root` instead of the real cache.
fn cfg_at(root: PathBuf) -> Config {
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(root);
    cfg
}

// A single-instance program for a fresh class over `Int`; the instance is
// canonical automatically. `body` is the `rankOf` method body, so two programs
// with different bodies produce different instance identities.
fn rank_program(body: &str) -> String {
    with_prelude(&format!(
        r"class Rank(a)
  rankOf : (a) -> Int
instance rankInt : Rank(Int)
  fn rankOf(x) = {body}
"
    ))
}

#[test]
fn canonical_binding_is_written_on_commit() {
    let tmp = TempDir::new("coherence", "written");
    let cfg = cfg_at(tmp.store_root());
    let roots = default_roots(std::path::Path::new("."));

    commit_to_store(&rank_program("x"), &roots, &cfg).unwrap();

    let store = Store::open_or_create(tmp.store_root()).unwrap();
    // The program's own class binds its sole instance as canonical.
    let rank = store
        .canonical(&CanonicalKey {
            class: "Rank".into(),
            head: "Int".into(),
        })
        .unwrap();
    assert!(rank.is_some(), "Rank(Int) canonical binding not written");
    // The prelude's canonical instances are bound too (Ord(Int) is one).
    let ord = store
        .canonical(&CanonicalKey {
            class: "Ord".into(),
            head: "Int".into(),
        })
        .unwrap();
    assert!(
        ord.is_some(),
        "prelude Ord(Int) canonical binding not written"
    );
}

#[test]
fn same_hash_recommit_is_a_noop() {
    let tmp = TempDir::new("coherence", "noop");
    let cfg = cfg_at(tmp.store_root());
    let roots = default_roots(std::path::Path::new("."));
    let src = rank_program("x");

    commit_to_store(&src, &roots, &cfg).unwrap();
    let key = CanonicalKey {
        class: "Rank".into(),
        head: "Int".into(),
    };
    let first = Store::open_or_create(tmp.store_root())
        .unwrap()
        .canonical(&key)
        .unwrap();

    // Committing the identical program again is not a conflict and does not move
    // the binding.
    commit_to_store(&src, &roots, &cfg).unwrap();
    let second = Store::open_or_create(tmp.store_root())
        .unwrap()
        .canonical(&key)
        .unwrap();
    assert_eq!(first, second);
    assert!(first.is_some());
}

#[test]
fn conflicting_canonical_designation_errors_naming_both_hashes() {
    let tmp = TempDir::new("coherence", "conflict");
    let cfg = cfg_at(tmp.store_root());
    let roots = default_roots(std::path::Path::new("."));

    // Program A binds Rank(Int) to the identity of `rankOf(x) = x`.
    commit_to_store(&rank_program("x"), &roots, &cfg).unwrap();
    let existing = Store::open_or_create(tmp.store_root())
        .unwrap()
        .canonical(&CanonicalKey {
            class: "Rank".into(),
            head: "Int".into(),
        })
        .unwrap()
        .expect("program A must have bound Rank(Int)");

    // Program B is the same shape but a different instance body, so a different
    // canonical instance for the same key: a hard cross-program conflict.
    let src_b = rank_program("0 - x");
    let err = commit_to_store(&src_b, &roots, &cfg)
        .expect_err("a divergent canonical for Rank(Int) must be refused");

    let msg = err.to_string();
    assert!(
        msg.contains("coherence conflict for Rank(Int)"),
        "message must name the class and head: {msg}"
    );
    assert!(
        msg.contains(&existing),
        "message must name the already-committed hash {existing}: {msg}"
    );
    assert!(
        msg.contains("re-designate"),
        "message must state the remedy: {msg}"
    );
    // The incoming hash is named too, distinct from the existing one: the message
    // carries two different hex identities.
    let hashes: std::collections::BTreeSet<&str> = msg
        .split(|c: char| !c.is_ascii_hexdigit())
        .filter(|t| t.len() == existing.len())
        .collect();
    assert!(
        hashes.len() >= 2,
        "message must name both the existing and the incoming hash: {msg}"
    );

    // The rejected commit leaves the original binding intact.
    let after = Store::open_or_create(tmp.store_root())
        .unwrap()
        .canonical(&CanonicalKey {
            class: "Rank".into(),
            head: "Int".into(),
        })
        .unwrap();
    assert_eq!(after.as_deref(), Some(existing.as_str()));

    // The error carries a caret at the offending declaration.
    let rendered = err.render_plain(&src_b, "program-b");
    assert!(
        rendered.contains("╭─"),
        "conflict must render with a caret: {rendered}"
    );
}

#[test]
fn in_program_undesignated_overlap_is_a_hard_error() {
    // Two instances for one head with no `canonical` designation is a hard error
    // at definition (the file-world coherence rule the store lifts across
    // programs), rendered with a caret.
    let src = r"class Ord(a)
  cmp : (a, a) -> Int
instance ordA : Ord(Int)
  fn cmp(x, y) = 0
instance ordB : Ord(Int)
  fn cmp(x, y) = 1
fn main() = cmp(1, 2)
";
    let out = report(src);
    assert!(
        out.contains("2 instances for Ord(Int)"),
        "undesignated overlap must be an error: {out}"
    );
    assert!(
        out.contains("╭─"),
        "the error must render with a caret: {out}"
    );
}

#[test]
fn explicit_dictionary_escape_hatch_still_typechecks() {
    // A second instance stays legal when one is designated canonical; the other
    // is reachable only through an explicit `using` override. This is the escape
    // hatch the store's coherence must not break.
    let src = r"class Ord(a)
  cmp : (a, a) -> Int
instance ordA : Ord(Int)
  fn cmp(x, y) = 0
instance ordB : Ord(Int)
  fn cmp(x, y) = 1
canonical Ord(Int) = ordA
fn pick(x : a, y : a) : Int given Ord(a) = cmp(x, y)
fn main() : Int = pick(1, 2, using ordB)
";
    let out = report(src);
    assert!(
        !out.contains("Type Error"),
        "the explicit-dictionary escape hatch must still typecheck: {out}"
    );
}

#[test]
fn representation_affecting_classes_are_reserved() {
    // The reserved classification the later cross-program reification will read:
    // Ord and Hash affect representation; Show and Functor do not.
    assert!(is_representation_affecting("Ord"));
    assert!(is_representation_affecting("Hash"));
    assert!(!is_representation_affecting("Show"));
    assert!(!is_representation_affecting("Functor"));
}
