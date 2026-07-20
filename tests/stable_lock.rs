//! The content-addressed lock manifest for stable migrations.
//!
//! A locked `auto` migration is pinned by its rung, edge, and route identities.
//! These tests prove the binding rule: a locked family re-verifies clean, a
//! changed generated behavior is a hard drift error, the identities are a pure
//! function of the source (deterministic and idempotent), and changing one rung's
//! default moves precisely the edges and routes that cross it.

use std::path::Path;

use prism::stable_lock::{edge_hash, LockManifest};
use prism::Root;

// A three-rung additive family, every route `auto`. Purely additive so `auto`
// derives both directions of every edge.
const BASE: &str = r#"
import Wire (..)

stable Save {
  V1 = { hero: String, depth: Int },
  V2 = { ..V1, fog: Int = 30 },
  V3 = { ..V2, mist: Int = 5 },
  migrations {
    V1 -> V2 = auto
    V2 -> V3 = auto
    V1 -> V3 = auto
  }
}

fn main() = println("ok")
"#;

// The same family with the `V1 -> V2` upgrade default changed. The default rides
// in the upgrade hash, so this moves the `V1 -> V2` edge and the `V1 -> V3` route.
const DRIFT: &str = r#"
import Wire (..)

stable Save {
  V1 = { hero: String, depth: Int },
  V2 = { ..V1, fog: Int = 99 },
  V3 = { ..V2, mist: Int = 5 },
  migrations {
    V1 -> V2 = auto
    V2 -> V3 = auto
    V1 -> V3 = auto
  }
}

fn main() = println("ok")
"#;

// The same family with only the `V2 -> V3` upgrade default changed. This moves the
// `V2 -> V3` edge and the `V1 -> V3` route, but must leave `V1 -> V2` untouched.
const UNRELATED: &str = r#"
import Wire (..)

stable Save {
  V1 = { hero: String, depth: Int },
  V2 = { ..V1, fog: Int = 30 },
  V3 = { ..V2, mist: Int = 7 },
  migrations {
    V1 -> V2 = auto
    V2 -> V3 = auto
    V1 -> V3 = auto
  }
}

fn main() = println("ok")
"#;

fn roots() -> Vec<Root> {
    vec![Root::Embedded(prism::stdlib::STDLIB)]
}

fn derive(src: &str) -> LockManifest {
    prism::driver::stable_lock::derive(&prism::with_prelude(src), &roots())
        .expect("derive lock manifest")
}

// A locked family re-verifies clean against the manifest derived from the same
// source, and its migration surface is actually recorded.
#[test]
fn locked_family_reverifies_clean() {
    let manifest = derive(BASE);
    let save = manifest.families.get("Save").expect("Save is locked");
    assert_eq!(save.rungs.len(), 3, "three rung shapes");
    assert_eq!(save.edges.len(), 2, "two adjacent edges");
    assert_eq!(save.routes.len(), 1, "one composed V1 -> V3 route");
    prism::driver::stable_lock::verify(&prism::with_prelude(BASE), &roots(), &manifest)
        .expect("the family that produced the manifest re-verifies clean");
}

// Deriving twice produces byte-identical manifests: the identities are a pure
// function of the source, so a second lock is idempotent.
#[test]
fn derivation_is_deterministic_and_idempotent() {
    let first = derive(BASE).to_text().expect("serialize");
    let second = derive(BASE).to_text().expect("serialize");
    assert_eq!(first, second, "a re-derivation is byte-identical");

    // Every recorded edge identity recomputes from its family, shape digests, and
    // component hashes, so the identity does not depend on how it was assembled.
    let manifest = derive(BASE);
    let save = &manifest.families["Save"];
    for edge in &save.edges {
        let from = save.rungs.iter().find(|r| r.ver == edge.from).unwrap();
        let to = save.rungs.iter().find(|r| r.ver == edge.to).unwrap();
        assert_eq!(
            edge.edge,
            edge_hash(
                "Save",
                &from.shape,
                &to.shape,
                &edge.upgrade,
                &edge.downgrade
            ),
            "edge {} -> {} recomputes from its inputs",
            edge.from,
            edge.to
        );
    }
}

// A changed generated behavior fails against the committed manifest with the
// dedicated lock-drift code, naming the family and the drifted edge.
#[test]
fn changed_generated_behavior_is_lock_drift() {
    let locked = derive(BASE);
    let err = prism::driver::stable_lock::verify(&prism::with_prelude(DRIFT), &roots(), &locked)
        .expect_err("a changed auto migration must drift");
    assert_eq!(err.code().as_str(), "E6067", "the stable-lock-drift code");
    let text = err.to_string();
    assert!(
        text.contains("Save") && text.contains("V1 -> V2"),
        "the drift names the family and the changed edge: {text}"
    );
}

// Changing one rung's default moves precisely the edges and routes that cross it.
// The `V2 -> V3` default change moves that edge and the composed `V1 -> V3` route,
// but leaves the `V1 -> V2` edge identity untouched.
#[test]
fn drift_is_scoped_to_crossing_edges() {
    let base = derive(BASE);
    let changed = derive(UNRELATED);
    let base_save = &base.families["Save"];
    let changed_save = &changed.families["Save"];

    let base_v1v2 = base_save.edges.iter().find(|e| e.to == "V2").unwrap();
    let changed_v1v2 = changed_save.edges.iter().find(|e| e.to == "V2").unwrap();
    assert_eq!(
        base_v1v2.edge, changed_v1v2.edge,
        "the untouched V1 -> V2 edge keeps its identity"
    );

    let base_v2v3 = base_save.edges.iter().find(|e| e.to == "V3").unwrap();
    let changed_v2v3 = changed_save.edges.iter().find(|e| e.to == "V3").unwrap();
    assert_ne!(
        base_v2v3.edge, changed_v2v3.edge,
        "the changed V2 -> V3 edge moves"
    );

    assert_ne!(
        base_save.routes[0].route, changed_save.routes[0].route,
        "the composed V1 -> V3 route crosses V2 -> V3, so it moves too"
    );

    // Verifying the changed source against the base manifest is a drift.
    prism::driver::stable_lock::verify(&prism::with_prelude(UNRELATED), &roots(), &base)
        .expect_err("a downstream default change drifts the locked route");
}

// A family with no `migrations` table is not lockable, so it never enters the
// manifest and is never checked, exactly as an unfrozen rung is not checked.
#[test]
fn family_without_migrations_is_not_locked() {
    const NO_TABLE: &str = r#"
import Wire (..)

stable Save {
  V1 = { hero: String, depth: Int },
  V2 = { ..V1, fog: Int = 30 }
}

fn main() = println("ok")
"#;
    assert!(
        derive(NO_TABLE).is_empty(),
        "a family with no migrations table is not locked"
    );
}

// The committed on-disk fixture manifest is current: re-deriving `save.pr`
// reproduces the exact bytes beside it, and the family verifies clean through the
// committed file. A future compiler change that legitimately moves these hashes
// reseats the golden with `prism store lock --accept`.
#[test]
fn committed_fixture_manifest_is_current() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/stable_lock");
    let source = dir.join("save.pr");
    let src = std::fs::read_to_string(&source).expect("read save.pr");
    let full = prism::with_prelude(&src);
    let committed = prism::driver::stable_lock::read_committed(&source)
        .expect("read committed manifest")
        .expect("save.pr.stable-lock is committed beside save.pr");
    let derived = prism::driver::stable_lock::derive(&full, &roots()).expect("derive");
    assert_eq!(
        derived.to_text().expect("serialize"),
        committed.to_text().expect("serialize"),
        "the committed manifest is current; reseat with `prism store lock --accept`"
    );
    prism::driver::stable_lock::verify(&full, &roots(), &committed)
        .expect("the committed fixture verifies clean");
}
