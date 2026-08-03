use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use crate::support::{
    artifact_identity_context, cache_key_with_identity, GateCacheIdentity, COMPILED_FEATURES,
    DEFAULT_FEATURE,
};

/// The feature names the root manifest declares. Hand-read rather than parsed
/// with a toml crate: the `[features]` table is one flat block of `name = [...]`
/// rows, and a key line is exactly a line with an identifier before its first
/// `=` (a continuation line inside a value carries no `=`).
fn manifest_features() -> BTreeSet<String> {
    let manifest_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let manifest = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", manifest_path.display()));
    let mut out = BTreeSet::new();
    let mut in_features = false;
    for line in manifest.lines() {
        let line = line.trim();
        if line.starts_with('[') {
            in_features = line == "[features]";
            continue;
        }
        if !in_features || line.starts_with('#') {
            continue;
        }
        let Some((key, _)) = line.split_once('=') else {
            continue;
        };
        let key = key.trim();
        let identifier = !key.is_empty()
            && key
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
        if identifier {
            out.insert(key.to_string());
        }
    }
    out
}

// A feature added to the manifest without a row in `COMPILED_FEATURES` would let
// two builds that differ only in it share one cache identity, and one build's
// verdicts would be served to the other. The identity is only total over the
// feature set if this holds.
#[test]
fn feature_identity_covers_every_cargo_feature() {
    let declared: BTreeSet<String> = manifest_features()
        .into_iter()
        .filter(|name| name != DEFAULT_FEATURE)
        .collect();
    let covered: BTreeSet<String> = COMPILED_FEATURES
        .iter()
        .map(|(name, _)| (*name).to_string())
        .collect();
    assert_eq!(
        declared, covered,
        "the gate cache identity must name every cargo feature: add the missing one to COMPILED_FEATURES (tests/support/mod.rs)"
    );
}

// Every feature contributes its own on/off cell, so no two feature
// configurations can render the same identity.
#[test]
fn feature_identity_names_every_feature_state() {
    let context = artifact_identity_context();
    for (name, enabled) in COMPILED_FEATURES {
        assert!(context.contains(&format!("{name}={enabled}")), "{context}");
    }
}

#[test]
fn gate_cache_key_names_backend_tag() {
    let full = "fn main() = 1\n";
    let identity = GateCacheIdentity::for_test("same-compiler");
    assert_ne!(
        cache_key_with_identity(full, "llvm", &identity),
        cache_key_with_identity(full, "mlir", &identity)
    );
}

#[test]
fn gate_cache_key_names_artifact_identity_context() {
    let full = "fn main() = 1\n";
    assert_ne!(
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-a\0target-a\0flags-a")
        ),
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-b\0target-a\0flags-a")
        )
    );
    assert_ne!(
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-a\0target-a\0flags-a")
        ),
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-a\0target-b\0flags-a")
        )
    );
    assert_ne!(
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-a\0target-a\0flags-a")
        ),
        cache_key_with_identity(
            full,
            "llvm",
            &GateCacheIdentity::for_test("scheme-a\0target-a\0flags-b")
        )
    );
}

#[test]
fn artifact_identity_context_carries_scheme_target_and_flags() {
    let context = artifact_identity_context();
    assert!(context.contains("hash-scheme="));
    assert!(context.contains("target="));
    assert!(context.contains("PRISM_BACKEND_OPT="));
    assert!(context.contains("PRISM_EFFECT_TIER="));
}
