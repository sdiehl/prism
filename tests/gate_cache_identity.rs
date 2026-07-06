mod common;

use common::{artifact_identity_context, cache_key_with_identity, GateCacheIdentity};

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
