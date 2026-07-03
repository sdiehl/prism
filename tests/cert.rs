//! The minimal certificate: the `cert`-kind envelope, its gate emission into the
//! store, and the way `prism audit` reads it back.
//!
//! The one live claim is `parity-passed`; the envelope shape is reserved for future
//! rungs (Lean-checked and beyond), so a reserved claim must decode as
//! recognized-but-unverifiable rather than as corruption. Every decode is total.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::HASH_SCHEME;
use prism::pkg::trust::{AuditReport, IndexRow, RootAudit, Verdict};
use prism::store::cert::{
    check_cert, decode_cert, emit, encode_cert, parity_cert, Cert, CertStatus, Claim,
    BACKEND_INTERP, BACKEND_LLVM, CLAIM_LEAN_CHECKED,
};
use prism::store::disk::{Store, Written};
use prism::store::CodecError;

// A unique scratch directory removed on drop, mirroring the store test harnesses.
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
            "prism-cert-{tag}-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn store(&self) -> Store {
        Store::open_or_create(self.path.join("store")).unwrap()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// A syntactically valid content-hash stand-in: hex, wider than the shard prefix.
const SUBJECT: &str = "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b";
const OTHER_SUBJECT: &str = "60303ae22b998861bce3b28f33eec1be758a213c";

// A locked-root audit row for `subject` carrying `cert`, otherwise green.
fn green_row(subject: &str, cert: CertStatus) -> RootAudit {
    RootAudit {
        pointer: IndexRow {
            name: "demo".to_string(),
            tag: "1.0".to_string(),
            root: subject.to_string(),
        },
        outcome: Ok(1),
        cert,
    }
}

const fn report(rows: Vec<RootAudit>) -> AuditReport {
    AuditReport {
        verdict: Verdict::Unsigned,
        rows,
        repoints: Vec::new(),
    }
}

#[test]
fn the_envelope_round_trips() {
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let decoded = decode_cert(&encode_cert(&cert)).expect("decode");
    assert_eq!(decoded, cert);
    assert_eq!(decoded.subject, SUBJECT);
    assert_eq!(decoded.claim, Claim::ParityPassed);
    assert_eq!(decoded.scheme, HASH_SCHEME);
    assert_eq!(decoded.backends, ("interp".to_string(), "llvm".to_string()));
}

#[test]
fn a_foreign_scheme_is_rejected_before_the_body() {
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let mut bytes = encode_cert(&cert);
    // The scheme tag is the first length-prefixed string; change its first char to
    // a different valid one, so the scheme mismatch (not a UTF-8 fault) is caught.
    bytes[1] = b'X';
    assert_eq!(decode_cert(&bytes), Err(CodecError::Scheme));
}

#[test]
fn a_non_cert_kind_is_rejected() {
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let mut bytes = encode_cert(&cert);
    // The kind varint sits right after the scheme string (1 length byte + tag).
    let kind_pos = 1 + HASH_SCHEME.len();
    bytes[kind_pos] = 0; // WireKind::Value
    assert_eq!(decode_cert(&bytes), Err(CodecError::Kind));
}

#[test]
fn trailing_bytes_are_rejected() {
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let mut bytes = encode_cert(&cert);
    bytes.push(0);
    assert_eq!(decode_cert(&bytes), Err(CodecError::TrailingBytes));
}

#[test]
fn hostile_bytes_never_panic() {
    assert!(decode_cert(&[]).is_err());
    assert!(decode_cert(&[0xff]).is_err());
    // A truncated envelope: the header alone, no body.
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let full = encode_cert(&cert);
    for cut in 0..full.len() {
        // Every prefix decodes to an error, never a panic (and never the full cert).
        assert_ne!(decode_cert(&full[..cut]).ok().as_ref(), Some(&cert));
    }
}

#[test]
fn the_gate_emits_exactly_one_cert_and_reruns_are_idempotent() {
    let tmp = TempDir::new("emit");
    let store = tmp.store();
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));

    assert_eq!(emit(&store, &cert).unwrap(), Written::New);
    assert!(store.has_cert(SUBJECT));
    // A re-run writes nothing: the certificate is idempotent under a fixed toolchain.
    assert_eq!(emit(&store, &cert).unwrap(), Written::Hit);

    let stored = store.get_cert(SUBJECT).unwrap().expect("cert present");
    assert_eq!(decode_cert(&stored).unwrap(), cert);
}

#[test]
fn a_conflicting_certificate_for_a_subject_is_refused() {
    let tmp = TempDir::new("immutable");
    let store = tmp.store();
    emit(
        &store,
        &parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM)),
    )
    .unwrap();
    // Different bytes for the same subject are corruption, never a silent overwrite.
    assert!(store.put_cert(SUBJECT, b"a different certificate").is_err());
}

#[test]
fn attest_emits_then_reuses() {
    let tmp = TempDir::new("attest");
    let store = tmp.store();
    // The attest path's second backend is native LLVM against the interpreter.
    let cert = parity_cert(SUBJECT, (BACKEND_LLVM, "interpreter"));
    assert_eq!(emit(&store, &cert).unwrap(), Written::New);
    assert_eq!(emit(&store, &cert).unwrap(), Written::Hit);
}

#[test]
fn audit_verifies_and_prints_the_certificate() {
    let tmp = TempDir::new("audit-ok");
    let store = tmp.store();
    emit(
        &store,
        &parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM)),
    )
    .unwrap();

    let status = check_cert(&store, SUBJECT);
    let CertStatus::Verified(desc) = &status else {
        panic!("expected a verified certificate, got {status:?}");
    };
    assert!(desc.contains("parity-passed"), "description: {desc}");

    let rep = report(vec![green_row(SUBJECT, status)]);
    assert!(rep.ok());
    let rendered = rep.render();
    assert!(
        rendered.contains("cert: parity-passed"),
        "render:\n{rendered}"
    );
}

#[test]
fn an_absent_certificate_is_not_a_failure() {
    let tmp = TempDir::new("absent");
    let store = tmp.store();
    assert_eq!(check_cert(&store, SUBJECT), CertStatus::Absent);
    let rep = report(vec![green_row(SUBJECT, CertStatus::Absent)]);
    assert!(rep.ok());
    // No certificate annotation is printed when none exists.
    assert!(!rep.render().contains("cert:"));
}

#[test]
fn audit_rejects_a_corrupt_certificate_naming_the_corruption() {
    let tmp = TempDir::new("audit-corrupt");
    let store = tmp.store();
    // Store bytes that are not a certificate at all under the subject's key.
    store.put_cert(SUBJECT, b"not a certificate").unwrap();

    let status = check_cert(&store, SUBJECT);
    assert!(
        matches!(status, CertStatus::Failed(ref m) if m.contains("corrupt")),
        "status: {status:?}"
    );

    let rep = report(vec![green_row(SUBJECT, status)]);
    assert!(!rep.ok(), "a corrupt certificate must fail the audit");
    assert!(rep.render().contains("cert: FAIL"));
}

#[test]
fn audit_rejects_a_foreign_scheme_certificate() {
    let tmp = TempDir::new("audit-foreign");
    let store = tmp.store();
    let foreign = Cert {
        scheme: "prism-core-hash-v0".to_string(),
        ..parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM))
    };
    store.put_cert(SUBJECT, &encode_cert(&foreign)).unwrap();

    let status = check_cert(&store, SUBJECT);
    assert!(
        matches!(status, CertStatus::Failed(ref m) if m.contains("foreign scheme")),
        "status: {status:?}"
    );
}

#[test]
fn audit_rejects_a_certificate_whose_subject_does_not_match() {
    let tmp = TempDir::new("audit-mismatch");
    let store = tmp.store();
    // A certificate about OTHER_SUBJECT filed under SUBJECT's key: a swap attack.
    let mismatched = parity_cert(OTHER_SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    store.put_cert(SUBJECT, &encode_cert(&mismatched)).unwrap();

    let status = check_cert(&store, SUBJECT);
    assert!(
        matches!(status, CertStatus::Failed(ref m) if m.contains("does not match")),
        "status: {status:?}"
    );
}

#[test]
fn a_reserved_claim_decodes_as_recognized_but_unverifiable() {
    // A future rung's claim (Lean-checked) rides the same envelope; an old build
    // must read it as a recognized-but-unverifiable certificate, not corruption.
    let reserved = Cert {
        claim: Claim::Reserved(CLAIM_LEAN_CHECKED),
        ..parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM))
    };
    let decoded = decode_cert(&encode_cert(&reserved)).expect("reserved decodes");
    assert_eq!(decoded.claim, Claim::Reserved(CLAIM_LEAN_CHECKED));

    let tmp = TempDir::new("reserved");
    let store = tmp.store();
    store.put_cert(SUBJECT, &encode_cert(&reserved)).unwrap();
    let status = check_cert(&store, SUBJECT);
    let CertStatus::Unverifiable(desc) = &status else {
        panic!("expected recognized-but-unverifiable, got {status:?}");
    };
    assert!(desc.contains("lean-checked"), "description: {desc}");

    // A reserved certificate is not a failure: the audit still passes.
    let rep = report(vec![green_row(SUBJECT, status)]);
    assert!(rep.ok());
    assert!(rep.render().contains("[unverifiable]"));
}
