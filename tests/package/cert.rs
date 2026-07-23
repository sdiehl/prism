//! The minimal certificate: the `cert`-kind envelope, its gate emission into the
//! store, and the way `prism audit` reads it back.
//!
//! The one verifiable claim is `parity-passed`. Reserved claims such as
//! `Lean-checked` decode as recognized-but-unverifiable rather than as corruption.
//! Every decode is total.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::Digest;
use prism::core::HASH_SCHEME;
use prism::pkg::trust::{AuditReport, IndexRow, RootAudit, Verdict, INDEX_KIND_NAMESPACE};
use prism::store::cert::{
    check_cert, decode_cert, emit, encode_cert, parity_cert, Cert, CertStatus, Claim,
    BACKEND_INTERP, BACKEND_LLVM, CLAIM_LEAN_CHECKED,
};
use prism::store::disk::{Store, Written};
use prism::store::CodecError;
use rstest::rstest;

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
            origin: "demo".to_string(),
            name: "demo".to_string(),
            tag: "1.0".to_string(),
            root: Digest::from(subject),
            scheme: HASH_SCHEME.to_string(),
            kind: INDEX_KIND_NAMESPACE.to_string(),
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
        log_head: None,
    }
}

#[test]
fn the_envelope_round_trips() {
    let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
    let decoded = decode_cert(&encode_cert(&cert)).expect("decode");
    assert_eq!(decoded, cert);
    assert_eq!(decoded.subject.as_str(), SUBJECT);
    assert_eq!(decoded.claim, Claim::ParityPassed);
    assert_eq!(decoded.scheme, HASH_SCHEME);
    assert_eq!(decoded.backends, ("interp".to_string(), "llvm".to_string()));
}

#[derive(Clone, Copy, Debug)]
enum DecodeFailure {
    ForeignScheme,
    NonCertKind,
    TrailingBytes,
}

impl DecodeFailure {
    fn bytes(self) -> Vec<u8> {
        let cert = parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
        let mut bytes = encode_cert(&cert);
        match self {
            Self::ForeignScheme => {
                // The scheme tag is the first length-prefixed string; change its
                // first char so the scheme mismatch, not UTF-8, is caught.
                bytes[1] = b'X';
            }
            Self::NonCertKind => {
                // The kind varint sits right after the scheme string.
                bytes[1 + HASH_SCHEME.len()] = 0;
            }
            Self::TrailingBytes => bytes.push(0),
        }
        bytes
    }

    const fn want(self) -> CodecError {
        match self {
            Self::ForeignScheme => CodecError::Scheme,
            Self::NonCertKind => CodecError::Kind,
            Self::TrailingBytes => CodecError::TrailingBytes,
        }
    }
}

#[rstest]
fn malformed_cert_envelopes_are_rejected(
    #[values(
        DecodeFailure::ForeignScheme,
        DecodeFailure::NonCertKind,
        DecodeFailure::TrailingBytes
    )]
    case: DecodeFailure,
) {
    assert_eq!(decode_cert(&case.bytes()), Err(case.want()));
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

#[derive(Clone, Copy, Debug)]
enum AuditFailure {
    CorruptBytes,
    ForeignScheme,
    SubjectMismatch,
}

impl AuditFailure {
    const fn tag(self) -> &'static str {
        match self {
            Self::CorruptBytes => "audit-corrupt",
            Self::ForeignScheme => "audit-foreign",
            Self::SubjectMismatch => "audit-mismatch",
        }
    }

    const fn needle(self) -> &'static str {
        match self {
            Self::CorruptBytes => "corrupt",
            Self::ForeignScheme => "foreign scheme",
            Self::SubjectMismatch => "does not match",
        }
    }

    fn write(self, store: &Store) {
        match self {
            Self::CorruptBytes => {
                store.put_cert(SUBJECT, b"not a certificate").unwrap();
            }
            Self::ForeignScheme => {
                let foreign = Cert {
                    scheme: "prism-core-hash-v0".to_string(),
                    ..parity_cert(SUBJECT, (BACKEND_INTERP, BACKEND_LLVM))
                };
                store.put_cert(SUBJECT, &encode_cert(&foreign)).unwrap();
            }
            Self::SubjectMismatch => {
                // A certificate about OTHER_SUBJECT filed under SUBJECT's key: a
                // swap attack.
                let mismatched = parity_cert(OTHER_SUBJECT, (BACKEND_INTERP, BACKEND_LLVM));
                store.put_cert(SUBJECT, &encode_cert(&mismatched)).unwrap();
            }
        }
    }
}

#[rstest]
fn audit_rejects_bad_certificates(
    #[values(
        AuditFailure::CorruptBytes,
        AuditFailure::ForeignScheme,
        AuditFailure::SubjectMismatch
    )]
    case: AuditFailure,
) {
    let tmp = TempDir::new(case.tag());
    let store = tmp.store();
    case.write(&store);

    let status = check_cert(&store, SUBJECT);
    assert!(
        matches!(status, CertStatus::Failed(ref m) if m.contains(case.needle())),
        "{case:?}: {status:?}"
    );

    let rep = report(vec![green_row(SUBJECT, status)]);
    assert!(!rep.ok(), "{case:?} must fail the audit");
    assert!(rep.render().contains("cert: FAIL"));
}

#[test]
fn a_reserved_claim_decodes_as_recognized_but_unverifiable() {
    // A reserved claim such as Lean-checked uses the same envelope; a build that
    // cannot verify it must report it as recognized-but-unverifiable, not corrupt.
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
