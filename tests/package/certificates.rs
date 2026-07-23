//! Lineage certificate slots: the two facts `lineage verify` can persist as a
//! digest-named artifact over a sidecar's own digest.
//!
//! The library cases pin the envelope: both live claims round-trip, a reserved
//! claim decodes as recognized-but-untrusted (an old build reads a newer claim
//! without mistaking it for corruption), and a subject-digest mismatch is a named
//! failure. The subprocess cases drive `prism lineage verify --certify` and
//! `prism lineage check-cert` end to end: a recorded run mints a `replay-verified`
//! certificate and a plain rehash mints a `lineage-verified` one, tampering the
//! sidecar fails the check naming the digest mismatch, and an unknown-claim
//! certificate is rejected rather than silently accepted.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::Digest;
use prism::core::HASH_SCHEME;
use prism::lineage::provenance::{sha256_hex, EVENT_HASH_SCHEME};
use prism::store::cert::{
    check_lineage_cert, decode_lineage_cert, encode_lineage_cert, lineage_cert, replay_cert,
    CertRow, CertStatus, LineageCert, LineageClaim,
};

// A program that observes one file input, so a recorded run has an input-file node
// to rehash for the lineage-verified certificate and a trace to replay for the
// replay-verified one.
const PROGRAM: &str = "fn main() : Unit ! {IO} =\n  \
    let cfg = read_file(\"input.json\")\n  \
    println(\"cfg={cfg}\")\n";

// The sidecar digest a certificate vouches for, computed exactly as the compiler
// does so the tests speak the same subject spelling as the tool.
fn subject_of(bytes: &[u8]) -> String {
    format!("{EVENT_HASH_SCHEME}:{}", sha256_hex(bytes))
}

// ------------------------------ library cases ------------------------------

#[test]
fn both_live_claims_round_trip() {
    let subject = subject_of(b"a sidecar");
    let replay = replay_cert(&subject, "sha256:abc", "fp-1", 3, 12, 1);
    assert_eq!(
        decode_lineage_cert(&encode_lineage_cert(&replay)).unwrap(),
        replay
    );
    assert_eq!(replay.claim, LineageClaim::ReplayVerified);

    let rehash = lineage_cert(&subject, "fp-1", 4, 2);
    assert_eq!(
        decode_lineage_cert(&encode_lineage_cert(&rehash)).unwrap(),
        rehash
    );
    assert_eq!(rehash.claim, LineageClaim::LineageVerified);
}

#[test]
fn a_recognized_claim_over_its_subject_verifies() {
    let bytes = b"the sidecar bytes";
    let subject = subject_of(bytes);
    let cert = encode_lineage_cert(&replay_cert(&subject, "sha256:abc", "fp", 1, 1, 1));
    let CertStatus::Verified(desc) = check_lineage_cert(&cert, &subject) else {
        panic!("a recognized claim over its subject must verify");
    };
    assert!(desc.contains("replay-verified"), "description: {desc}");
}

#[test]
fn a_subject_mismatch_is_a_named_failure() {
    // A certificate minted over one sidecar, checked against another's digest: the
    // tamper case, at the library level.
    let cert = encode_lineage_cert(&lineage_cert(&subject_of(b"original"), "fp", 1, 0));
    let status = check_lineage_cert(&cert, &subject_of(b"tampered"));
    let CertStatus::Failed(reason) = status else {
        panic!("a subject mismatch must fail");
    };
    assert!(reason.contains("digest mismatch"), "reason: {reason}");
}

#[test]
fn a_reserved_claim_is_recognized_but_untrusted() {
    // A reserved claim uses the same envelope; a build that cannot verify it must
    // report it as recognized-but-untrusted, not corrupt.
    let subject = subject_of(b"sidecar");
    let reserved = LineageCert {
        subject: Digest::from(subject.clone()),
        claim: LineageClaim::Reserved(99),
        scheme: HASH_SCHEME.to_string(),
        compiler: "future".to_string(),
        evidence: vec![CertRow {
            key: "unknown".to_string(),
            value: "1".to_string(),
        }],
    };
    let bytes = encode_lineage_cert(&reserved);
    assert_eq!(decode_lineage_cert(&bytes).unwrap(), reserved);
    let CertStatus::Unverifiable(desc) = check_lineage_cert(&bytes, &subject) else {
        panic!("a reserved claim must be recognized-but-untrusted");
    };
    assert!(desc.contains("not recognized"), "description: {desc}");
}

#[test]
fn hostile_bytes_never_panic() {
    assert!(decode_lineage_cert(&[]).is_err());
    assert!(decode_lineage_cert(&[0xff]).is_err());
    let full = encode_lineage_cert(&lineage_cert(&subject_of(b"x"), "fp", 1, 0));
    for cut in 0..full.len() {
        // Every prefix decodes to an error, never a panic.
        assert!(decode_lineage_cert(&full[..cut]).is_err());
    }
}

// ------------------------------ subprocess cases ---------------------------

const fn prism_bin() -> &'static str {
    env!("CARGO_BIN_EXE_prism")
}

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
            "prism-certificates-{tag}-{}-{nanos}-{n}",
            process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// Record a run of PROGRAM in `dir`, leaving `run.plineage` and `run.replay` beside
// its input. The recorded run is the fixture both certificate kinds ride over.
fn record(dir: &Path) {
    fs::write(dir.join("pipe.pr"), PROGRAM).unwrap();
    fs::write(dir.join("input.json"), "{\"t\": 5}").unwrap();
    let output = Command::new(prism_bin())
        .current_dir(dir)
        .args([
            "run",
            "pipe.pr",
            "--record",
            "run.replay",
            "--lineage",
            "run.plineage",
        ])
        .output()
        .expect("runs prism run --record --lineage");
    assert!(
        output.status.success(),
        "record stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

// Run a `prism lineage` subcommand in `dir`, returning (success, stdout, stderr).
fn lineage(dir: &Path, args: &[&str]) -> (bool, String, String) {
    let output = Command::new(prism_bin())
        .current_dir(dir)
        .arg("lineage")
        .args(args)
        .output()
        .expect("runs prism lineage");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn replay_verified_certificate_mints_and_checks() {
    let tmp = TempDir::new("replay");
    record(&tmp.path);

    let (ok, out, err) = lineage(
        &tmp.path,
        &[
            "verify",
            "run.plineage",
            "--replay",
            "--certify",
            "run.pcert",
        ],
    );
    assert!(ok, "mint failed:\n{err}");
    assert!(out.contains("certificate written"), "stdout:\n{out}");
    assert!(
        tmp.path.join("run.pcert").exists(),
        "certificate was written"
    );

    let (ok, out, err) = lineage(&tmp.path, &["check-cert", "run.pcert", "run.plineage"]);
    assert!(ok, "check failed:\n{err}");
    assert!(out.contains("replay-verified"), "stdout:\n{out}");
}

#[test]
fn lineage_verified_certificate_mints_and_checks() {
    let tmp = TempDir::new("rehash");
    record(&tmp.path);

    let (ok, out, err) = lineage(
        &tmp.path,
        &["verify", "run.plineage", "--certify", "run.pcert"],
    );
    assert!(ok, "mint failed:\n{err}");
    assert!(out.contains("certificate written"), "stdout:\n{out}");

    let (ok, out, err) = lineage(&tmp.path, &["check-cert", "run.pcert", "run.plineage"]);
    assert!(ok, "check failed:\n{err}");
    assert!(out.contains("lineage-verified"), "stdout:\n{out}");
}

#[test]
fn tampering_the_sidecar_fails_the_check_naming_the_mismatch() {
    let tmp = TempDir::new("tamper");
    record(&tmp.path);
    let (ok, _, err) = lineage(
        &tmp.path,
        &["verify", "run.plineage", "--certify", "run.pcert"],
    );
    assert!(ok, "mint failed:\n{err}");

    // Tamper the sidecar after the certificate was minted: its digest moves.
    let sidecar = tmp.path.join("run.plineage");
    let mut bytes = fs::read(&sidecar).unwrap();
    bytes.push(b' ');
    fs::write(&sidecar, &bytes).unwrap();

    let (ok, _, err) = lineage(&tmp.path, &["check-cert", "run.pcert", "run.plineage"]);
    assert!(!ok, "a tampered sidecar must fail the certificate check");
    assert!(err.contains("digest mismatch"), "stderr:\n{err}");
}

#[test]
fn an_unknown_claim_certificate_is_rejected() {
    let tmp = TempDir::new("unknown");
    record(&tmp.path);

    // Forge a certificate whose subject correctly binds the sidecar but whose claim
    // this build does not recognize: an older build must not trust a future claim.
    let sidecar_bytes = fs::read(tmp.path.join("run.plineage")).unwrap();
    let forged = LineageCert {
        subject: Digest::from(subject_of(&sidecar_bytes)),
        claim: LineageClaim::Reserved(4096),
        scheme: HASH_SCHEME.to_string(),
        compiler: "a-future-build".to_string(),
        evidence: Vec::new(),
    };
    fs::write(tmp.path.join("forged.pcert"), encode_lineage_cert(&forged)).unwrap();

    let (ok, _, err) = lineage(&tmp.path, &["check-cert", "forged.pcert", "run.plineage"]);
    assert!(!ok, "an unknown claim must not be silently accepted");
    assert!(
        err.contains("untrusted") || err.contains("not recognized"),
        "stderr:\n{err}"
    );
}

#[test]
fn a_failed_verification_writes_no_certificate() {
    let tmp = TempDir::new("nofail");
    record(&tmp.path);
    // Tamper the recorded input so the replay's input-file rehash disagrees.
    fs::write(tmp.path.join("input.json"), "{\"t\": 6}").unwrap();

    let (ok, _, _) = lineage(
        &tmp.path,
        &[
            "verify",
            "run.plineage",
            "--replay",
            "--certify",
            "run.pcert",
        ],
    );
    assert!(!ok, "a diverging replay must fail");
    assert!(
        !tmp.path.join("run.pcert").exists(),
        "a failed verification must write no certificate"
    );
}
