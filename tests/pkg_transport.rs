//! The package manager's transport, trust, and publish surface: the Transport
//! trait, git-backed replication with hash verification, stdlib-baseline dedup,
//! `export` source-stability, the signed index, the transparency log, `audit`, and
//! `publish`.
//!
//! Every test runs against temp directories (and temp git repositories) removed on
//! drop, so nothing touches the user's real store or leaves state behind. Tests
//! that need `git` or `ssh-keygen` skip cleanly when the tool is absent.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::core::HASH_SCHEME;
use prism::flags::SignMode;
use prism::pkg::export::{export, verify_manifest, EXPORT_MANIFEST_HEADER};
use prism::pkg::transport::{
    push_closure, verify, verify_closure, DiskTransport, GitTransport, Transport, TransportError,
};
use prism::pkg::trust::{
    audit, parse_index, serialize_index, sign, verify_signature, IndexRow, Log, SignedArtifact,
    Verdict, INDEX_KIND_NAMESPACE,
};
use prism::resolve::SourceBundleArtifactKind;
use prism::store::disk::Store;
use prism::{commit_to_store, default_roots, namespace_identity, with_prelude, Config, DynFlags};

// A unique scratch directory removed on drop.
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

    fn join(&self, rel: &str) -> PathBuf {
        self.path.join(rel)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

// Two functions with an internal edge, using no stdlib beyond primitive `+`.
const PROG_PLAIN: &str = "fn double(x) = x + x\nfn quad(x) = double(double(x))\n";

// A function that calls a stdlib definition (`map`), so its closure reaches the
// shared baseline.
const PROG_STDLIB: &str = "fn inc(xs) = map(\\(x) -> x + 1, xs)\n";

fn store_cfg(root: PathBuf) -> Config {
    let mut cfg = Config::default();
    cfg.flags.store = true;
    cfg.flags.store_path = Some(root);
    cfg.flags.quiet = true;
    cfg
}

// Commit a program into a fresh store, returning the opened store.
fn commit(prog: &str, root: &Path) -> Store {
    let cfg = store_cfg(root.to_path_buf());
    commit_to_store(&with_prelude(prog), &default_roots(Path::new(".")), &cfg)
        .expect("commit_to_store");
    Store::open_or_create(root).expect("open store")
}

fn hash_of(store: &Store, name: &str) -> String {
    store
        .names()
        .unwrap()
        .remove(name)
        .unwrap_or_else(|| panic!("no name binding for {name}"))
}

// -- Transport trait: disk round-trip and verification --------------------------

#[test]
fn disk_transport_round_trips_and_verifies() {
    let tmp = TempDir::new("disk");
    let store = commit(PROG_PLAIN, &tmp.join("store"));
    let hash = hash_of(&store, "double");

    let tp = DiskTransport::open(tmp.join("store")).unwrap();
    assert!(tp.has(&hash));
    let bytes = tp.fetch(&hash).expect("fetch verified");
    verify(&hash, &bytes).expect("bytes verify against hash");

    let absent = "ff".repeat(32);
    assert!(matches!(tp.fetch(&absent), Err(TransportError::Missing(_))));
}

#[test]
fn fetch_rejects_a_corrupted_object() {
    let tmp = TempDir::new("corrupt");
    let store = commit(PROG_PLAIN, &tmp.join("store"));
    let hash = hash_of(&store, "double");
    let good = store.get(&hash).unwrap();

    // Tampering with a single byte breaks the content-hash re-derivation.
    let mut bad = good;
    *bad.last_mut().unwrap() ^= 0xff;
    assert!(matches!(
        verify(&hash, &bad),
        Err(TransportError::HashMismatch { .. } | TransportError::Codec(_))
    ));

    // Garbage that is not even a frame is rejected too.
    assert!(verify(&hash, b"not a def frame at all").is_err());
}

// -- stdlib-baseline dedup ------------------------------------------------------

#[test]
fn push_closure_dedups_the_stdlib_baseline() {
    let tmp = TempDir::new("dedup");
    let src = commit(PROG_STDLIB, &tmp.join("src"));
    let inc = hash_of(&src, "inc");
    let baseline: BTreeSet<String> = prism::pkg::stdlib_baseline().unwrap();

    let dst = DiskTransport::open(tmp.join("dst")).unwrap();
    let stats = push_closure(&src, &dst, std::slice::from_ref(&inc), &baseline).unwrap();

    // The user definition travels; nothing reachable from the stdlib root does.
    assert!(stats.transferred.contains(&inc));
    for h in &stats.transferred {
        assert!(
            !baseline.contains(h),
            "a baseline hash was transferred: {h}"
        );
    }
    assert!(
        stats.skipped_baseline > 0,
        "the closure never reached the shared baseline"
    );
    assert!(dst.has(&inc));
}

// -- git-backed adapter: push, fetch, corruption rejection ----------------------

fn git_config_identity(repo: &Path) {
    for (k, v) in [
        ("user.email", "test@prism.dev"),
        ("user.name", "prism test"),
    ] {
        Command::new("git")
            .args(["-C", &repo.to_string_lossy(), "config", k, v])
            .status()
            .unwrap();
    }
}

#[test]
fn git_adapter_replicates_a_store_with_verification() {
    if !have("git") {
        eprintln!("skipping: git not installed");
        return;
    }
    let tmp = TempDir::new("git");
    let src = commit(PROG_STDLIB, &tmp.join("src"));
    let inc = hash_of(&src, "inc");
    let baseline = prism::pkg::stdlib_baseline().unwrap();

    // A bare remote is the store's git home.
    let remote = tmp.join("remote.git");
    Command::new("git")
        .args(["init", "--bare", "--quiet", &remote.to_string_lossy()])
        .status()
        .unwrap();

    // Publisher: clone the empty remote, push the closure, commit and push.
    let pub_clone = tmp.join("pub");
    let publisher = GitTransport::clone_or_open(&remote.to_string_lossy(), &pub_clone).unwrap();
    git_config_identity(&pub_clone);
    let stats = push_closure(&src, &publisher, std::slice::from_ref(&inc), &baseline).unwrap();
    assert!(stats.transferred.contains(&inc));
    publisher.push("publish inc").unwrap();

    // Consumer: clone the now-populated remote and fetch, verified.
    let con_clone = tmp.join("con");
    let consumer = GitTransport::clone_or_open(&remote.to_string_lossy(), &con_clone).unwrap();
    assert!(consumer.has(&inc));
    let bytes = consumer.fetch(&inc).expect("fetch verified");
    verify(&inc, &bytes).unwrap();

    // Corrupt the consumer's copy on disk; the next fetch must reject it.
    let obj = con_clone.join("objects").join(&inc[..2]).join(&inc[2..]);
    fs::write(&obj, b"tampered").unwrap();
    assert!(consumer.fetch(&inc).is_err());
}

// -- export: source-stability fixpoint ------------------------------------------

#[test]
fn export_is_a_source_level_fixpoint() {
    let tmp = TempDir::new("export");
    let roots = default_roots(Path::new("."));

    let full1 = with_prelude(PROG_PLAIN);
    let r1 = export(PROG_PLAIN, &full1, &roots, &tmp.join("e1"), "prog").unwrap();
    let text1 = fs::read_to_string(&r1.source_path).unwrap();

    // Re-ingest the emitted text and export again.
    let full2 = with_prelude(&text1);
    let r2 = export(&text1, &full2, &roots, &tmp.join("e2"), "prog").unwrap();
    let text2 = fs::read_to_string(&r2.source_path).unwrap();

    assert_eq!(text1, text2, "export is not a text-level fixpoint");
    // A pure reformat is behavior-preserving, so the namespace root is stable here;
    // hash-stability across a full store round trip stays an open promise.
    assert_eq!(r1.root, r2.root);
    assert_eq!(r1.scheme, HASH_SCHEME);
    assert_eq!(r1.kind, INDEX_KIND_NAMESPACE);
    let manifest = fs::read_to_string(&r1.manifest_path).unwrap();
    assert!(manifest.starts_with(&format!("{EXPORT_MANIFEST_HEADER}\n")));
    assert!(manifest.contains(&format!("scheme\t{}\n", r1.scheme)));
    assert!(manifest.contains(&format!("kind\t{}\n", r1.kind)));
    assert!(manifest.contains(&format!("root\t{}\n", r1.root)));
    let identity = namespace_identity(&full1, &roots).unwrap();
    let parsed = verify_manifest(&manifest, &identity).unwrap();
    assert_eq!(parsed.root, r1.root);

    let wrong_kind = manifest.replace(
        &format!("kind\t{}\n", r1.kind),
        &format!("kind\t{}\n", SourceBundleArtifactKind::Package.as_str()),
    );
    let err = verify_manifest(&wrong_kind, &identity)
        .unwrap_err()
        .to_string();
    assert!(err.contains("artifact kind"), "{err}");
}

// -- signed index: sign/verify round-trip and tamper detection ------------------

// Generate a throwaway ssh key and its allowed_signers line for `identity`.
fn ssh_keypair(dir: &Path, identity: &str) -> (PathBuf, PathBuf) {
    let key = dir.join("id");
    let ok = Command::new("ssh-keygen")
        .args([
            "-t",
            "ed25519",
            "-f",
            &key.to_string_lossy(),
            "-N",
            "",
            "-C",
            identity,
            "-q",
        ])
        .status()
        .unwrap()
        .success();
    assert!(ok, "ssh-keygen failed to make a key");
    let pubkey = fs::read_to_string(dir.join("id.pub")).unwrap();
    let allowed = dir.join("allowed_signers");
    fs::write(&allowed, format!("{identity} {pubkey}")).unwrap();
    (key, allowed)
}

fn ssh_flags(key: &Path, allowed: &Path, identity: &str) -> DynFlags {
    DynFlags {
        sign_mode: SignMode::Ssh,
        sign_key: Some(key.to_path_buf()),
        sign_identity: Some(identity.to_string()),
        sign_allowed_signers: Some(allowed.to_path_buf()),
        ..DynFlags::default()
    }
}

#[test]
fn package_index_rows_name_the_hash_scheme() {
    let row = IndexRow {
        origin: "github.com/prism-lang/http".into(),
        name: "http".into(),
        tag: "2.0".into(),
        scheme: HASH_SCHEME.into(),
        kind: prism::pkg::trust::INDEX_KIND_SOURCE.into(),
        root: "a3f9".repeat(16),
    };
    let body = serialize_index(std::slice::from_ref(&row));
    let text = String::from_utf8(body.clone()).unwrap();
    assert!(text.starts_with("prism-pkg-index\tv4\n"));
    assert!(
        text.contains(&format!("\t{HASH_SCHEME}\t")),
        "index row must carry hash scheme:\n{text}"
    );
    assert!(
        text.contains("github.com/prism-lang/http\thttp\t2.0"),
        "index row must carry canonical origin before display name:\n{text}"
    );
    assert_eq!(parse_index(&body), vec![row]);
}

#[test]
fn a_legacy_index_parses_to_no_rows() {
    // The legacy index headers are gone: only the current header yields rows.
    // Parsing stays tolerant (no rows rather than an error) because callers
    // that need presence-versus-absence check the index artifact itself, but a
    // legacy body can no longer smuggle rows in under an old scheme.
    let body = b"prism-pkg-index\tv1\nhttp\t2.0\ta3f9\n";
    assert_eq!(parse_index(body), Vec::new());
}

#[test]
fn signed_index_round_trips_and_detects_tampering() {
    if !have("ssh-keygen") {
        eprintln!("skipping: ssh-keygen not installed");
        return;
    }
    let tmp = TempDir::new("sign");
    let identity = "test@prism";
    let (key, allowed) = ssh_keypair(&tmp.path, identity);
    let flags = ssh_flags(&key, &allowed, identity);

    let rows = vec![IndexRow {
        origin: "github.com/prism-lang/http".into(),
        name: "http".into(),
        tag: "2.0".into(),
        scheme: HASH_SCHEME.into(),
        kind: prism::pkg::trust::INDEX_KIND_SOURCE.into(),
        root: "a3f9".repeat(16),
    }];
    let body = serialize_index(&rows);
    let sig = sign(&body, &flags).expect("sign").expect("a signature");
    let artifact = SignedArtifact {
        body: body.clone(),
        sig: Some(sig.clone()),
    };
    assert!(matches!(
        verify_signature(&artifact, &flags),
        Verdict::Valid { .. }
    ));

    // A tampered body no longer verifies under the same signature.
    let mut tampered = body;
    tampered.extend_from_slice(b"http\tevil\tdeadbeef\n");
    let bad = SignedArtifact {
        body: tampered,
        sig: Some(sig),
    };
    assert!(matches!(
        verify_signature(&bad, &flags),
        Verdict::Invalid(_)
    ));
}

#[test]
fn unsigned_mode_produces_no_signature() {
    let flags = DynFlags {
        sign_mode: SignMode::Unsigned,
        ..DynFlags::default()
    };
    let body = serialize_index(&[IndexRow {
        origin: "x".into(),
        name: "x".into(),
        tag: "1".into(),
        scheme: HASH_SCHEME.into(),
        kind: prism::pkg::trust::INDEX_KIND_SOURCE.into(),
        root: "00".repeat(32),
    }]);
    assert!(sign(&body, &flags).unwrap().is_none());
    let artifact = SignedArtifact { body, sig: None };
    assert_eq!(verify_signature(&artifact, &flags), Verdict::Unsigned);
}

// -- transparency log: append-only and repoint detection ------------------------

#[test]
fn log_is_append_only_and_detects_repoints() {
    let tmp = TempDir::new("log");
    let log = Log::at(tmp.join("log"));

    assert_eq!(
        log.append(
            "github.com/prism-lang/http",
            "http",
            "2.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "aaaa",
        )
        .unwrap(),
        0
    );
    assert_eq!(
        log.append(
            "github.com/prism-lang/geo",
            "geo",
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "bbbb",
        )
        .unwrap(),
        1
    );
    assert!(log.repoints().unwrap().is_empty());

    // Re-publishing the same pointer is not a repoint.
    assert_eq!(
        log.append(
            "github.com/prism-lang/http",
            "http",
            "2.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "aaaa",
        )
        .unwrap(),
        2
    );
    assert!(log.repoints().unwrap().is_empty());

    // Moving http@2.0 to a new root is a repoint the log makes visible.
    assert_eq!(
        log.append(
            "github.com/prism-lang/http",
            "http",
            "2.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "cccc",
        )
        .unwrap(),
        3
    );
    let repoints = log.repoints().unwrap();
    assert_eq!(repoints.len(), 1);
    assert_eq!(repoints[0].origin, "github.com/prism-lang/http");
    assert_eq!(repoints[0].name, "http");
    assert_eq!(repoints[0].from_root, "aaaa");
    assert_eq!(repoints[0].to_root, "cccc");

    // The sequence is dense and monotonic, and every entry is preserved.
    let entries = log.entries().unwrap();
    assert_eq!(entries.len(), 4);
    for (i, e) in entries.iter().enumerate() {
        assert_eq!(e.seq, i as u64);
    }
}

// -- publish and audit ----------------------------------------------------------

// Publish PROG_STDLIB unsigned into a store, returning the published pointer.
fn publish_unsigned(root: &Path, name: &str, tag: &str) -> IndexRow {
    let cfg = {
        let mut c = store_cfg(root.to_path_buf());
        c.flags.sign_mode = SignMode::Unsigned;
        c
    };
    let full = with_prelude(PROG_STDLIB);
    let roots = default_roots(Path::new("."));
    let msg = prism::pkg::trust::publish_cmd(&full, &roots, name, tag, &cfg).unwrap();
    assert!(
        msg.contains("git tag"),
        "publish must print the git tag command"
    );
    let identity = namespace_identity(&full, &roots).unwrap();
    IndexRow {
        origin: name.to_string(),
        name: name.to_string(),
        tag: tag.to_string(),
        scheme: identity.scheme.to_string(),
        kind: identity.kind.to_string(),
        root: identity.root,
    }
}

#[test]
fn publish_writes_the_pointer_and_a_log_row() {
    let tmp = TempDir::new("publish");
    let store_root = tmp.join("store");
    let row = publish_unsigned(&store_root, "http", "2.0");

    // The signed index binds the pointer.
    let tp = DiskTransport::open(&store_root).unwrap();
    let idx = tp.fetch_index("http").unwrap();
    assert_eq!(idx, vec![row.clone()]);

    // The transparency log recorded it at sequence 0.
    let log = prism::pkg::trust::store_log(&store_root);
    let entries = log.entries().unwrap();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].root, row.root);
}

#[test]
fn audit_passes_the_green_path_and_names_each_failure() {
    let tmp = TempDir::new("audit");
    let store_root = tmp.join("store");
    let row = publish_unsigned(&store_root, "http", "2.0");

    let tp = DiskTransport::open(&store_root).unwrap();
    let log = prism::pkg::trust::store_log(&store_root);
    let baseline = prism::pkg::stdlib_baseline().unwrap();
    let unsigned = DynFlags {
        sign_mode: SignMode::Unsigned,
        ..DynFlags::default()
    };

    // Green path: unsigned index accepted because the override is set.
    let report = audit(
        tp.store(),
        &tp,
        &log,
        std::slice::from_ref(&row),
        &baseline,
        &unsigned,
        true,
    )
    .unwrap();
    assert!(report.ok(), "green audit failed: {}", report.render());

    // Failure 1: an unsigned index is refused without the override.
    let refused = audit(
        tp.store(),
        &tp,
        &log,
        std::slice::from_ref(&row),
        &baseline,
        &unsigned,
        false,
    )
    .unwrap();
    assert!(!refused.ok());
    assert!(refused.render().contains("unsigned"));

    // Failure 2: a pin the signed index does not match is a named failure.
    let mismatch = IndexRow {
        root: "de".repeat(32),
        ..row.clone()
    };
    let bad = audit(
        tp.store(),
        &tp,
        &log,
        std::slice::from_ref(&mismatch),
        &baseline,
        &unsigned,
        true,
    )
    .unwrap();
    assert!(!bad.ok());

    // Failure 3: a corrupt user object fails the closure integrity re-check. The
    // stdlib baseline is trusted, so the corruption must land on `inc`.
    let inc = hash_of(tp.store(), "inc");
    let obj = store_root.join("objects").join(&inc[..2]).join(&inc[2..]);
    fs::write(&obj, b"corrupt").unwrap();
    let integrity = audit(
        tp.store(),
        &tp,
        &log,
        std::slice::from_ref(&row),
        &baseline,
        &unsigned,
        true,
    )
    .unwrap();
    assert!(!integrity.ok(), "corruption slipped past audit");
}

#[test]
fn verify_closure_counts_the_user_objects() {
    let tmp = TempDir::new("closure");
    let src = commit(PROG_PLAIN, &tmp.join("store"));
    let quad = hash_of(&src, "quad");
    let baseline = prism::pkg::stdlib_baseline().unwrap();
    // quad -> double, both user objects, both re-verify.
    let n = verify_closure(&src, std::slice::from_ref(&quad), &baseline).unwrap();
    assert!(n >= 2, "expected quad and double, verified {n}");
}

// -- transparency log: mutilation is loud, an empty file is uninitialized -------

// A crash between file creation and the header write leaves a zero-byte log.
// That state is uninitialized, not malformed: reads see an empty history and
// the next publish writes the header and entry 0, healing it.
#[test]
fn empty_log_file_is_uninitialized_not_bricked() {
    let tmp = TempDir::new("log-empty");
    let path = tmp.join("log");
    std::fs::write(&path, "").unwrap();
    let log = Log::at(&path);
    assert!(log.entries().unwrap().is_empty());
    let seq = log
        .append(
            "github.com/prism-lang/http",
            "http",
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "aaaa",
        )
        .unwrap();
    assert_eq!(seq, 0);
    assert_eq!(log.entries().unwrap().len(), 1);
}

// A crash after the header but before the first entry leaves a header-only
// file; the next append must not write a second header.
#[test]
fn header_only_log_appends_without_a_second_header() {
    let tmp = TempDir::new("log-header-only");
    let path = tmp.join("log");
    let log = Log::at(&path);
    log.append(
        "github.com/prism-lang/http",
        "http",
        "1.0",
        HASH_SCHEME,
        prism::pkg::trust::INDEX_KIND_SOURCE,
        "aaaa",
    )
    .unwrap();
    let text = std::fs::read_to_string(&path).unwrap();
    let header = text.lines().next().unwrap().to_string();
    // Reconstruct the crashed state: header line only, then append again.
    std::fs::write(&path, format!("{header}\n")).unwrap();
    let seq = log
        .append(
            "github.com/prism-lang/geo",
            "geo",
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "bbbb",
        )
        .unwrap();
    assert_eq!(seq, 0);
    let text = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        text.lines().filter(|l| *l == header).count(),
        1,
        "exactly one header line:\n{text}"
    );
    assert_eq!(log.entries().unwrap().len(), 1);
}

// A sequence hole is a loud error, never a silent renumbering. Deleting a line
// from a chained log trips the chain check first (its own test covers that), so
// the hole here is built chain-valid: each line commits the digest of the line
// before it (read back through `head()`, which digests the last line) while the
// sequence jumps from 0 to 2, exactly what a tamperer who re-chains after
// removing an entry would produce. Density still catches it.
#[test]
fn a_sequence_hole_is_a_loud_error_not_a_renumbering() {
    let tmp = TempDir::new("log-hole");
    let path = tmp.join("log");
    let header = "prism-pkg-log\tv5";
    std::fs::write(&path, format!("{header}\n")).unwrap();
    let log = Log::at(&path);
    let d_header = log.head().unwrap().expect("header digests");
    let line0 = format!(
        "0\t1\t{d_header}\tgithub.com/prism-lang/x\thttp\t1.0\tprism-core-hash-v1\tsource-bundle\taaaa"
    );
    std::fs::write(&path, format!("{header}\n{line0}\n")).unwrap();
    let d0 = log.head().unwrap().expect("line 0 digests");
    let line2 = format!(
        "2\t3\t{d0}\tgithub.com/prism-lang/x\ttz\t1.0\tprism-core-hash-v1\tsource-bundle\tcccc"
    );
    std::fs::write(&path, format!("{header}\n{line0}\n{line2}\n")).unwrap();
    let err = log.entries().unwrap_err().to_string();
    assert!(err.contains("sequence hole"), "unexpected error: {err}");
    assert!(
        log.append(
            "github.com/prism-lang/x",
            "late",
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            "dddd",
        )
        .is_err(),
        "append into a holey log must refuse"
    );
}

// A line that fits no known shape is evidence of corruption, not noise to skip:
// skipping would desynchronize the numbering under the reader's feet.
#[test]
fn an_unrecognized_line_is_a_loud_error() {
    let tmp = TempDir::new("log-garbage");
    let path = tmp.join("log");
    let log = Log::at(&path);
    log.append(
        "github.com/prism-lang/http",
        "http",
        "1.0",
        HASH_SCHEME,
        prism::pkg::trust::INDEX_KIND_SOURCE,
        "aaaa",
    )
    .unwrap();
    let mut text = std::fs::read_to_string(&path).unwrap();
    text.push_str("not a log line\n");
    std::fs::write(&path, text).unwrap();
    let err = log.entries().unwrap_err().to_string();
    assert!(err.contains("unrecognized line"), "unexpected error: {err}");
}

// -- transparency log: the hash chain ------------------------------------------

// Content tampering with the sequence numbers intact is exactly what the density
// check cannot see; the chain catches it because the edited line no longer
// hashes to what its successor committed.
#[test]
fn editing_a_line_in_place_breaks_the_chain() {
    let tmp = TempDir::new("log-chain-tamper");
    let path = tmp.join("log");
    let log = Log::at(&path);
    for (name, root) in [("http", "aaaa"), ("geo", "bbbb"), ("tz", "cccc")] {
        log.append(
            "github.com/prism-lang/x",
            name,
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            root,
        )
        .unwrap();
    }
    assert_eq!(log.entries().unwrap().len(), 3);
    let text = std::fs::read_to_string(&path).unwrap();
    // Rewrite the middle entry's root, keeping its seq and shape intact.
    let edited = text.replace("bbbb", "beef");
    assert_ne!(text, edited, "the edit must hit");
    std::fs::write(&path, edited).unwrap();
    let err = log.entries().unwrap_err().to_string();
    assert!(err.contains("chain break"), "unexpected error: {err}");
}

// A cleanly truncated suffix is internally consistent, the one mutilation no
// local check can see; the head is the value that makes it visible to anyone
// who pinned the longer log's head.
#[test]
fn suffix_truncation_moves_the_chain_head() {
    let tmp = TempDir::new("log-chain-head");
    let path = tmp.join("log");
    let log = Log::at(&path);
    for (name, root) in [("http", "aaaa"), ("geo", "bbbb")] {
        log.append(
            "github.com/prism-lang/x",
            name,
            "1.0",
            HASH_SCHEME,
            prism::pkg::trust::INDEX_KIND_SOURCE,
            root,
        )
        .unwrap();
    }
    let full_head = log.head().unwrap().expect("chained log has a head");
    let text = std::fs::read_to_string(&path).unwrap();
    let kept: Vec<&str> = text.lines().take(2).collect(); // header + entry 0
    std::fs::write(&path, format!("{}\n", kept.join("\n"))).unwrap();
    assert_eq!(log.entries().unwrap().len(), 1, "truncated log still reads");
    let short_head = log.head().unwrap().expect("still chained");
    assert_ne!(full_head, short_head, "the head is the witness anchor");
}

// The unchained history formats (v1 through v4) are gone: a log under any old
// header neither reads nor extends, and it has no chain head. The migration is
// a fresh v5 log, never a reinterpretation of unverifiable history.
#[test]
fn a_legacy_log_is_rejected_outright() {
    for legacy_header in ["prism-pkg-log\tv3", "prism-pkg-log\tv4"] {
        let tmp = TempDir::new("log-legacy");
        let path = tmp.join("log");
        std::fs::write(
            &path,
            format!(
                "{legacy_header}\n0\t1\tgithub.com/prism-lang/x\thttp\t1.0\tprism-core-hash-v1\tsource-bundle\taaaa\n"
            ),
        )
        .unwrap();
        let log = Log::at(&path);
        let err = log.entries().unwrap_err().to_string();
        assert!(
            err.contains("unrecognized header"),
            "unexpected error for {legacy_header}: {err}"
        );
        assert!(
            log.head().unwrap().is_none(),
            "a legacy log has no chain head"
        );
        let err = log
            .append(
                "github.com/prism-lang/x",
                "geo",
                "1.0",
                HASH_SCHEME,
                prism::pkg::trust::INDEX_KIND_SOURCE,
                "bbbb",
            )
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("unrecognized header"),
            "unexpected error for {legacy_header}: {err}"
        );
    }
}
