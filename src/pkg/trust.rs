//! Trust: one signed artifact and a local append-only transparency log.
//!
//! Integrity needs no signature, because a tampered blob fails its content hash on
//! fetch. The one thing a hash cannot self-certify is the mapping from a human
//! package identity, name, and tag to a root hash, so that mapping is the *sole*
//! signed artifact: a tiny, human-readable `identity -> name -> tag -> root`
//! index. Everything under it verifies itself.
//!
//! Beside the index, a local append-only transparency log records every
//! pointer ever seen with a monotonic sequence number, so a silent repoint of a
//! published identity is detectable after the fact. This is the log's local rung:
//! no witnessing, no gossip, just an on-disk record that is only appended to,
//! never rewritten.
//!
//! Signing is done by an external tool behind a narrow seam ([`sign`],
//! [`verify_signature`]), so no cryptographic dependency enters the compiler. The
//! default is `ssh-keygen -Y sign`/`-Y verify` (namespaced signatures, present
//! wherever OpenSSH is); `minisign` is an alternative behind the same seam; and an
//! explicit unsigned mode is a development escape hatch that [`audit`] refuses
//! unless the operator allows it.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::core::HASH_SCHEME;
use crate::driver::Config;
use crate::error::Error;
use crate::flags::{DynFlags, SignMode};
use crate::pkg::std_source::encode_source_bundle;
use crate::pkg::stdlib_baseline;
use crate::pkg::transport::{pkg_dir, verify_all, DiskTransport, Transport, TransportError};
use crate::resolve::Root;
use crate::store::cert::{check_cert, CertStatus};
use crate::store::disk::{resolve_store_path, Store};

// The signature namespace (domain separator) `ssh-keygen -Y` binds a signature to.
// A signature over the index in this namespace is meaningless in any other, which
// stops a signature made for one purpose being replayed as another.
const SIG_NAMESPACE: &str = "prism-package-index";

// Line-oriented, tab-separated, header-versioned artifact formats. A row is one
// line; hashes and git tags contain no tab, so the separator is unambiguous.
const INDEX_HEADER_V1: &str = "prism-pkg-index\tv1";
const INDEX_HEADER_V2: &str = "prism-pkg-index\tv2";
const INDEX_HEADER_V3: &str = "prism-pkg-index\tv3";
const INDEX_HEADER_V4: &str = "prism-pkg-index\tv4";
const LOG_HEADER_V1: &str = "prism-pkg-log\tv1";
const LOG_HEADER_V2: &str = "prism-pkg-log\tv2";
const LOG_HEADER_V3: &str = "prism-pkg-log\tv3";
const LOG_HEADER_V4: &str = "prism-pkg-log\tv4";
const FIELD_SEP: char = '\t';

/// Signed-index kind for a whole-program namespace root.
pub const INDEX_KIND_NAMESPACE: &str = crate::driver::NAMESPACE_ARTIFACT_KIND;
/// Signed-index kind for a store-served source bundle.
pub const INDEX_KIND_SOURCE: &str = "source-bundle";

/// One signed pointer.
///
/// A package `origin` exposes a human `name` at a git `tag` that resolves to a
/// `root` content hash under a named hash scheme. The index is a set of these,
/// and the whole set is what a signature covers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexRow {
    /// The canonical package identity. For git dependencies this is the manifest
    /// URL, so two repositories with the same display name cannot share a pointer.
    pub origin: String,
    /// The package name a developer types.
    pub name: String,
    /// The opaque git tag the release was cut at (never a range).
    pub tag: String,
    /// The namespace root content hash the name and tag map to.
    pub root: String,
    /// The hash scheme that gives `root` its meaning.
    pub scheme: String,
    /// The artifact kind the root names.
    pub kind: String,
}

/// The signed index as it travels: the index body (the rows) and its detached
/// signature. `sig` is `None` for an unsigned (dev-mode) index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedArtifact {
    /// The serialized index rows, exactly the bytes the signature covers.
    pub body: Vec<u8>,
    /// The detached signature over `body`, or `None` when unsigned.
    pub sig: Option<Vec<u8>>,
}

/// The failures a trust operation can produce.
#[derive(Debug)]
pub enum TrustError {
    /// A filesystem error.
    Io(io::Error),
    /// A transport failure surfaced through an index read or write.
    Transport(TransportError),
    /// The signing tool ran but failed, or the configuration it needs is absent.
    Sign(String),
}

impl std::fmt::Display for TrustError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "trust io error: {e}"),
            Self::Transport(e) => write!(f, "{e}"),
            Self::Sign(msg) => write!(f, "signing error: {msg}"),
        }
    }
}

impl std::error::Error for TrustError {}

impl From<io::Error> for TrustError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<TransportError> for TrustError {
    fn from(e: TransportError) -> Self {
        Self::Transport(e)
    }
}

impl From<TrustError> for crate::error::Error {
    fn from(e: TrustError) -> Self {
        match e {
            TrustError::Io(io) => Self::Io(io),
            other => Self::Resolve(other.to_string()),
        }
    }
}

/// Parse the index body into its rows. Tolerant: an unrecognized or short line is
/// skipped, so an additive future field never breaks an old reader.
#[must_use]
pub fn parse_index(body: &[u8]) -> Vec<IndexRow> {
    let text = String::from_utf8_lossy(body);
    let mut lines = text.lines();
    // A body with the wrong header parses to no rows rather than an error: callers
    // that need the distinction check `index_artifact` for presence.
    let header = lines.next();
    if header != Some(INDEX_HEADER_V1)
        && header != Some(INDEX_HEADER_V2)
        && header != Some(INDEX_HEADER_V3)
        && header != Some(INDEX_HEADER_V4)
    {
        return Vec::new();
    }
    lines
        .filter_map(|line| {
            let fields: Vec<&str> = line.split(FIELD_SEP).collect();
            match (header, fields.as_slice()) {
                (Some(INDEX_HEADER_V1), [name, tag, root]) if !name.is_empty() => Some(IndexRow {
                    name: (*name).to_string(),
                    tag: (*tag).to_string(),
                    origin: (*name).to_string(),
                    root: (*root).to_string(),
                    scheme: HASH_SCHEME.to_string(),
                    kind: INDEX_KIND_NAMESPACE.to_string(),
                }),
                (Some(INDEX_HEADER_V2), [name, tag, scheme, root]) if !name.is_empty() => {
                    Some(IndexRow {
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        origin: (*name).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: INDEX_KIND_NAMESPACE.to_string(),
                        root: (*root).to_string(),
                    })
                }
                (Some(INDEX_HEADER_V3), [name, tag, scheme, kind, root]) if !name.is_empty() => {
                    Some(IndexRow {
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        origin: (*name).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: (*root).to_string(),
                    })
                }
                (Some(INDEX_HEADER_V4), [origin, name, tag, scheme, kind, root])
                    if !origin.is_empty() && !name.is_empty() =>
                {
                    Some(IndexRow {
                        origin: (*origin).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: (*root).to_string(),
                    })
                }
                _ => None,
            }
        })
        .collect()
}

/// Serialize rows into an index body, sorted by `(origin, name, tag)` so the same
/// set of pointers always yields byte-identical bytes and therefore a stable
/// signature.
#[must_use]
pub fn serialize_index(rows: &[IndexRow]) -> Vec<u8> {
    let mut sorted: Vec<&IndexRow> = rows.iter().collect();
    sorted.sort_by(|a, b| (&a.origin, &a.name, &a.tag).cmp(&(&b.origin, &b.name, &b.tag)));
    let mut body = String::from(INDEX_HEADER_V4);
    body.push('\n');
    for r in sorted {
        let _ = writeln!(
            body,
            "{}{FIELD_SEP}{}{FIELD_SEP}{}{FIELD_SEP}{}{FIELD_SEP}{}{FIELD_SEP}{}",
            r.origin, r.name, r.tag, r.scheme, r.kind, r.root
        );
    }
    body.into_bytes()
}

/// Upsert `(origin, name, tag) -> root` into `rows`, returning the new row set.
///
/// A repoint (an existing `(origin, name, tag)` given a new root) replaces the
/// row; the transparency log is what makes that change visible after the fact.
#[must_use]
pub fn upsert(rows: &[IndexRow], row: IndexRow) -> Vec<IndexRow> {
    let mut map: BTreeMap<(String, String, String), (String, String, String)> = rows
        .iter()
        .map(|r| {
            (
                (r.origin.clone(), r.name.clone(), r.tag.clone()),
                (r.scheme.clone(), r.kind.clone(), r.root.clone()),
            )
        })
        .collect();
    map.insert(
        (row.origin.clone(), row.name.clone(), row.tag.clone()),
        (row.scheme, row.kind, row.root),
    );
    map.into_iter()
        .map(|((origin, name, tag), (scheme, kind, root))| IndexRow {
            origin,
            name,
            tag,
            root,
            scheme,
            kind,
        })
        .collect()
}

/// The outcome of verifying an index signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The signature checked out under the configured verifier.
    Valid {
        /// The signer identity, when the verifier reports one.
        identity: Option<String>,
    },
    /// The artifact carries no signature (dev mode).
    Unsigned,
    /// A signature was present but did not verify; the string is the diagnostic.
    Invalid(String),
    /// The verifier tool or its configuration was unavailable, so no judgment
    /// could be made.
    Unavailable(String),
}

/// Sign `body` with the configured external signer.
///
/// Returns `Ok(None)` in unsigned mode; otherwise `Ok(Some(sig))` with the
/// detached signature. Never links a crypto library: it shells to `ssh-keygen`
/// (or `minisign`) behind this one seam.
///
/// # Errors
/// [`TrustError::Sign`] if the mode needs a key that is not configured, or the
/// external tool fails.
pub fn sign(body: &[u8], flags: &DynFlags) -> Result<Option<Vec<u8>>, TrustError> {
    match flags.sign_mode {
        SignMode::Unsigned => Ok(None),
        SignMode::Ssh => {
            let key = flags.sign_key.as_ref().ok_or_else(|| {
                TrustError::Sign(
                    "ssh signing needs a key: set PRISM_SIGN_KEY, or PRISM_SIGN_MODE=unsigned for dev"
                        .into(),
                )
            })?;
            let sig = run_capturing(
                "ssh-keygen",
                &[
                    "-Y",
                    "sign",
                    "-f",
                    &key.to_string_lossy(),
                    "-n",
                    SIG_NAMESPACE,
                ],
                body,
            )?;
            Ok(Some(sig))
        }
        SignMode::Minisign => {
            let key = flags.sign_key.as_ref().ok_or_else(|| {
                TrustError::Sign(
                    "minisign signing needs a secret key: set PRISM_SIGN_KEY, or PRISM_SIGN_MODE=unsigned"
                        .into(),
                )
            })?;
            minisign_sign(body, key)
        }
    }
}

/// Verify an artifact's signature under the configured verifier.
///
/// Drives off the presence of a signature and the configured mode. An unsigned
/// artifact is [`Verdict::Unsigned`] (a policy decision left to the caller); a
/// missing verifier tool or `allowed_signers` file is [`Verdict::Unavailable`],
/// never a silent pass.
#[must_use]
pub fn verify_signature(artifact: &SignedArtifact, flags: &DynFlags) -> Verdict {
    let Some(sig) = &artifact.sig else {
        return Verdict::Unsigned;
    };
    match flags.sign_mode {
        SignMode::Minisign => minisign_verify(&artifact.body, sig, flags),
        // ssh is the default verifier for any present signature unless minisign is
        // explicitly selected; unsigned mode with a signature present still checks
        // it rather than ignoring evidence.
        SignMode::Ssh | SignMode::Unsigned => ssh_verify(&artifact.body, sig, flags),
    }
}

fn ssh_verify(body: &[u8], sig: &[u8], flags: &DynFlags) -> Verdict {
    let Some(allowed) = &flags.sign_allowed_signers else {
        return Verdict::Unavailable(
            "ssh verify needs an allowed_signers file: set PRISM_SIGN_ALLOWED_SIGNERS".into(),
        );
    };
    let identity = flags.sign_identity.clone().unwrap_or_default();
    let sig_file = match write_temp("sig", sig) {
        Ok(p) => p,
        Err(e) => return Verdict::Unavailable(format!("could not stage signature: {e}")),
    };
    let res = run_status(
        "ssh-keygen",
        &[
            "-Y",
            "verify",
            "-f",
            &allowed.to_string_lossy(),
            "-I",
            &identity,
            "-n",
            SIG_NAMESPACE,
            "-s",
            &sig_file.to_string_lossy(),
        ],
        body,
    );
    let _ = fs::remove_file(&sig_file);
    verdict_of(res, flags.sign_identity.clone())
}

fn minisign_verify(body: &[u8], sig: &[u8], flags: &DynFlags) -> Verdict {
    let Some(pubkey) = &flags.sign_allowed_signers else {
        return Verdict::Unavailable(
            "minisign verify needs a public key: set PRISM_SIGN_ALLOWED_SIGNERS".into(),
        );
    };
    let data_file = match write_temp("data", body) {
        Ok(p) => p,
        Err(e) => return Verdict::Unavailable(format!("could not stage data: {e}")),
    };
    let sig_file = match write_temp("minisig", sig) {
        Ok(p) => p,
        Err(e) => {
            let _ = fs::remove_file(&data_file);
            return Verdict::Unavailable(format!("could not stage signature: {e}"));
        }
    };
    let res = run_status(
        "minisign",
        &[
            "-V",
            "-p",
            &pubkey.to_string_lossy(),
            "-m",
            &data_file.to_string_lossy(),
            "-x",
            &sig_file.to_string_lossy(),
        ],
        &[],
    );
    let _ = fs::remove_file(&data_file);
    let _ = fs::remove_file(&sig_file);
    verdict_of(res, None)
}

fn minisign_sign(body: &[u8], key: &Path) -> Result<Option<Vec<u8>>, TrustError> {
    let data_file = write_temp("data", body)?;
    let sig_path = {
        let mut p = data_file.clone().into_os_string();
        p.push(".minisig");
        PathBuf::from(p)
    };
    let res = run_status(
        "minisign",
        &[
            "-S",
            "-s",
            &key.to_string_lossy(),
            "-m",
            &data_file.to_string_lossy(),
            "-x",
            &sig_path.to_string_lossy(),
        ],
        &[],
    );
    let out = match res {
        Ok(true) => fs::read(&sig_path).map(Some).map_err(TrustError::Io),
        Ok(false) => Err(TrustError::Sign("minisign refused to sign".into())),
        Err(e) => Err(TrustError::Sign(format!("could not run minisign: {e}"))),
    };
    let _ = fs::remove_file(&data_file);
    let _ = fs::remove_file(&sig_path);
    out
}

// Map a process result to a verdict: success is valid, a clean non-zero exit is
// invalid, a spawn failure (tool absent) is unavailable.
fn verdict_of(res: Result<bool, io::Error>, identity: Option<String>) -> Verdict {
    match res {
        Ok(true) => Verdict::Valid { identity },
        Ok(false) => Verdict::Invalid("signature did not verify".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            Verdict::Unavailable("signing tool not found on PATH".into())
        }
        Err(e) => Verdict::Unavailable(format!("could not run verifier: {e}")),
    }
}

// Run a tool feeding `stdin`, returning its stdout on success or a `Sign` error
// carrying stderr on failure.
fn run_capturing(tool: &str, args: &[&str], stdin: &[u8]) -> Result<Vec<u8>, TrustError> {
    let mut child = Command::new(tool)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| TrustError::Sign(format!("could not run {tool}: {e}")))?;
    child
        .stdin
        .take()
        .expect("stdin was piped")
        .write_all(stdin)?;
    let out = child
        .wait_with_output()
        .map_err(|e| TrustError::Sign(format!("{tool} failed: {e}")))?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(TrustError::Sign(
            String::from_utf8_lossy(&out.stderr).trim().to_string(),
        ))
    }
}

// Run a tool feeding `stdin`, returning whether it exited zero. A spawn failure
// (tool not installed) is surfaced as the io error so callers can distinguish
// "absent" from "rejected".
fn run_status(tool: &str, args: &[&str], stdin: &[u8]) -> Result<bool, io::Error> {
    let mut child = Command::new(tool)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()?;
    child
        .stdin
        .take()
        .expect("stdin was piped")
        .write_all(stdin)?;
    Ok(child.wait()?.success())
}

// A unique temp path for staging a blob a CLI tool must read from a file. The
// `.tmp` marker and pid/counter keep concurrent signers from colliding.
fn write_temp(tag: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let path = std::env::temp_dir().join(format!(
        "prism-pkg.{tag}.{}.{nanos}.{n}",
        std::process::id()
    ));
    fs::write(&path, bytes)?;
    Ok(path)
}

/// The local append-only transparency log: every `origin/name/tag -> root`
/// pointer ever published, with a monotonic sequence, so a repoint is detectable.
#[derive(Debug)]
pub struct Log {
    path: PathBuf,
}

/// One recorded pointer in the transparency log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogEntry {
    /// The monotonic sequence number, dense from zero in append order.
    pub seq: u64,
    /// The wall-clock nanoseconds the entry was appended.
    pub time_nanos: u128,
    /// The canonical package identity.
    pub origin: String,
    /// The published name.
    pub name: String,
    /// The published git tag.
    pub tag: String,
    /// The hash scheme that gives `root` its meaning.
    pub scheme: String,
    /// The artifact kind the root names.
    pub kind: String,
    /// The root hash the name and tag were pointed at.
    pub root: String,
}

/// A detected repoint: an `(origin, name, tag)` that the log shows pointed at more
/// than one root over time. The presence of any repoint is the signal `audit`
/// surfaces.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Repoint {
    /// The repointed package identity.
    pub origin: String,
    /// The repointed name.
    pub name: String,
    /// The repointed tag.
    pub tag: String,
    /// The root it pointed at first.
    pub from_root: String,
    /// The hash scheme for `from_root`.
    pub from_scheme: String,
    /// The artifact kind for `from_root`.
    pub from_kind: String,
    /// The root it was later repointed to.
    pub to_root: String,
    /// The hash scheme for `to_root`.
    pub to_scheme: String,
    /// The artifact kind for `to_root`.
    pub to_kind: String,
}

impl Log {
    /// A log rooted at `path` (the file need not exist yet).
    #[must_use]
    pub fn at(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    /// Append a pointer, returning its assigned sequence number.
    ///
    /// Verify-on-append: the prior entries are read (never rewritten) to assign the
    /// next dense sequence, then one line is appended. A crash can only lose the
    /// tail, never corrupt earlier history.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn append(
        &self,
        origin: &str,
        name: &str,
        tag: &str,
        scheme: &str,
        kind: &str,
        root: &str,
    ) -> io::Result<u64> {
        let existing = self.entries()?;
        let seq = existing.len() as u64;
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut f = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)?;
        if existing.is_empty() {
            writeln!(f, "{LOG_HEADER_V4}")?;
        }
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        writeln!(
            f,
            "{seq}{FIELD_SEP}{nanos}{FIELD_SEP}{origin}{FIELD_SEP}{name}{FIELD_SEP}{tag}{FIELD_SEP}{scheme}{FIELD_SEP}{kind}{FIELD_SEP}{root}"
        )?;
        Ok(seq)
    }

    /// Every entry, in append order. A missing log is empty.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed header.
    pub fn entries(&self) -> io::Result<Vec<LogEntry>> {
        let text = match fs::read_to_string(&self.path) {
            Ok(t) => t,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e),
        };
        let mut lines = text.lines();
        let header = lines.next();
        if header != Some(LOG_HEADER_V1)
            && header != Some(LOG_HEADER_V2)
            && header != Some(LOG_HEADER_V3)
            && header != Some(LOG_HEADER_V4)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("malformed transparency log at {}", self.path.display()),
            ));
        }
        let mut out = Vec::new();
        for line in lines {
            let fields: Vec<&str> = line.split(FIELD_SEP).collect();
            match (header, fields.as_slice()) {
                (Some(LOG_HEADER_V1), [seq, time, name, tag, root]) => out.push(LogEntry {
                    seq: seq.parse().unwrap_or_default(),
                    time_nanos: time.parse().unwrap_or_default(),
                    origin: (*name).to_string(),
                    name: (*name).to_string(),
                    tag: (*tag).to_string(),
                    scheme: HASH_SCHEME.to_string(),
                    kind: INDEX_KIND_NAMESPACE.to_string(),
                    root: (*root).to_string(),
                }),
                (Some(LOG_HEADER_V2), [seq, time, name, tag, scheme, root]) => {
                    out.push(LogEntry {
                        seq: seq.parse().unwrap_or_default(),
                        time_nanos: time.parse().unwrap_or_default(),
                        origin: (*name).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: INDEX_KIND_NAMESPACE.to_string(),
                        root: (*root).to_string(),
                    });
                }
                (Some(LOG_HEADER_V3), [seq, time, name, tag, scheme, kind, root]) => {
                    out.push(LogEntry {
                        seq: seq.parse().unwrap_or_default(),
                        time_nanos: time.parse().unwrap_or_default(),
                        origin: (*name).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: (*root).to_string(),
                    });
                }
                (Some(LOG_HEADER_V4), [seq, time, origin, name, tag, scheme, kind, root]) => {
                    out.push(LogEntry {
                        seq: seq.parse().unwrap_or_default(),
                        time_nanos: time.parse().unwrap_or_default(),
                        origin: (*origin).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: (*root).to_string(),
                    });
                }
                _ => {}
            }
        }
        Ok(out)
    }

    /// The repoints the log records: each `(origin, name, tag)` whose root changed
    /// between two entries. An empty result means no published pointer was ever
    /// moved.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed log.
    pub fn repoints(&self) -> io::Result<Vec<Repoint>> {
        let mut latest: BTreeMap<(String, String, String), (String, String, String)> =
            BTreeMap::new();
        let mut out = Vec::new();
        for e in self.entries()? {
            let key = (e.origin.clone(), e.name.clone(), e.tag.clone());
            if let Some(prev) = latest.get(&key) {
                if prev != &(e.scheme.clone(), e.kind.clone(), e.root.clone()) {
                    out.push(Repoint {
                        origin: e.origin.clone(),
                        name: e.name.clone(),
                        tag: e.tag.clone(),
                        from_scheme: prev.0.clone(),
                        from_kind: prev.1.clone(),
                        from_root: prev.2.clone(),
                        to_scheme: e.scheme.clone(),
                        to_kind: e.kind.clone(),
                        to_root: e.root.clone(),
                    });
                }
            }
            latest.insert(key, (e.scheme, e.kind, e.root));
        }
        Ok(out)
    }
}

/// The receipt `prism publish` returns: the pointer it recorded, its log sequence,
/// how it was signed, and the exact `git tag` command the operator runs to cut the
/// matching tag in their own repository.
#[derive(Debug, Clone)]
pub struct PublishReceipt {
    /// The `origin -> name -> tag -> root` pointer written to the signed index.
    pub row: IndexRow,
    /// The transparency-log sequence assigned to this pointer.
    pub seq: u64,
    /// Whether the emitted index carried a signature.
    pub signed: bool,
    /// The signing mode in force.
    pub mode: SignMode,
    /// The `git tag` command to run in the source repository; Prism never runs it
    /// itself, because the tag belongs to the operator's workflow.
    pub git_tag_cmd: String,
}

/// Publish an `origin/name/tag -> root` pointer: upsert it into the signed index,
/// sign the new index, write it through the transport, and append the pointer to
/// the local transparency log.
///
/// The objects the root closes over are assumed already published; this records
/// only the authenticated pointer to them (tag-plus-signed-pointer).
///
/// # Errors
/// A signing failure, or a transport/filesystem error writing the index or log.
pub fn publish<T: Transport + ?Sized>(
    dst: &T,
    log: &Log,
    row: IndexRow,
    flags: &DynFlags,
) -> Result<PublishReceipt, TrustError> {
    let current = dst
        .index_artifact()?
        .map(|a| parse_index(&a.body))
        .unwrap_or_default();
    let rows = upsert(&current, row.clone());
    let body = serialize_index(&rows);
    let sig = sign(&body, flags)?;
    let signed = sig.is_some();
    dst.publish_index(&SignedArtifact { body, sig })?;
    let seq = log.append(
        &row.origin,
        &row.name,
        &row.tag,
        &row.scheme,
        &row.kind,
        &row.root,
    )?;
    let git_tag_cmd = format!(
        "git tag -a {} -m 'prism {} -> {}'",
        row.tag, row.name, row.root
    );
    Ok(PublishReceipt {
        row,
        seq,
        signed,
        mode: flags.sign_mode,
        git_tag_cmd,
    })
}

/// The per-root result of an audit: the pointer checked, and either the number of
/// objects re-verified in its closure or the named failure.
#[derive(Debug, Clone)]
pub struct RootAudit {
    /// The pointer that was audited.
    pub pointer: IndexRow,
    /// `Ok(objects verified)` for a green root, `Err(reason)` for a failure.
    pub outcome: Result<usize, String>,
    /// The certificate the root carries, if any. An absent certificate is not a
    /// failure; a corrupt or foreign-scheme one is, and fails the whole audit.
    pub cert: CertStatus,
}

/// The whole audit outcome: the index signature verdict, the per-root results, and
/// any repoints the transparency log revealed.
#[derive(Debug, Clone)]
pub struct AuditReport {
    /// The verdict on the signed index's signature.
    pub verdict: Verdict,
    /// One entry per locked root.
    pub rows: Vec<RootAudit>,
    /// Repoints detected in the transparency log (a published pointer that moved).
    pub repoints: Vec<Repoint>,
}

impl AuditReport {
    /// Whether the whole audit passed: every root green, every certificate sound
    /// (absent or verifiable, never corrupt), and no repoint detected.
    #[must_use]
    pub fn ok(&self) -> bool {
        self.repoints.is_empty()
            && self
                .rows
                .iter()
                .all(|r| r.outcome.is_ok() && !matches!(r.cert, CertStatus::Failed(_)))
    }

    /// A one-line-per-root rendering: the signature verdict, then a green `ok` or a
    /// named failure for each root, then any repoint warnings.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "index signature: {}", verdict_label(&self.verdict));
        for r in &self.rows {
            let short = short_hash(&r.pointer.root);
            match &r.outcome {
                Ok(n) => {
                    let _ = writeln!(
                        out,
                        "ok    {} {}@{}  {short}  ({n} objects verified){}",
                        r.pointer.origin,
                        r.pointer.name,
                        r.pointer.tag,
                        cert_suffix(&r.cert)
                    );
                }
                Err(reason) => {
                    let _ = writeln!(
                        out,
                        "FAIL  {} {}@{}  {short}  {reason}{}",
                        r.pointer.origin,
                        r.pointer.name,
                        r.pointer.tag,
                        cert_suffix(&r.cert)
                    );
                }
            }
        }
        for rp in &self.repoints {
            let _ = writeln!(
                out,
                "REPOINT {} {}@{}: {} -> {} (transparency log records a moved pointer)",
                rp.origin,
                rp.name,
                rp.tag,
                short_hash(&rp.from_root),
                short_hash(&rp.to_root)
            );
        }
        out
    }
}

/// Re-verify every locked root against the local store and check each pointer
/// against the signed index and the transparency log.
///
/// Integrity (a hash check over each root's closure) needs no signature; the index
/// verdict and the log check establish authenticity. A repoint anywhere in the log
/// fails the whole audit.
///
/// # Errors
/// A transport error reading the index, or a filesystem error reading the log.
pub fn audit(
    store: &Store,
    index: &dyn Transport,
    log: &Log,
    locked: &[IndexRow],
    baseline: &BTreeSet<String>,
    flags: &DynFlags,
    allow_unsigned: bool,
) -> Result<AuditReport, TrustError> {
    let artifact = index.index_artifact()?;
    let verdict = artifact.as_ref().map_or_else(
        || Verdict::Unavailable("no signed index has been published".into()),
        |a| verify_signature(a, flags),
    );
    let index_rows = artifact
        .as_ref()
        .map(|a| parse_index(&a.body))
        .unwrap_or_default();
    let sig_problem = signature_problem(&verdict, allow_unsigned);
    let repoints = log.repoints()?;
    let log_entries = log.entries()?;
    // Integrity is a hash check over the objects the store committed, computed once
    // and shared by every pointer (a namespace root is a fold over its members, not
    // a walkable object, so the members are the walk roots).
    let integrity = verify_all(store, baseline).map_err(|e| format!("store integrity: {e}"));

    let rows = locked
        .iter()
        .map(|p| RootAudit {
            pointer: p.clone(),
            outcome: audit_one(
                &index_rows,
                &log_entries,
                p,
                sig_problem.as_deref(),
                &integrity,
            ),
            cert: check_cert(store, &p.root),
        })
        .collect();

    Ok(AuditReport {
        verdict,
        rows,
        repoints,
    })
}

// The full per-root check: signature policy, then authenticity against the signed
// index, then presence in the transparency log, then the shared store-integrity
// result.
fn audit_one(
    index_rows: &[IndexRow],
    log_entries: &[LogEntry],
    p: &IndexRow,
    sig_problem: Option<&str>,
    integrity: &Result<usize, String>,
) -> Result<usize, String> {
    if let Some(msg) = sig_problem {
        return Err(msg.to_string());
    }
    match index_rows
        .iter()
        .find(|r| r.origin == p.origin && r.name == p.name && r.tag == p.tag)
    {
        None => {
            return Err(format!(
                "no signed index pointer for {} {}@{}",
                p.origin, p.name, p.tag
            ));
        }
        Some(r) if r.scheme != HASH_SCHEME => {
            return Err(format!(
                "signed index points {} {}@{} at foreign scheme {}; this build speaks {}",
                p.origin, p.name, p.tag, r.scheme, HASH_SCHEME
            ));
        }
        Some(r) if r.scheme != p.scheme => {
            return Err(format!(
                "signed index points {} {}@{} under scheme {}, lock pins scheme {}",
                p.origin, p.name, p.tag, r.scheme, p.scheme
            ));
        }
        Some(r) if r.kind != p.kind => {
            return Err(format!(
                "signed index points {} {}@{} at kind {}, lock pins kind {}",
                p.origin, p.name, p.tag, r.kind, p.kind
            ));
        }
        Some(r) if r.root != p.root => {
            return Err(format!(
                "signed index points {} {}@{} at {}, lock pins {}",
                p.origin,
                p.name,
                p.tag,
                short_hash(&r.root),
                short_hash(&p.root)
            ))
        }
        Some(_) => {}
    }
    if !log_entries.iter().any(|e| {
        e.name == p.name
            && e.tag == p.tag
            && e.origin == p.origin
            && e.scheme == p.scheme
            && e.kind == p.kind
            && e.root == p.root
    }) {
        return Err(format!(
            "pointer {} {}@{} is absent from the transparency log",
            p.origin, p.name, p.tag
        ));
    }
    integrity.clone()
}

// Whether the signature verdict blocks acceptance, and why. `None` means the
// signature is acceptable under the current policy.
fn signature_problem(verdict: &Verdict, allow_unsigned: bool) -> Option<String> {
    match verdict {
        Verdict::Valid { .. } => None,
        Verdict::Unsigned if allow_unsigned => None,
        Verdict::Unsigned => {
            Some("index is unsigned (pass the unsigned override to accept dev mode)".into())
        }
        Verdict::Invalid(m) => Some(format!("index signature did not verify: {m}")),
        Verdict::Unavailable(m) => Some(format!("index signature unverifiable: {m}")),
    }
}

// The certificate annotation appended to a root's audit line. Absent adds nothing;
// a verifiable or reserved cert reports itself; a failed cert names the corruption.
fn cert_suffix(status: &CertStatus) -> String {
    match status {
        CertStatus::Absent => String::new(),
        CertStatus::Verified(desc) => format!("  cert: {desc}"),
        CertStatus::Unverifiable(desc) => format!("  cert: {desc} [unverifiable]"),
        CertStatus::Failed(reason) => format!("  cert: FAIL {reason}"),
    }
}

fn verdict_label(verdict: &Verdict) -> String {
    match verdict {
        Verdict::Valid { identity: Some(id) } => format!("valid ({id})"),
        Verdict::Valid { identity: None } => "valid".into(),
        Verdict::Unsigned => "unsigned (dev mode)".into(),
        Verdict::Invalid(m) => format!("INVALID: {m}"),
        Verdict::Unavailable(m) => format!("unverifiable: {m}"),
    }
}

// A short hash prefix for human-facing lines, matching the store's display habit.
fn short_hash(hash: &str) -> &str {
    let n = crate::core::HASH_PREFIX_HEX.min(hash.len());
    &hash[..n]
}

// The local transparency log lives beside the signed index, under the store's
// `pkg/` directory. Local-only: never fetched, only appended to.
const LOG_LOCAL_FILE: &str = "log";

/// The transparency log for the store rooted at `store_root`.
#[must_use]
pub fn store_log(store_root: &Path) -> Log {
    Log::at(pkg_dir(store_root).join(LOG_LOCAL_FILE))
}

/// The `prism publish` command body: commit the program, cut a signed pointer at
/// `tag`, and return the human-facing receipt to print.
///
/// Objects are committed into the store, the namespace root is derived, and the
/// `(origin, name, tag, root)` pointer is written to the signed index and the
/// local log. The matching git tag is the operator's to create; its exact command
/// is included rather than run.
///
/// # Errors
/// A front-end error, a signing failure, or a store/filesystem error.
pub fn publish_cmd(
    full_src: &str,
    roots: &[Root],
    name: &str,
    tag: &str,
    cfg: &Config,
) -> Result<String, Error> {
    crate::commit_to_store(full_src, roots, cfg)?;
    let identity = crate::namespace_identity(full_src, roots)?;
    let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
    let dst = DiskTransport::open(&store_root)?;
    let log = store_log(&store_root);
    let row = IndexRow {
        origin: name.to_string(),
        name: name.to_string(),
        tag: tag.to_string(),
        scheme: identity.scheme.to_string(),
        kind: identity.kind.to_string(),
        root: identity.root,
    };
    let receipt = publish(&dst, &log, row, &cfg.flags)?;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "published {} {}@{} -> {}",
        receipt.row.origin, receipt.row.name, receipt.row.tag, receipt.row.root
    );
    if receipt.signed {
        let _ = writeln!(out, "  index signed with {}", receipt.mode.label());
    } else {
        let _ = writeln!(
            out,
            "  index is UNSIGNED ({}) -- not for distribution; `prism audit` rejects it \
             without the unsigned override",
            receipt.mode.label()
        );
    }
    let _ = writeln!(out, "  transparency log sequence {}", receipt.seq);
    let _ = writeln!(out, "next, cut the matching tag in your source repository:");
    let _ = writeln!(out, "  {}", receipt.git_tag_cmd);
    Ok(out)
}

/// The `prism publish` source-package command body used by the CLI.
///
/// This preserves the existing namespace-pointer publisher above for lower-level
/// tests, but gives the package build path a source artifact it can actually put
/// on the module search path: a deterministic source bundle keyed by the bundle's
/// BLAKE3 digest and authenticated by the signed index.
///
/// # Errors
/// A front-end error, a signing failure, or a store/filesystem error.
pub fn publish_source_cmd(
    user_src: &str,
    full_src: &str,
    roots: &[Root],
    origin: &str,
    name: &str,
    tag: &str,
    cfg: &Config,
) -> Result<String, Error> {
    crate::commit_to_store(full_src, roots, cfg)?;
    let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
    let store = Store::open_or_create(&store_root)?;
    let bundle = encode_source_bundle([(name, user_src)]);
    let root = blake3::hash(&bundle).to_hex().to_string();
    store.put(&root, &bundle)?;
    let dst = DiskTransport::open(&store_root)?;
    let log = store_log(&store_root);
    let row = IndexRow {
        origin: origin.to_string(),
        name: name.to_string(),
        tag: tag.to_string(),
        scheme: HASH_SCHEME.to_string(),
        kind: INDEX_KIND_SOURCE.to_string(),
        root,
    };
    let receipt = publish(&dst, &log, row, &cfg.flags)?;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "published {} {}@{} -> {}",
        receipt.row.origin, receipt.row.name, receipt.row.tag, receipt.row.root
    );
    if receipt.signed {
        let _ = writeln!(out, "  index signed with {}", receipt.mode.label());
    } else {
        let _ = writeln!(
            out,
            "  index is UNSIGNED ({}) -- not for distribution; `prism audit` rejects it \
             without the unsigned override",
            receipt.mode.label()
        );
    }
    let _ = writeln!(
        out,
        "  source bundle stored for module {}",
        receipt.row.name
    );
    let _ = writeln!(out, "  transparency log sequence {}", receipt.seq);
    let _ = writeln!(out, "next, cut the matching tag in your source repository:");
    let _ = writeln!(out, "  {}", receipt.git_tag_cmd);
    Ok(out)
}

/// The `prism audit` command body: re-verify every pointer the signed index
/// publishes against the local store and the transparency log.
///
/// Each pointer's root closure is re-hashed against the store, the pointer is
/// checked against the signed index and the log, and any repoint fails the audit.
/// Returns the full report; the caller renders it and sets the exit code from
/// [`AuditReport::ok`].
///
/// # Errors
/// A front-end error deriving the shared baseline, or a store/filesystem error.
pub fn audit_cmd(cfg: &Config, allow_unsigned: bool) -> Result<AuditReport, Error> {
    let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
    let dst = DiskTransport::open(&store_root)?;
    // Absent a lockfile, audit every pointer the signed index publishes; the typed
    // `audit` entry point accepts a lock-derived pin set when one is available.
    let locked = dst
        .index_artifact()?
        .map(|a| parse_index(&a.body))
        .unwrap_or_default();
    let baseline = stdlib_baseline()?;
    let log = store_log(&store_root);
    let report = audit(
        dst.store(),
        &dst,
        &log,
        &locked,
        &baseline,
        &cfg.flags,
        allow_unsigned,
    )?;
    Ok(report)
}
