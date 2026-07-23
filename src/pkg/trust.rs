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
//! published identity is detectable after the fact. Each line commits the digest
//! of the previous line (rooted at the header), so an in-place edit anywhere
//! breaks every later link and reads fail loudly; the chain head is exposed
//! through `audit` as the one value an external witness pins, which is what
//! makes a cleanly truncated suffix (the only mutilation a local check cannot
//! see) detectable after the fact. This is the log's local rung: no gossip
//! protocol, just an on-disk record that is only appended to, never rewritten,
//! plus one head hash worth writing down somewhere else.
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
#[cfg(unix)]
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(unix)]
use rustix::fs::{flock, FlockOperation};

use crate::core::{Digest, HASH_SCHEME};
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

// Line-oriented, tab-separated artifact formats. A row is one line; hashes and
// git tags contain no tab, so the separator is unambiguous. This compiler is
// still pre-stability, so the trust surface accepts only the current protocol.
const INDEX_HEADER: &str = "prism-pkg-index\tv4";
const LOG_HEADER: &str = "prism-pkg-log\tv5";
const FIELD_SEP: char = '\t';

// The digest a chained log line carries for its predecessor: the previous
// line's exact bytes (no newline), in the provenance scheme spelling.
fn line_digest(line: &str) -> String {
    format!(
        "{}:{}",
        crate::lineage::provenance::EVENT_HASH_SCHEME,
        crate::lineage::provenance::sha256_hex(line.as_bytes())
    )
}

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
    pub root: Digest,
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
            other => Self::ResolvePackage(other.to_string()),
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
    if header != Some(INDEX_HEADER) {
        return Vec::new();
    }
    lines
        .filter_map(|line| {
            let fields: Vec<&str> = line.split(FIELD_SEP).collect();
            match (header, fields.as_slice()) {
                (Some(INDEX_HEADER), [origin, name, tag, scheme, kind, root])
                    if !origin.is_empty() && !name.is_empty() =>
                {
                    Some(IndexRow {
                        origin: (*origin).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: Digest::from(*root),
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
    let mut body = String::from(INDEX_HEADER);
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
                (r.scheme.clone(), r.kind.clone(), r.root.to_string()),
            )
        })
        .collect();
    map.insert(
        (row.origin.clone(), row.name.clone(), row.tag.clone()),
        (row.scheme, row.kind, row.root.into_string()),
    );
    map.into_iter()
        .map(|((origin, name, tag), (scheme, kind, root))| IndexRow {
            origin,
            name,
            tag,
            root: Digest::from(root),
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
    let Some(identity) = flags.sign_identity.as_deref() else {
        return Verdict::Unavailable(
            "ssh verify needs a signer identity: set PRISM_SIGN_IDENTITY".into(),
        );
    };
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
            identity,
            "-n",
            SIG_NAMESPACE,
            "-s",
            &sig_file.to_string_lossy(),
        ],
        body,
    );
    remove_temp(&sig_file);
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
            remove_temp(&data_file);
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
    remove_temp(&data_file);
    remove_temp(&sig_file);
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
    // `sig_path` is a sibling of `data_file` in the same private directory, so
    // removing that directory cleans both.
    remove_temp(&data_file);
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

// The shared prefix for Prism's private temp directories and the files staged in
// them, so they are recognizable in a system temp dir.
const TEMP_NAME_PREFIX: &str = "prism-pkg";

// Mode bits for a freshly created private staging directory: owner-only rwx, so
// no other user can plant a symlink into it or read a staged blob mid-operation.
#[cfg(unix)]
const PRIVATE_DIR_MODE: u32 = 0o700;

/// Create a fresh, private (0700 on unix) directory under the system temp dir and
/// return its path.
///
/// The name is unique per call (process id, a process-local counter, and the wall
/// clock), and the directory is created with mkdir semantics that fail on a
/// pre-existing path rather than following it, so a planted symlink or a squatted
/// name cannot redirect what is written inside. Staging a blob or an executable in
/// a directory made this way, instead of at a predictable shared-temp path, closes
/// the symlink-follow and name-prediction races a fixed `temp_dir()/name` opens.
///
/// # Errors
/// A filesystem error other than a name collision, which is retried.
pub(crate) fn private_temp_dir(tag: &str) -> io::Result<PathBuf> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let base = std::env::temp_dir();
    loop {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let dir = base.join(format!(
            "{TEMP_NAME_PREFIX}.{tag}.{}.{nanos}.{n}",
            std::process::id()
        ));
        // Both branches use mkdir semantics that fail on a pre-existing path; the
        // unix branch additionally clamps the mode to owner-only.
        #[cfg(unix)]
        let created = {
            let mut builder = fs::DirBuilder::new();
            builder.mode(PRIVATE_DIR_MODE);
            builder.create(&dir)
        };
        #[cfg(not(unix))]
        let created = fs::create_dir(&dir);
        match created {
            Ok(()) => return Ok(dir),
            // A name collision is the one recoverable case: loop for a fresh name
            // rather than reuse a directory that may not be ours.
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e),
        }
    }
}

// Stage a blob a CLI tool must read from a file, inside a freshly created private
// directory. Returns the file path; `remove_temp` cleans up the whole directory.
fn write_temp(tag: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    let path = private_temp_dir(tag)?.join(tag);
    fs::write(&path, bytes)?;
    Ok(path)
}

// Remove a file staged by `write_temp` along with the private directory that held
// it, best-effort. A sibling produced beside the staged file (a detached
// signature written next to it) shares that directory, so one removal cleans both.
fn remove_temp(path: &Path) {
    match path.parent() {
        Some(dir) => {
            let _ = fs::remove_dir_all(dir);
        }
        None => {
            let _ = fs::remove_file(path);
        }
    }
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
    pub root: Digest,
    /// The chain link: the digest of the previous log line's exact bytes
    /// (`sha256:<hex>`, the header line for entry zero).
    pub prev: Option<String>,
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

// The sibling file whose advisory lock serializes transparency-log appenders: the
// log path with this extension.
const LOG_LOCK_EXTENSION: &str = "lock";

// The advisory lock held across a transparency-log append. `append` is a
// read-modify-write, and an exclusive `flock` on a sibling lock file makes two
// concurrent appenders serialize instead of racing to the same sequence off a
// stale prev digest. The kernel drops the lock when the handle closes, including
// on a crash, so a killed publisher never strands it. Non-unix targets (the wasm
// build has no real filesystem) degrade to a no-op. Holding the open handle is
// holding the lock; dropping it (closing the file) releases it.
struct AppendLock {
    _file: fs::File,
}

impl AppendLock {
    fn acquire(log_path: &Path) -> io::Result<Self> {
        let lock_path = log_path.with_extension(LOG_LOCK_EXTENSION);
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)?;
        lock_exclusive(&file)?;
        Ok(Self { _file: file })
    }
}

// Take the exclusive advisory lock, blocking until no other handle holds it.
#[cfg(unix)]
fn lock_exclusive(file: &fs::File) -> io::Result<()> {
    flock(file, FlockOperation::LockExclusive).map_err(io::Error::from)
}

#[cfg(not(unix))]
fn lock_exclusive(_file: &fs::File) -> io::Result<()> {
    Ok(())
}

impl Log {
    /// A log rooted at `path` (the file need not exist yet).
    #[must_use]
    pub fn at(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    /// Append a pointer, returning its assigned sequence number.
    ///
    /// Verify-on-append: the prior entries are read (never rewritten, and
    /// rejected if mutilated) before one line is appended, so an append can only
    /// ever extend a valid dense log. A crash can only lose the tail, never
    /// corrupt earlier history. What no local check can detect is a cleanly
    /// truncated suffix, a shortened log that is internally consistent; that
    /// requires an external witness holding a later sequence number, which is
    /// what `audit` against a remote index provides.
    ///
    /// # Errors
    /// Fails on a filesystem error or a log `entries` rejects as mutilated.
    pub fn append(
        &self,
        origin: &str,
        name: &str,
        tag: &str,
        scheme: &str,
        kind: &str,
        root: &str,
    ) -> io::Result<u64> {
        // The parent must exist before the sibling lock file can be created there.
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        // Serialize the whole read-modify-write. Without exclusion two concurrent
        // publishers read the same tail, compute the same sequence off the same
        // prev digest, and the second appended line breaks the chain so every
        // later audit read fails. The lock releases when `_lock` drops at exit.
        let _lock = AppendLock::acquire(&self.path)?;
        let text = self.read_text()?.unwrap_or_default();
        let existing = self.parse(&text)?;
        // The next sequence comes from the last entry's own number, never from a
        // count: a count silently renumbers into any hole, while continuing from
        // the recorded maximum keeps the numbers a property of the entries
        // themselves (and `parse` has already rejected a non-dense log).
        let seq = existing.last().map_or(0, |e| e.seq + 1);
        let mut f = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)?;
        // The header is owed exactly when the file has no bytes yet (fresh, or
        // left empty by a crash between create and header write, which this
        // heals). Keying on `existing.is_empty()` instead would write a second
        // header into a crashed header-only file.
        let need_header = f.metadata()?.len() == 0;
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        // One buffered write for header plus line, so the crash window between
        // them is a single syscall rather than two.
        let mut out = String::new();
        if need_header {
            out.push_str(LOG_HEADER);
            out.push('\n');
        }
        // Chained format: each line commits the previous line's bytes, the first
        // entry committing the header itself, so any in-place edit breaks every
        // later link.
        let prev_line = if need_header {
            LOG_HEADER
        } else {
            text.lines().last().unwrap_or(LOG_HEADER)
        };
        let prev = line_digest(prev_line);
        let _ = writeln!(
            out,
            "{seq}{FIELD_SEP}{nanos}{FIELD_SEP}{prev}{FIELD_SEP}{origin}{FIELD_SEP}{name}{FIELD_SEP}{tag}{FIELD_SEP}{scheme}{FIELD_SEP}{kind}{FIELD_SEP}{root}"
        );
        f.write_all(out.as_bytes())?;
        Ok(seq)
    }

    /// The chain head: the digest of the last line of a chained (v5) log, the
    /// value an external witness pins so a cleanly truncated suffix is
    /// detectable after the fact. `None` for a missing or empty log.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn head(&self) -> io::Result<Option<String>> {
        let Some(text) = self.read_text()? else {
            return Ok(None);
        };
        if text.lines().next() != Some(LOG_HEADER) {
            return Ok(None);
        }
        Ok(text.lines().last().map(line_digest))
    }

    fn read_text(&self) -> io::Result<Option<String>> {
        match fs::read_to_string(&self.path) {
            Ok(t) => Ok(Some(t)),
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Every entry, in append order. A missing log is empty.
    ///
    /// # Errors
    /// Fails on a filesystem error, a malformed header or line, or a log whose
    /// sequence numbers are not dense from zero (evidence of a hole or a
    /// reordering; the log is tamper-evident, so it fails loudly rather than
    /// pretending the surviving lines are the whole history).
    pub fn entries(&self) -> io::Result<Vec<LogEntry>> {
        let Some(text) = self.read_text()? else {
            return Ok(Vec::new());
        };
        self.parse(&text)
    }

    // The one parser behind `entries` and `append`: header dispatch, per-line
    // shape checks, chain verification (v5), and the dense-from-zero check.
    fn parse(&self, text: &str) -> io::Result<Vec<LogEntry>> {
        // A zero-byte (or whitespace-only) file is an uninitialized log, not a
        // malformed one: a crash between file creation and the header write
        // leaves exactly this state, and `append` heals it by writing the
        // header. Treating it as malformed would brick publishing permanently.
        if text.trim().is_empty() {
            return Ok(Vec::new());
        }
        let malformed = |what: &str| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "malformed transparency log at {}: {what}",
                    self.path.display()
                ),
            )
        };
        let mut lines = text.lines();
        let header = lines.next();
        if header != Some(LOG_HEADER) {
            return Err(malformed("unrecognized header"));
        }
        // The chain pointer each v5 line must carry: the digest of the previous
        // line's exact bytes, rooted at the header line.
        let mut prev_line = header.unwrap_or_default();
        let parse_seq = |s: &str| {
            s.parse::<u64>()
                .map_err(|_| malformed(&format!("unparseable sequence number `{s}`")))
        };
        let mut out = Vec::new();
        for line in lines {
            let fields: Vec<&str> = line.split(FIELD_SEP).collect();
            match (header, fields.as_slice()) {
                (Some(LOG_HEADER), [seq, time, prev, origin, name, tag, scheme, kind, root]) => {
                    let want = line_digest(prev_line);
                    if *prev != want {
                        return Err(malformed(&format!(
                            "chain break before seq {seq}: line commits `{prev}`, previous line hashes to `{want}`"
                        )));
                    }
                    out.push(LogEntry {
                        seq: parse_seq(seq)?,
                        time_nanos: time.parse().unwrap_or_default(),
                        origin: (*origin).to_string(),
                        name: (*name).to_string(),
                        tag: (*tag).to_string(),
                        scheme: (*scheme).to_string(),
                        kind: (*kind).to_string(),
                        root: Digest::from(*root),
                        prev: Some((*prev).to_string()),
                    });
                }
                // A line that fits no known shape is evidence, not noise:
                // skipping it would desynchronize the sequence numbering and
                // hide whatever put it there.
                _ => return Err(malformed(&format!("unrecognized line `{line}`"))),
            }
            prev_line = line;
        }
        // The dense-from-zero promise is checked, not assumed: a gap or
        // regression means lines were lost or reordered after they were written.
        for (i, e) in out.iter().enumerate() {
            if e.seq != i as u64 {
                return Err(malformed(&format!(
                    "sequence hole: entry at position {i} carries seq {}",
                    e.seq
                )));
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
                if prev != &(e.scheme.clone(), e.kind.clone(), e.root.to_string()) {
                    out.push(Repoint {
                        origin: e.origin.clone(),
                        name: e.name.clone(),
                        tag: e.tag.clone(),
                        from_scheme: prev.0.clone(),
                        from_kind: prev.1.clone(),
                        from_root: prev.2.clone(),
                        to_scheme: e.scheme.clone(),
                        to_kind: e.kind.clone(),
                        to_root: e.root.to_string(),
                    });
                }
            }
            latest.insert(key, (e.scheme, e.kind, e.root.into_string()));
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
    /// The transparency log's chain head (chained logs only): the digest an
    /// external witness pins so a cleanly truncated suffix is detectable.
    pub log_head: Option<String>,
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
        if let Some(head) = &self.log_head {
            let _ = writeln!(out, "log head: {head}");
        }
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

    let log_head = log.head()?;
    Ok(AuditReport {
        verdict,
        rows,
        repoints,
        log_head,
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
// The root travels as untrusted deserialized text, so the prefix is taken by
// character count rather than a raw byte slice: a multibyte codepoint straddling
// the byte boundary would panic an index expression but only widens a char cut.
fn short_hash(hash: &str) -> &str {
    match hash.char_indices().nth(crate::core::HASH_PREFIX_HEX) {
        Some((byte, _)) => &hash[..byte],
        None => hash,
    }
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
    let root = Digest::from(blake3::hash(&bundle).to_hex().to_string());
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn short_hash_multibyte_boundary_does_not_panic() {
        // A root whose byte at the prefix length lands inside a multibyte
        // codepoint panics a raw byte slice; the char-boundary cut must not.
        // 15 ASCII chars, then 'e' with acute accent straddling byte 16.
        let root = "0123456789abcde\u{e9}ffff";
        let short = short_hash(root);
        assert_eq!(short, "0123456789abcde\u{e9}");
        assert_eq!(short.chars().count(), crate::core::HASH_PREFIX_HEX);
    }

    #[test]
    fn short_hash_ascii_prefix_is_unchanged() {
        assert_eq!(short_hash("0123456789abcdef0123"), "0123456789abcdef");
        assert_eq!(short_hash("abc"), "abc");
    }

    #[test]
    fn concurrent_appends_serialize_into_a_valid_chain() {
        let dir = private_temp_dir("logtest").expect("temp dir");
        let log = Arc::new(Log::at(dir.join("log")));
        let n: u64 = 8;
        let handles: Vec<_> = (0..n)
            .map(|i| {
                let log = Arc::clone(&log);
                thread::spawn(move || {
                    let name = format!("pkg{i}");
                    log.append(
                        "origin",
                        &name,
                        "v1",
                        HASH_SCHEME,
                        INDEX_KIND_SOURCE,
                        "root",
                    )
                    .expect("append");
                })
            })
            .collect();
        for h in handles {
            h.join().expect("thread");
        }
        // `entries` verifies the chain and the dense-from-zero numbering; a race
        // would have broken a link or duplicated a sequence.
        let entries = log.entries().expect("entries");
        let seqs: Vec<u64> = entries.iter().map(|e| e.seq).collect();
        assert_eq!(seqs, (0..n).collect::<Vec<_>>());
        let _ = fs::remove_dir_all(&dir);
    }
}
