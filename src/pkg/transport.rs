//! Transport as a capability behind a trait, never ambient IO.
//!
//! Fetch and publish are operations on [`Transport`]; the disk and a git remote
//! are implementations of it, not calls scattered through a resolver. The codec
//! never performs IO itself, and a resolver that walks a Merkle closure asks the
//! trait for bytes without knowing whether they come from a local directory or a
//! clone of a remote.
//!
//! Every fetch verifies. [`verify`] re-derives a fetched blob's content hash from
//! the reconstructed Core and rejects it unless it equals the hash that asked for
//! it, so the host is trusted for availability, never for integrity: the same
//! bytes are as good from any mirror because the hash validates them.
//!
//! The canonical adapter is a store serialized into a plain git repository. The
//! on-disk store *is already* a directory of files (`objects/`, `meta/`, `index/`,
//! `VERSION`); a git repository holding that layout is therefore a store, and a
//! git remote is a store a peer can clone. [`GitTransport`] clones and pulls by
//! shelling to the system `git` binary, adding no Rust dependency.

use std::collections::BTreeSet;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::core::Digest;
use crate::pkg::trust::{self, IndexRow, SignedArtifact};
use crate::store::codec::decode_def;
use crate::store::disk::{Store, Written};
use crate::store::CodecError;

/// The failures a transport operation can produce.
#[derive(Debug)]
pub enum TransportError {
    /// A filesystem or process error.
    Io(io::Error),
    /// A fetched blob did not decode as a `def` frame.
    Codec(CodecError),
    /// A fetched blob decoded but did not hash to the key that requested it: the
    /// integrity check that makes an untrusted host safe.
    HashMismatch {
        /// The hash the caller asked for.
        requested: String,
        /// The hash the bytes actually reconstruct to, if they reconstruct at all.
        got: Option<String>,
    },
    /// The object is absent from the backing store.
    Missing(String),
    /// A `git` invocation (or another remote step) failed; the string is the
    /// captured diagnostic.
    Remote(String),
}

impl fmt::Display for TransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "transport io error: {e}"),
            Self::Codec(e) => write!(f, "fetched object did not decode: {e}"),
            Self::HashMismatch { requested, got } => match got {
                Some(g) => write!(
                    f,
                    "integrity failure: object requested as {requested} reconstructs to {g}"
                ),
                None => write!(
                    f,
                    "integrity failure: object requested as {requested} could not be re-hashed"
                ),
            },
            Self::Missing(h) => write!(f, "object {h} is absent from the store"),
            Self::Remote(msg) => write!(f, "remote transport error: {msg}"),
        }
    }
}

impl std::error::Error for TransportError {}

impl From<io::Error> for TransportError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<CodecError> for TransportError {
    fn from(e: CodecError) -> Self {
        Self::Codec(e)
    }
}

impl From<TransportError> for crate::error::Error {
    fn from(e: TransportError) -> Self {
        match e {
            TransportError::Io(io) => Self::Io(io),
            other => Self::ResolvePackage(other.to_string()),
        }
    }
}

/// Re-derive `bytes`' content hash and confirm it equals `hash`.
///
/// The store key is a definition's content hash, so verification is not a checksum
/// over the bytes: the frame is decoded, the anonymous Core group reconstructed,
/// and its content hash recomputed ([`crate::store::codec::Decoded::rehash`]). A
/// tampered blob either fails to decode or reconstructs to a different hash, and
/// both are rejected before the object is ever admitted to a store.
///
/// # Errors
/// [`TransportError::Codec`] if the bytes are not a `def` frame,
/// [`TransportError::HashMismatch`] if they reconstruct to a different hash.
pub fn verify(hash: &str, bytes: &[u8]) -> Result<(), TransportError> {
    let decoded = decode_def(bytes)?;
    match decoded.rehash() {
        Some(h) if h.as_str() == hash => Ok(()),
        got => Err(TransportError::HashMismatch {
            requested: hash.to_string(),
            got: got.map(Digest::into_string),
        }),
    }
}

/// A narrow transport surface: fetch and publish objects, and read or write the
/// one signed package-identity-to-root index. Everything else the package
/// manager does is built over these.
pub trait Transport {
    /// Whether the backing store already holds `hash`. No fetch, no verify, no
    /// network: the warm-cache check a closure walk consults before asking for
    /// bytes.
    fn has(&self, hash: &str) -> bool;

    /// Fetch the `def` object keyed by `hash`, verified against `hash` before it
    /// is returned (see [`verify`]).
    ///
    /// # Errors
    /// [`TransportError::Missing`] if absent, [`TransportError::Codec`] or
    /// [`TransportError::HashMismatch`] if the bytes fail verification, or
    /// [`TransportError::Io`] / [`TransportError::Remote`] on a backing failure.
    fn fetch(&self, hash: &str) -> Result<Vec<u8>, TransportError>;

    /// Publish one `def` object under `hash`. Idempotent: a hash already present
    /// with identical bytes is a [`Written::Hit`], never an overwrite.
    ///
    /// # Errors
    /// [`TransportError::Io`] / [`TransportError::Remote`] on a backing failure, or
    /// a byte mismatch against an existing object.
    fn publish(&self, hash: &str, bytes: &[u8]) -> Result<Written, TransportError>;

    /// The signed package-identity pointers published under `name` (possibly
    /// several tags and origins). Parsed from the index artifact; the signature is
    /// verified separately by the trust layer, not here.
    ///
    /// # Errors
    /// [`TransportError::Io`] / [`TransportError::Remote`] on a backing failure.
    fn fetch_index(&self, name: &str) -> Result<Vec<IndexRow>, TransportError>;

    /// The whole signed index artifact (its rows and its detached signature), for
    /// the trust layer to verify. `None` when no index has been published.
    ///
    /// # Errors
    /// [`TransportError::Io`] / [`TransportError::Remote`] on a backing failure.
    fn index_artifact(&self) -> Result<Option<SignedArtifact>, TransportError>;

    /// Replace the signed index artifact.
    ///
    /// # Errors
    /// [`TransportError::Io`] / [`TransportError::Remote`] on a backing failure.
    fn publish_index(&self, artifact: &SignedArtifact) -> Result<(), TransportError>;
}

// The signed-index artifacts live beside the store's own layers, in a `pkg/`
// subdirectory of the store root, so they clone and pull with the objects: a git
// remote carries the store and its name index in one repository.
const PKG_DIR: &str = "pkg";
const INDEX_FILE: &str = "index";
const INDEX_SIG_FILE: &str = "index.sig";

/// The package-manager artifact directory under a store root (the signed index and
/// the local transparency log). The one place the `pkg/` subdirectory name is
/// spelled.
#[must_use]
pub fn pkg_dir(store_root: &Path) -> PathBuf {
    store_root.join(PKG_DIR)
}

/// A transport backed by a local on-disk store directory.
///
/// The store's object API supplies fetch and publish; the signed index rides in a
/// `pkg/` subdirectory of the same root.
#[derive(Debug)]
pub struct DiskTransport {
    store: Store,
    root: PathBuf,
}

impl DiskTransport {
    /// Open (creating if absent) the store rooted at `root`.
    ///
    /// # Errors
    /// Fails on a filesystem error or a foreign store stamp.
    pub fn open(root: impl AsRef<Path>) -> io::Result<Self> {
        let root = root.as_ref().to_path_buf();
        let store = Store::open_or_create(&root)?;
        Ok(Self { store, root })
    }

    /// The underlying store, for callers that need its metadata/index layers
    /// directly (a closure walk reads objects through it).
    #[must_use]
    pub const fn store(&self) -> &Store {
        &self.store
    }

    /// The store root on disk.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    fn pkg_path(&self, file: &str) -> PathBuf {
        self.root.join(PKG_DIR).join(file)
    }
}

impl Transport for DiskTransport {
    fn has(&self, hash: &str) -> bool {
        self.store.has(hash)
    }

    fn fetch(&self, hash: &str) -> Result<Vec<u8>, TransportError> {
        if !self.store.has(hash) {
            return Err(TransportError::Missing(hash.to_string()));
        }
        let bytes = self.store.get(hash)?;
        verify(hash, &bytes)?;
        Ok(bytes)
    }

    fn publish(&self, hash: &str, bytes: &[u8]) -> Result<Written, TransportError> {
        // Verify before admitting: a publisher never writes an object whose bytes
        // do not match the hash it is filed under.
        verify(hash, bytes)?;
        Ok(self.store.put(hash, bytes)?)
    }

    fn fetch_index(&self, name: &str) -> Result<Vec<IndexRow>, TransportError> {
        let Some(artifact) = self.index_artifact()? else {
            return Ok(Vec::new());
        };
        Ok(trust::parse_index(&artifact.body)
            .into_iter()
            .filter(|r| r.name == name)
            .collect())
    }

    fn index_artifact(&self) -> Result<Option<SignedArtifact>, TransportError> {
        let index = self.pkg_path(INDEX_FILE);
        let body = match fs::read(&index) {
            Ok(b) => b,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let sig = match fs::read(self.pkg_path(INDEX_SIG_FILE)) {
            Ok(s) => Some(s),
            Err(e) if e.kind() == io::ErrorKind::NotFound => None,
            Err(e) => return Err(e.into()),
        };
        Ok(Some(SignedArtifact { body, sig }))
    }

    fn publish_index(&self, artifact: &SignedArtifact) -> Result<(), TransportError> {
        let dir = self.root.join(PKG_DIR);
        fs::create_dir_all(&dir)?;
        fs::write(self.pkg_path(INDEX_FILE), &artifact.body)?;
        let sig_path = self.pkg_path(INDEX_SIG_FILE);
        match &artifact.sig {
            Some(sig) => fs::write(&sig_path, sig)?,
            // An unsigned index leaves no stale signature behind.
            None => {
                if sig_path.exists() {
                    fs::remove_file(&sig_path)?;
                }
            }
        }
        Ok(())
    }
}

/// A transport backed by a git repository whose working tree is a store.
///
/// A remote store is cloned once into a local working directory; thereafter the
/// clone is a [`DiskTransport`], so fetch and index reads are local and verified.
/// Publishing writes objects into the clone's working tree and [`GitTransport::push`]
/// commits and pushes them to the remote in one step. All git access shells to the
/// system binary, so no git library is linked in.
#[derive(Debug)]
pub struct GitTransport {
    remote: String,
    local: DiskTransport,
    clone_dir: PathBuf,
}

impl GitTransport {
    /// Clone `remote` into `clone_dir` (or pull, if the clone already exists) and
    /// open its working tree as a store.
    ///
    /// # Errors
    /// [`TransportError::Remote`] if git fails, [`TransportError::Io`] on a
    /// filesystem error.
    pub fn clone_or_open(
        remote: &str,
        clone_dir: impl AsRef<Path>,
    ) -> Result<Self, TransportError> {
        let clone_dir = clone_dir.as_ref().to_path_buf();
        if clone_dir.join(".git").is_dir() {
            git(&["pull", "--ff-only"], Some(&clone_dir))?;
        } else {
            if let Some(parent) = clone_dir.parent() {
                fs::create_dir_all(parent)?;
            }
            git(
                &["clone", "--quiet", remote, &clone_dir.to_string_lossy()],
                None,
            )?;
        }
        let local = DiskTransport::open(&clone_dir)?;
        Ok(Self {
            remote: remote.to_string(),
            local,
            clone_dir,
        })
    }

    /// The local working clone, exposed for a closure walk that reads objects
    /// through the underlying store.
    #[must_use]
    pub const fn local(&self) -> &DiskTransport {
        &self.local
    }

    /// Commit every staged change in the working tree and push it to the remote.
    /// A no-op (nothing to commit) is success, so a publish that only re-hit
    /// existing objects still returns cleanly.
    ///
    /// # Errors
    /// [`TransportError::Remote`] if a git step fails.
    pub fn push(&self, message: &str) -> Result<(), TransportError> {
        let cwd = Some(self.clone_dir.as_path());
        git(&["add", "-A"], cwd)?;
        // `git commit` exits non-zero when there is nothing to commit; treat that
        // one case as success rather than an error.
        let committed = git(&["commit", "-m", message], cwd);
        if let Err(TransportError::Remote(msg)) = &committed {
            if !msg.contains("nothing to commit") {
                committed?;
            }
        }
        // Push HEAD explicitly so the first push to a fresh remote creates the
        // branch without needing an upstream to be configured first.
        git(&["push", "--quiet", "origin", "HEAD"], cwd)?;
        Ok(())
    }

    /// The remote URL this transport was opened against.
    #[must_use]
    pub fn remote(&self) -> &str {
        &self.remote
    }
}

impl Transport for GitTransport {
    fn has(&self, hash: &str) -> bool {
        self.local.has(hash)
    }

    fn fetch(&self, hash: &str) -> Result<Vec<u8>, TransportError> {
        self.local.fetch(hash)
    }

    fn publish(&self, hash: &str, bytes: &[u8]) -> Result<Written, TransportError> {
        self.local.publish(hash, bytes)
    }

    fn fetch_index(&self, name: &str) -> Result<Vec<IndexRow>, TransportError> {
        self.local.fetch_index(name)
    }

    fn index_artifact(&self) -> Result<Option<SignedArtifact>, TransportError> {
        self.local.index_artifact()
    }

    fn publish_index(&self, artifact: &SignedArtifact) -> Result<(), TransportError> {
        self.local.publish_index(artifact)
    }
}

// Run `git` with `args` in `cwd`, capturing output. A non-zero exit is a
// `Remote` error carrying stderr so a caller sees git's own diagnostic.
fn git(args: &[&str], cwd: Option<&Path>) -> Result<String, TransportError> {
    let mut cmd = Command::new("git");
    cmd.args(args);
    if let Some(dir) = cwd {
        cmd.current_dir(dir);
    }
    let out = cmd
        .output()
        .map_err(|e| TransportError::Remote(format!("could not run git: {e}")))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(TransportError::Remote(
            String::from_utf8_lossy(&out.stderr).trim().to_string(),
        ))
    }
}

/// What one [`push_closure`] moved, enough to assert the stdlib baseline never
/// travels and a warm remote transfers nothing.
#[derive(Debug, Default, Clone)]
pub struct PushStats {
    /// The hashes actually transferred to the destination, in sorted order.
    pub transferred: Vec<String>,
    /// Objects pruned because they are reachable from the shared stdlib root.
    pub skipped_baseline: usize,
    /// Objects the destination already held (warm-cache hits).
    pub skipped_present: usize,
}

/// Replicate the Merkle closure of `roots` from `src` to `dst`, skipping the
/// shared standard-library baseline and anything the destination already holds.
///
/// The closure is walked purely over the objects in `src`: each `def` frame
/// carries its own external dependency hashes, so the graph is recovered from the
/// bytes without a side table. Nothing reachable from `baseline` is walked or
/// transferred, which is the reference-or-inline dedup made concrete: the stdlib
/// is the zero-cost baseline both peers assume.
///
/// # Errors
/// A missing root object, a decode failure, or a backing IO/verify error.
pub fn push_closure<T: Transport + ?Sized>(
    src: &Store,
    dst: &T,
    roots: &[String],
    baseline: &BTreeSet<String>,
) -> Result<PushStats, TransportError> {
    let mut stats = PushStats::default();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut work: Vec<String> = roots.to_vec();
    let mut to_send: BTreeSet<String> = BTreeSet::new();

    while let Some(hash) = work.pop() {
        if !seen.insert(hash.clone()) {
            continue;
        }
        // Prune at the shared baseline: a stdlib member and everything beneath it
        // is assumed present on the peer, so it is never fetched from `src` (which
        // need not even hold it) nor sent.
        if baseline.contains(&hash) {
            stats.skipped_baseline += 1;
            continue;
        }
        let bytes = src
            .get(&hash)
            .map_err(|_| TransportError::Missing(hash.clone()))?;
        let decoded = decode_def(&bytes)?;
        for dep in decoded.dep_hashes {
            work.push(dep);
        }
        to_send.insert(hash);
    }

    for hash in to_send {
        if dst.has(&hash) {
            stats.skipped_present += 1;
            continue;
        }
        let bytes = src
            .get(&hash)
            .map_err(|_| TransportError::Missing(hash.clone()))?;
        dst.publish(&hash, &bytes)?;
        stats.transferred.push(hash);
    }
    stats.transferred.sort();
    Ok(stats)
}

/// Re-verify the Merkle closure of `roots` against `src`.
///
/// Every object reachable from a root must be present and reconstruct to the hash
/// it is filed under. Pruned at the shared stdlib `baseline`, which is assumed
/// present and trusted.
///
/// Returns the number of objects verified. This is the integrity half of
/// `prism audit`: a hash check over the whole closure, independent of any
/// signature.
///
/// # Errors
/// [`TransportError::Missing`] for an absent object, or a decode/hash-mismatch
/// error for a corrupt one.
pub fn verify_closure(
    src: &Store,
    roots: &[String],
    baseline: &BTreeSet<String>,
) -> Result<usize, TransportError> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut work: Vec<String> = roots.to_vec();
    let mut verified = 0usize;
    while let Some(hash) = work.pop() {
        if !seen.insert(hash.clone()) {
            continue;
        }
        if baseline.contains(&hash) {
            continue;
        }
        if !src.has(&hash) {
            return Err(TransportError::Missing(hash));
        }
        let bytes = src.get(&hash)?;
        verify(&hash, &bytes)?;
        verified += 1;
        for dep in decode_def(&bytes)?.dep_hashes {
            work.push(dep);
        }
    }
    Ok(verified)
}

/// Re-verify every object the store holds outside the shared stdlib baseline.
///
/// A published namespace root is a Merkle fold over its members, not itself a
/// stored object, so integrity is checked over the objects the store actually
/// committed: the name index's non-baseline hashes are the roots, and the whole
/// closure beneath them is re-hashed. Returns the number of objects verified.
///
/// # Errors
/// A missing or corrupt object, or a filesystem error reading the name index.
pub fn verify_all(src: &Store, baseline: &BTreeSet<String>) -> Result<usize, TransportError> {
    let roots: Vec<String> = src
        .names()?
        .into_values()
        .filter(|h| !baseline.contains(h))
        .collect();
    verify_closure(src, &roots, baseline)
}
