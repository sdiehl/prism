//! The on-disk two-layer content-addressed store.
//!
//! An **anonymous layer** (`objects/`) holds one immutable, append-only blob per
//! content hash: writing a hash that already exists verifies byte-identity
//! rather than overwriting, and a mismatch is corruption, never a silent
//! replace. A **metadata layer** (`meta/`) holds the mutable, human-facing facts
//! keyed by the same hash (name, type, and reserved slots for docs and source
//! positions); a rename or a doc edit touches only this layer and never the
//! anonymous object the hash commits to. Beside them, two flat, versioned index
//! files support reverse queries: `index/names` (name to hash) and `index/deps`
//! (hash to its direct dependents), plus a `canonical` index binding each
//! `(class, type-head)` to its canonical instance hash and a `verified/`
//! directory recording which checks a hash has already passed.
//!
//! Everything is a cache. The store is derived from the source, never
//! load-bearing for correctness: deleting it forces recomputation, nothing more.
//!
//! Durability and concurrency rest on two disciplines. Every write goes to a
//! uniquely named temp file in the destination directory and is renamed into
//! place, which is atomic on POSIX, so a concurrent reader sees either the old
//! complete file or the new one, never a torn write, and a process killed
//! mid-write leaves only a `.tmp.*` file that no reader ever opens (readers only
//! ever open the exact hash path). Index writers, which read-modify-write a
//! whole file, additionally take an advisory `index/lock` so a concurrent update
//! is not lost; the lock is best-effort (a stale lock from a killed writer is
//! stolen after a bounded wait) because index files are cache state and a lost
//! binding is recovered on the next commit.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::core::{scc_groups, Core, CoreFn, DepGraph, Hashes, HASH_SCHEME};
use crate::store::codec;
use crate::sym::Sym;

mod certs;
mod index;
mod meta;
mod objects;
mod verified;

pub use index::CanonicalKey;
pub use meta::DefMeta;
pub use verified::VerifiedRecord;

// The store's own on-disk layout version, independent of the hash scheme. A bump
// means the directory shape or an index file format changed; an old store is
// refused rather than misread. The hash scheme tag lives in the hash module and
// is never re-typed here.
const STORE_FORMAT: &str = "prism-store-v1";

const VERSION_FILE: &str = "VERSION";
const OBJECTS_DIR: &str = "objects";
const META_DIR: &str = "meta";
const INDEX_DIR: &str = "index";
const VERIFIED_DIR: &str = "verified";
const CERTS_DIR: &str = "certs";
const LOCK_FILE: &str = "lock";

// Objects and metadata blobs are sharded git-style by the first byte of the hex
// hash (two hex characters) so no single directory holds the whole store.
const SHARD_HEX: usize = 2;

// Line-oriented flat-file conventions shared by every index. A record is one
// line; fields within a record are tab-separated; a list within a field is
// space-separated. Canonical symbols and hex hashes contain neither, so the
// separators are unambiguous.
const FIELD_SEP: char = '\t';
const LIST_SEP: char = ' ';

/// A content hash rendered as lowercase hex, the identity every layer is keyed
/// by. Borrowed here to avoid churn; the store never owns hashes.
type HashHex = str;

/// Whether a `put` created a new object or matched an existing one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Written {
    /// The hash was absent; the object was written.
    New,
    /// The hash was present and the bytes matched; nothing was written.
    Hit,
}

/// What one [`commit_program`] did, enough for a caller to assert warm-cache
/// behavior (a second commit of an unchanged program writes zero objects).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CommitStats {
    /// Anonymous objects newly written this commit.
    pub objects_written: usize,
    /// Anonymous objects already present with identical bytes (cache hits).
    pub objects_hit: usize,
    /// Metadata blobs written (the mutable layer is always rewritten).
    pub meta_written: usize,
    /// Name bindings recorded.
    pub names_bound: usize,
}

/// An open handle to a store rooted at a directory. Cheap to hold; all state is
/// on disk, so a handle is just the validated root path.
#[derive(Debug, Clone)]
pub struct Store {
    root: PathBuf,
}

impl Store {
    /// Open the store at `root`, creating and stamping it if absent.
    ///
    /// A fresh directory is stamped with the hash scheme and store format. An
    /// existing directory is opened only if both stamps match; a foreign or
    /// future stamp is a hard error rather than a misread.
    ///
    /// # Errors
    /// Fails on any filesystem error, or if an existing store carries a scheme
    /// or format tag this build does not speak.
    pub fn open_or_create(root: impl AsRef<Path>) -> io::Result<Self> {
        let root = root.as_ref().to_path_buf();
        let version = root.join(VERSION_FILE);
        if version.exists() {
            check_stamp(&version)?;
        } else {
            fs::create_dir_all(&root)?;
            atomic_write(&version, stamp().as_bytes())?;
        }
        Ok(Self { root })
    }

    /// Put an anonymous object. If the hash is present its bytes must match
    /// (immutability); a mismatch is corruption. See [`Written`].
    ///
    /// # Errors
    /// Fails on a filesystem error, an ill-formed hash, or a byte mismatch
    /// against an existing object.
    pub fn put(&self, hash: &HashHex, bytes: &[u8]) -> io::Result<Written> {
        objects::put(&self.root, hash, bytes)
    }

    /// Read an anonymous object.
    ///
    /// # Errors
    /// Fails if the hash is absent or on a filesystem error.
    pub fn get(&self, hash: &HashHex) -> io::Result<Vec<u8>> {
        objects::get(&self.root, hash)
    }

    /// Whether an anonymous object exists for `hash`.
    #[must_use]
    pub fn has(&self, hash: &HashHex) -> bool {
        objects::has(&self.root, hash)
    }

    /// Write (or overwrite, since the layer is mutable) a definition's metadata.
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn put_meta(&self, hash: &HashHex, m: &DefMeta) -> io::Result<()> {
        meta::put(&self.root, hash, m)
    }

    /// Read a definition's metadata, if any.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed metadata blob.
    pub fn get_meta(&self, hash: &HashHex) -> io::Result<Option<DefMeta>> {
        meta::get(&self.root, hash)
    }

    /// Bind names to hashes in the mutable name index (read-modify-write under
    /// the advisory lock). An existing name is repointed.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn bind_names(&self, bindings: &BTreeMap<String, String>) -> io::Result<()> {
        index::bind_names(&self.root, bindings)
    }

    /// Resolve a name to its bound hash, if any.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn lookup_name(&self, name: &str) -> io::Result<Option<String>> {
        Ok(index::load_names(&self.root)?.remove(name))
    }

    /// The whole name index.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn names(&self) -> io::Result<BTreeMap<String, String>> {
        index::load_names(&self.root)
    }

    /// Record reverse-dependency edges (each entry `hash -> hashes that directly
    /// depend on it`), merged into the existing `deps` index under the lock.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn add_dependents(&self, edges: &BTreeMap<String, BTreeSet<String>>) -> io::Result<()> {
        index::add_dependents(&self.root, edges)
    }

    /// The hashes that directly depend on `hash`.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn dependents(&self, hash: &HashHex) -> io::Result<BTreeSet<String>> {
        Ok(index::load_deps(&self.root)?
            .remove(hash)
            .unwrap_or_default())
    }

    /// Bind the canonical instance for a `(class, type-head)` (the on-disk key
    /// shape is fixed, see [`index`]; coherence enforcement owns the semantics).
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn set_canonical(&self, key: &CanonicalKey, instance_hash: &str) -> io::Result<()> {
        index::set_canonical(&self.root, key, instance_hash)
    }

    /// The canonical instance hash for a `(class, type-head)`, if bound.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn canonical(&self, key: &CanonicalKey) -> io::Result<Option<String>> {
        index::canonical(&self.root, key)
    }

    /// Append a verification record for `hash` (the format is fixed, see
    /// [`verified`]).
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn put_verified(&self, hash: &HashHex, record: &VerifiedRecord) -> io::Result<()> {
        verified::put(&self.root, hash, record)
    }

    /// The verification records recorded for `hash`.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed record.
    pub fn verified(&self, hash: &HashHex) -> io::Result<Vec<VerifiedRecord>> {
        verified::get(&self.root, hash)
    }

    /// Write the certificate envelope attesting a property of `subject`. Immutable
    /// like an anonymous object: an identical cert is a [`Written::Hit`], different
    /// bytes for an existing subject are a corruption error.
    ///
    /// # Errors
    /// Fails on a filesystem error, an ill-formed hash, or a byte mismatch against
    /// an existing certificate.
    pub fn put_cert(&self, subject: &HashHex, bytes: &[u8]) -> io::Result<Written> {
        certs::put(&self.root, subject, bytes)
    }

    /// The certificate envelope attesting `subject`, or `None` when none exists.
    /// An absent certificate is never an error: not every hash carries one.
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn get_cert(&self, subject: &HashHex) -> io::Result<Option<Vec<u8>>> {
        certs::get(&self.root, subject)
    }

    /// Whether a certificate envelope exists for `subject`.
    #[must_use]
    pub fn has_cert(&self, subject: &HashHex) -> bool {
        certs::has(&self.root, subject)
    }
}

/// Commit a whole elaborated program into the store.
///
/// Writes one anonymous object per definition (via the [`codec`] seam), its
/// metadata, the name bindings, and the reverse-dependency edges. Idempotent:
/// committing an unchanged program a second time writes zero objects (every hash
/// is a hit).
///
/// `hashes` maps each definition's canonical symbol to its content hash;
/// `hash_meta` supplies each definition's rendered out-of-Core elaboration
/// inputs (type, principal row, borrow mask), the same string the content hash
/// commits to, which the codec round-trips verbatim; `graph` supplies direct
/// dependencies; `metas` supplies the human metadata-layer facts. A definition
/// without a hash (there should be none) is skipped.
///
/// # Errors
/// Fails on any filesystem error or a byte mismatch against an existing object
/// (which would mean two different definitions collided on one hash).
pub fn commit_program(
    store: &Store,
    core: &Core,
    hashes: &Hashes,
    hash_meta: &BTreeMap<Sym, String>,
    graph: &DepGraph,
    metas: &BTreeMap<Sym, DefMeta>,
) -> io::Result<CommitStats> {
    let mut stats = CommitStats::default();
    let mut names: BTreeMap<String, String> = BTreeMap::new();
    let mut dependents: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    let fnmap: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();

    // A definition's content hash folds in its whole recursive group (a cycle's
    // members hash in each other), so each member's object serializes the group
    // and names which member it is keyed by. A singleton group is the common case.
    for group_syms in scc_groups(core) {
        let members: Vec<&CoreFn> = group_syms
            .iter()
            .filter_map(|s| fnmap.get(s).copied())
            .collect();
        if members.len() != group_syms.len() {
            continue;
        }

        for (target, func) in members.iter().enumerate() {
            let Some(hash) = hashes.get(&func.name) else {
                continue;
            };
            let payload = codec::encode_def(&codec::AnonEntry {
                group: &members,
                target,
                hash,
                deps: hashes,
                meta: hash_meta,
            });
            match store.put(hash, &payload)? {
                Written::New => stats.objects_written += 1,
                Written::Hit => stats.objects_hit += 1,
            }

            if let Some(m) = metas.get(&func.name) {
                store.put_meta(hash, m)?;
                stats.meta_written += 1;
                names.insert(m.name.clone(), hash.clone());
                stats.names_bound += 1;
            }

            // Reverse-dependency edges: each direct dependency hash gains this
            // definition as a dependent. Builtins carry no top-level hash and drop
            // out, exactly as the namespace export does.
            for dep in graph.direct_deps(func.name) {
                if let Some(dep_hash) = hashes.get(&dep) {
                    dependents
                        .entry(dep_hash.clone())
                        .or_default()
                        .insert(hash.clone());
                }
            }
        }
    }

    if !names.is_empty() {
        store.bind_names(&names)?;
    }
    if !dependents.is_empty() {
        store.add_dependents(&dependents)?;
    }
    Ok(stats)
}

/// Resolve the store root: the explicit `override_` (the `PRISM_STORE_PATH`
/// knob) if given, else a user-wide cache directory, else `target/prism-store`
/// under the current directory.
///
/// The store is content-addressed, so a hash built once is reusable across every
/// project on the machine; a user-wide cache directory is therefore the natural
/// home and lets unrelated builds share entries. When no cache or home directory
/// is discoverable (sandboxes, CI), it falls back to `target/prism-store`,
/// mirroring the project's existing habit of putting derived artifacts under
/// `target/` and keeping the store always writable. Because the store is only a
/// cache, the fallback is never a correctness concern.
#[must_use]
pub fn resolve_store_path(override_: Option<&Path>) -> PathBuf {
    if let Some(p) = override_ {
        return p.to_path_buf();
    }
    if let Some(dir) = user_cache_dir() {
        return dir.join("prism").join("store");
    }
    PathBuf::from("target").join("prism-store")
}

// The platform user-cache directory, discovered from ambient location env vars
// (not compiler behavior knobs, so not part of DynFlags). None when nothing is
// discoverable, which drops the caller to the target/ fallback.
fn user_cache_dir() -> Option<PathBuf> {
    #[cfg(windows)]
    {
        std::env::var_os("LOCALAPPDATA").map(PathBuf::from)
    }
    #[cfg(not(windows))]
    {
        if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME") {
            return Some(PathBuf::from(xdg));
        }
        std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache"))
    }
}

// The VERSION stamp: hash scheme (from the hash module, never re-typed) then the
// store format, one per line.
fn stamp() -> String {
    format!("{HASH_SCHEME}\n{STORE_FORMAT}\n")
}

// Refuse a store whose stamp this build does not speak.
fn check_stamp(version: &Path) -> io::Result<()> {
    let text = fs::read_to_string(version)?;
    let mut lines = text.lines();
    let scheme = lines.next().unwrap_or_default();
    let format = lines.next().unwrap_or_default();
    if scheme != HASH_SCHEME || format != STORE_FORMAT {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "store at {} has foreign stamp (scheme {scheme:?}, format {format:?}); \
                 this build speaks scheme {HASH_SCHEME:?}, format {STORE_FORMAT:?}",
                version.display()
            ),
        ));
    }
    Ok(())
}

// The sharded path for a hash under `layer`: `<layer>/<first 2 hex>/<rest>`.
fn shard_path(layer: &Path, hash: &HashHex) -> PathBuf {
    let (shard, rest) = hash.split_at(SHARD_HEX);
    layer.join(shard).join(rest)
}

// A hash usable as a filesystem key: nonempty hex, long enough to shard. This
// guards the path construction, not the hash's cryptographic strength.
fn validate_hash(hash: &HashHex) -> io::Result<()> {
    if hash.len() > SHARD_HEX && hash.bytes().all(|b| b.is_ascii_hexdigit()) {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("ill-formed content hash {hash:?}"),
        ))
    }
}

// Unique temp path in `dir`. The `.tmp.` prefix marks it as never an object or
// index file, so a reader (which only opens exact known paths) ignores a temp
// left by a killed writer.
fn unique_temp(dir: &Path) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    dir.join(format!(".tmp.{pid}.{nanos}.{n}"))
}

// Write `bytes` to `path` atomically: full write plus fsync to a unique temp in
// the same directory, then rename over the destination. The rename is the commit
// point; a crash before it leaves only the temp.
fn atomic_write(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let dir = path
        .parent()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "store path has no parent"))?;
    fs::create_dir_all(dir)?;
    let tmp = unique_temp(dir);
    {
        let mut f = fs::File::create(&tmp)?;
        f.write_all(bytes)?;
        f.sync_all()?;
    }
    fs::rename(&tmp, path)
}
