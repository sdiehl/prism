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
//! required for correctness: deleting it forces recomputation, nothing more.
//! That contract lets the high-churn layers bound themselves: a publish that
//! lands in a full shard retires that shard's oldest entries (see
//! `evict_shard_overflow`), so no layer grows without limit between explicit
//! `gc` runs and the sweep is a deep clean, never the only line of defense.
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
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism_common::digest::SCHEME as HASH_SCHEME;

mod census;
mod certs;
mod decisions;
#[cfg(test)]
mod faults;
mod gc;
mod index;
mod meta;
mod objects;
mod queries;
#[cfg(test)]
mod testutil;
mod verified;

pub use census::{LayerCensus, StoreCensus};
#[cfg(test)]
use faults::FaultPoint;
pub use gc::{GcProgress, GcProgressFn, GcStats};
pub use index::{CanonicalConflict, CanonicalKey};
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
const QUERIES_DIR: &str = "queries";
const DECISIONS_DIR: &str = "decisions";
const LOCK_FILE: &str = "lock";

// Objects and metadata blobs are sharded git-style by the first byte of the hex
// hash (two hex characters) so no single directory holds the whole store.
const SHARD_HEX: usize = 2;
// How many shard directories one sharded layer fans out to.
const SHARD_COUNT: u64 = 1 << (4 * SHARD_HEX);

// Publish-time bounds for the high-churn sharded layers. Keys are hashes, so
// shards fill uniformly and bounding every shard bounds the layer: a publish
// landing in a shard past its budget retires that one directory's oldest
// entries, paying retirement continuously and locally instead of deferring it
// to a full-store crawl that grows more expensive the longer it is postponed.
// Budgets are per shard; a layer's ceiling is the budget times the shard
// count. Eviction never consults liveness: bindings and objects are cache
// entries whose loss is a correct future miss (see the query and object read
// paths), so age is the only signal needed.

/// A sharded layer's per-shard retention budget: watermark pairs on both the
/// entry count and the byte total.
///
/// A publish that leaves its shard over either cap retires oldest entries
/// until the overflowing dimension sits at its low mark, so a layer of tiny
/// entries is bounded by count and a layer of large blobs by bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardBudget {
    /// Most entries one shard retains before a publish trims it.
    pub cap: usize,
    /// The entry count an overfull shard is trimmed back to.
    pub low: usize,
    /// Most bytes one shard retains before a publish trims it.
    pub byte_cap: u64,
    /// The byte total an oversized shard is trimmed back to.
    pub byte_low: u64,
}

const KIB: u64 = 1 << 10;
const MIB: u64 = 1 << 20;

/// Query bindings are small fixed-size pointers, so the entry cap is the
/// binding bound: one kind holds at most about 64K bindings.
pub const QUERY_SHARD_BUDGET: ShardBudget = ShardBudget {
    cap: 256,
    low: 192,
    byte_cap: MIB,
    byte_low: 768 * KIB,
};

/// Objects (and the metadata blobs keyed beside them) vary from bytes to
/// megabytes, so both dimensions bind: at most about 256K entries and 4 GiB
/// per layer.
pub const OBJECT_SHARD_BUDGET: ShardBudget = ShardBudget {
    cap: 1024,
    low: 768,
    byte_cap: 16 * MIB,
    byte_low: 12 * MIB,
};

// One publish never retires more than this many files: a shard inherited far
// above its budget is ground down across many publishes instead of stalling
// one.
const EVICT_BATCH: usize = 512;

// Every in-flight write carries this prefix. Readers only ever open exact
// object/index paths, so a file with this prefix is never content: a temp left
// by a killed writer is inert until some later write in the same directory.
pub const TEMP_PREFIX: &str = ".tmp.";

// A layer or query kind so far past its budget that an in-place sweep would
// grind for hours is retired wholesale: renamed to a dot-prefixed sibling at
// the store root, drained offline, then deleted. Readers only ever open exact
// live paths, so a retired tree is invisible the moment the rename lands, and
// a crash mid-drain leaves a tree the next sweep finds by prefix and resumes.
// The manifest written inside the tree names its origin layer as data, so
// resumption never parses facts back out of a directory name.
const RETIRED_PREFIX: &str = ".retired.";
const RETIRED_MANIFEST: &str = ".retired-manifest";
const RETIRED_FORMAT: &str = "prism-store-retired-v1";

// Line-oriented flat-file conventions shared by every index. A record is one
// line. Fields within a record are tab-separated. A list within a field is
// space-separated. Canonical symbols and hex hashes contain neither, so the
// separators are unambiguous.
const FIELD_SEP: char = '\t';
const LIST_SEP: char = ' ';

/// Validated lowercase hexadecimal identity accepted by store internals.
///
/// Construction is the only validation boundary; paths and indexes cannot be
/// addressed with an unchecked string after this point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StoreHash<'a>(&'a str);

impl<'a> StoreHash<'a> {
    /// Validate a hexadecimal store identity.
    ///
    /// # Errors
    /// Returns `InvalidInput` when `hash` is too short for sharding or contains
    /// anything other than lowercase hexadecimal digits.
    pub fn new(hash: &'a str) -> io::Result<Self> {
        if hash.len() < SHARD_HEX
            || !hash
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "hash must be lowercase hex and at least two characters",
            ));
        }
        Ok(Self(hash))
    }

    #[must_use]
    pub const fn as_str(self) -> &'a str {
        self.0
    }
}

impl fmt::Display for StoreHash<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl Deref for StoreHash<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

type HashHex<'a> = StoreHash<'a>;

/// Whether a `put` created a new object or matched an existing one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Written {
    /// The hash was absent; the object was written.
    New,
    /// The hash was present and the bytes matched; nothing was written.
    Hit,
}

/// What one `commit_program` did, enough for a caller to assert warm-cache
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
    pub fn put(&self, hash: &str, bytes: &[u8]) -> io::Result<Written> {
        let hash = StoreHash::new(hash)?;
        objects::put(&self.root, &hash, bytes)
    }

    /// Read an anonymous object.
    ///
    /// # Errors
    /// Fails if the hash is absent or on a filesystem error.
    pub fn get(&self, hash: &str) -> io::Result<Vec<u8>> {
        let hash = StoreHash::new(hash)?;
        objects::get(&self.root, &hash)
    }

    /// Whether an anonymous object exists for `hash`.
    #[must_use]
    pub fn has(&self, hash: &str) -> bool {
        StoreHash::new(hash).is_ok_and(|hash| objects::has(&self.root, &hash))
    }

    /// Resolve a typed compiler query key to its immutable output object hash.
    ///
    /// Query entries are cache indexes, never semantic authority. A missing entry
    /// is a normal miss; a malformed entry is rejected rather than treated as a
    /// hit.
    ///
    /// # Errors
    /// Fails on malformed keys/entries or a filesystem error.
    pub fn get_query(&self, kind: &str, key: &str) -> io::Result<Option<String>> {
        let key = StoreHash::new(key)?;
        queries::get(&self.root, kind, &key)
    }

    /// Bind a typed compiler query key to an immutable output object.
    ///
    /// Rebinding the same key to different output bytes is corruption: identical
    /// query inputs must have one byte-identical result.
    ///
    /// # Errors
    /// Fails on malformed hashes, a conflicting existing binding, or a filesystem
    /// error.
    pub fn put_query(&self, kind: &str, key: &str, output: &str) -> io::Result<()> {
        let key = StoreHash::new(key)?;
        let output = StoreHash::new(output)?;
        if !objects::has(&self.root, &output) {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("query output object {output} is absent"),
            ));
        }
        #[cfg(test)]
        faults::hit(FaultPoint::AfterObjectBeforeQuery)?;
        queries::put(&self.root, kind, &key, &output)
    }

    /// Read the latest successful explanatory record for a query locator.
    ///
    /// Decision records are mutable metadata and never authorize cache reuse.
    /// Missing records are normal for a first build.
    ///
    /// # Errors
    /// Fails on malformed locators, malformed records, or filesystem errors.
    pub fn get_decision(&self, kind: &str, locator: &str) -> io::Result<Option<Vec<u8>>> {
        decisions::get(&self.root, kind, locator)
    }

    /// Atomically replace the explanatory record for a successful query.
    ///
    /// # Errors
    /// Fails on malformed locators or filesystem errors.
    pub fn put_decision(&self, kind: &str, locator: &str, bytes: &[u8]) -> io::Result<()> {
        decisions::put(&self.root, kind, locator, bytes)
    }

    /// Write (or overwrite, since the layer is mutable) a definition's metadata.
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn put_meta(&self, hash: &str, m: &DefMeta) -> io::Result<()> {
        let hash = StoreHash::new(hash)?;
        meta::put(&self.root, &hash, m)
    }

    /// Read a definition's metadata, if any.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed metadata blob.
    pub fn get_meta(&self, hash: &str) -> io::Result<Option<DefMeta>> {
        let hash = StoreHash::new(hash)?;
        meta::get(&self.root, &hash)
    }

    /// Bind names to hashes in the mutable name index (read-modify-write under
    /// the advisory lock). An existing name is repointed.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn bind_names(&self, bindings: &BTreeMap<String, String>) -> io::Result<()> {
        for hash in bindings.values() {
            StoreHash::new(hash)?;
        }
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

    /// Point the mutable ref `name` at `hash` in the `refs` index (a git-style
    /// ref into the immutable object layer). Repointing leaves the old object in
    /// place. Kept separate from the definition name index.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn set_ref(&self, name: &str, hash: &str) -> io::Result<()> {
        StoreHash::new(hash)?;
        index::set_ref(&self.root, name, hash)
    }

    /// Resolve a ref `name` to the hash it points at, if bound.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn get_ref(&self, name: &str) -> io::Result<Option<String>> {
        index::get_ref(&self.root, name)
    }

    /// Remove a mutable ref, leaving its immutable target object in place.
    /// Missing refs are a successful no-op.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn remove_ref(&self, name: &str) -> io::Result<()> {
        index::remove_ref(&self.root, name)
    }

    /// Record reverse-dependency edges (each entry `hash -> hashes that directly
    /// depend on it`), merged into the existing `deps` index under the lock.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn add_dependents(&self, edges: &BTreeMap<String, BTreeSet<String>>) -> io::Result<()> {
        for (hash, dependents) in edges {
            StoreHash::new(hash)?;
            for dependent in dependents {
                StoreHash::new(dependent)?;
            }
        }
        index::add_dependents(&self.root, edges)
    }

    /// The hashes that directly depend on `hash`.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn dependents(&self, hash: &str) -> io::Result<BTreeSet<String>> {
        let hash = StoreHash::new(hash)?;
        Ok(index::load_deps(&self.root)?
            .remove(hash.as_str())
            .unwrap_or_default())
    }

    /// Bind the canonical instance for a `(class, type-head)` (the on-disk key
    /// shape is fixed, see the `index` submodule; coherence enforcement owns the semantics).
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn set_canonical(&self, key: &CanonicalKey, instance_hash: &str) -> io::Result<()> {
        StoreHash::new(instance_hash)?;
        index::set_canonical(&self.root, key, instance_hash)
    }

    /// Atomically merge canonical instance bindings, rejecting any divergent
    /// existing binding under the same index lock that protects the write.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn merge_canonicals(
        &self,
        bindings: &[(CanonicalKey, String)],
    ) -> io::Result<Result<(), CanonicalConflict>> {
        for (_, hash) in bindings {
            StoreHash::new(hash)?;
        }
        index::merge_canonicals(&self.root, bindings)
    }

    /// The canonical instance hash for a `(class, type-head)`, if bound.
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn canonical(&self, key: &CanonicalKey) -> io::Result<Option<String>> {
        index::canonical(&self.root, key)
    }

    /// Append a verification record for `hash` (the format is fixed, see
    /// the `verified` submodule).
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn put_verified(&self, hash: &str, record: &VerifiedRecord) -> io::Result<()> {
        let hash = StoreHash::new(hash)?;
        verified::put(&self.root, &hash, record)
    }

    /// The verification records recorded for `hash`.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed record.
    pub fn verified(&self, hash: &str) -> io::Result<Vec<VerifiedRecord>> {
        let hash = StoreHash::new(hash)?;
        verified::get(&self.root, &hash)
    }

    /// Write the certificate envelope attesting a property of `subject`. Immutable
    /// like an anonymous object: an identical cert is a [`Written::Hit`], different
    /// bytes for an existing subject are a corruption error.
    ///
    /// # Errors
    /// Fails on a filesystem error, an ill-formed hash, or a byte mismatch against
    /// an existing certificate.
    pub fn put_cert(&self, subject: &str, bytes: &[u8]) -> io::Result<Written> {
        let subject = StoreHash::new(subject)?;
        certs::put(&self.root, &subject, bytes)
    }

    /// The certificate envelope attesting `subject`, or `None` when none exists.
    /// An absent certificate is never an error: not every hash carries one.
    ///
    /// # Errors
    /// Fails on a filesystem error or an ill-formed hash.
    pub fn get_cert(&self, subject: &str) -> io::Result<Option<Vec<u8>>> {
        let subject = StoreHash::new(subject)?;
        certs::get(&self.root, &subject)
    }

    /// Whether a certificate envelope exists for `subject`.
    #[must_use]
    pub fn has_cert(&self, subject: &str) -> bool {
        StoreHash::new(subject).is_ok_and(|subject| certs::has(&self.root, &subject))
    }

    /// Garbage-collect entries older than `min_age`: prune stale query
    /// bindings, then remove any object or metadata blob that no surviving
    /// query output or index entry (`names`/`deps`/`canonical`/`refs`)
    /// references. `dry_run` reports what would be removed without touching
    /// the filesystem. See the `gc` submodule for the reachability rules and
    /// why the age cutoff exists.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed query/index entry.
    pub fn gc(&self, min_age: std::time::Duration, dry_run: bool) -> io::Result<GcStats> {
        self.gc_with_progress(min_age, dry_run, &|_| {})
    }

    /// As [`Store::gc`], reporting progress beats to `progress` as the sweep
    /// walks shard directories, so an interactive caller can render a live
    /// indicator. Beats arrive from the sweep's worker threads, hence the
    /// `Sync` bound on the callback.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed query/index entry.
    pub fn gc_with_progress(
        &self,
        min_age: std::time::Duration,
        dry_run: bool,
        progress: GcProgressFn<'_>,
    ) -> io::Result<GcStats> {
        let cutoff = SystemTime::now() - min_age;
        gc::sweep(&self.root, cutoff, dry_run, progress)
    }

    /// Count the files each store layer holds right now, without reading or
    /// stating any of them (see the `census` submodule for how the count stays
    /// cheap on stores holding millions of files).
    ///
    /// # Errors
    /// Fails on a filesystem error.
    pub fn census(&self) -> io::Result<StoreCensus> {
        census::take(&self.root)
    }
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
fn shard_path(layer: &Path, hash: &HashHex<'_>) -> PathBuf {
    let (shard, rest) = hash.split_at(SHARD_HEX);
    layer.join(shard).join(rest)
}

// Retire the oldest entries of a shard directory that has grown past its
// budget on either dimension, down toward the low watermarks, never touching
// `keep` (the entry just published), temp files, or subdirectories.
// Best-effort by contract: eviction is hygiene for a cache layer, so any
// error, including a race with a concurrent evictor or an external cleanup
// unlinking the same files, leaves the publish untouched.
fn evict_shard_overflow(shard_dir: &Path, keep: &Path, budget: ShardBudget) {
    let Ok(entries) = fs::read_dir(shard_dir) else {
        return;
    };
    let mut aged: Vec<(SystemTime, PathBuf, u64)> = Vec::new();
    let mut total_bytes = 0u64;
    for entry in entries.flatten() {
        let path = entry.path();
        if path == keep
            || entry.file_name().to_string_lossy().starts_with(TEMP_PREFIX)
            || !entry.file_type().is_ok_and(|t| t.is_file())
        {
            continue;
        }
        let Ok(meta) = entry.metadata() else {
            continue;
        };
        let Ok(modified) = meta.modified() else {
            continue;
        };
        total_bytes += meta.len();
        aged.push((modified, path, meta.len()));
    }
    // A dimension participates only if it was over its cap when the publish
    // landed; the other stops trimming the moment its own low mark holds.
    let over_entries = aged.len() > budget.cap;
    let over_bytes = total_bytes > budget.byte_cap;
    if !over_entries && !over_bytes {
        return;
    }
    aged.sort();
    let mut count = aged.len();
    let mut bytes = total_bytes;
    for (evicted, (_, path, len)) in aged.into_iter().enumerate() {
        let past_count = over_entries && count > budget.low;
        let past_bytes = over_bytes && bytes > budget.byte_low;
        if evicted >= EVICT_BATCH || (!past_count && !past_bytes) {
            break;
        }
        let _ = fs::remove_file(path);
        count -= 1;
        bytes = bytes.saturating_sub(len);
    }
}

// Refresh a published entry's age so shard eviction, which retires by mtime,
// sees a republished entry as live. Best-effort for the same reason eviction
// is: an entry whose refresh loses a race is merely evicted a little sooner.
fn refresh_entry_age(path: &Path) {
    let _ = fs::File::open(path).and_then(|f| f.set_modified(SystemTime::now()));
}

// Tripwire for a broken retirement path, shared by the sharded layers. Every
// publish bounds its own shard, so a shard can only reach a count far past its
// budget if eviction has stopped firing or the tree predates bounding. A
// publish landing in the sample shard counts that one directory (keys are
// hashes, so one publish in 256 pays one small directory read) and, past the
// threshold, returns the layer-wide estimate to warn with, at most once per
// process per `warned` flag. Counting failures return nothing because a
// metric must never fail a publish that already succeeded.
const SAMPLE_SHARD: &str = "00";
fn runaway_estimate(shard_dir: &Path, shard_warn_entries: u64, warned: &AtomicBool) -> Option<u64> {
    let rd = fs::read_dir(shard_dir).ok()?;
    let count = rd.count() as u64;
    if count > shard_warn_entries && !warned.swap(true, Ordering::Relaxed) {
        return Some(count.saturating_mul(SHARD_COUNT));
    }
    None
}

// A hash usable as a filesystem key: nonempty hex, long enough to shard. This
// guards the path construction, not the hash's cryptographic strength.

// Unique dot-prefixed path in `dir`: the pid, a timestamp, and a process-wide
// counter make collisions impossible in practice across concurrent writers.
fn unique_name(dir: &Path, prefix: &str) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    dir.join(format!("{prefix}{pid}.{nanos}.{n}"))
}

// Unique temp path in `dir`. The temp prefix marks it as never an object or
// index file, so a reader (which only opens exact known paths) ignores a temp
// left by a killed writer.
fn unique_temp(dir: &Path) -> PathBuf {
    unique_name(dir, TEMP_PREFIX)
}

// The directory a store file publishes into; every store path has one.
fn parent_dir(path: &Path) -> io::Result<&Path> {
    path.parent()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "store path has no parent"))
}

// The pre-publication stage shared by both atomic writers: write `bytes` in
// full to a fresh unique temp in `dir` and flush it durable. The caller owns
// the commit (rename or link) and the temp's removal; an error here leaves the
// temp behind exactly as a killed writer would, which is safe because readers
// never open temp paths.
fn write_temp(dir: &Path, bytes: &[u8]) -> io::Result<PathBuf> {
    fs::create_dir_all(dir)?;
    let tmp = unique_temp(dir);
    let mut f = fs::File::create(&tmp)?;
    #[cfg(test)]
    faults::partial_write(&mut f, bytes)?;
    f.write_all(bytes)?;
    #[cfg(test)]
    faults::hit(FaultPoint::BeforeFlush)?;
    f.sync_all()?;
    #[cfg(test)]
    faults::hit(FaultPoint::AfterFlush)?;
    Ok(tmp)
}

/// Write `bytes` to `path` atomically, without ever replacing an existing file.
///
/// A full write plus fsync to a unique temp in the same directory, then a hard
/// link into place. The link is the commit point: it fails rather than replaces
/// when the destination exists, so a published object is never overwritten; a
/// crash before it leaves only the temp. The flag reports whether this call was
/// the one that published.
///
/// # Errors
/// Any filesystem failure while creating the temp directory entry, writing,
/// syncing, or linking. An existing destination is not an error.
pub fn atomic_write_if_absent(path: &Path, bytes: &[u8]) -> io::Result<bool> {
    let tmp = write_temp(parent_dir(path)?, bytes)?;
    #[cfg(test)]
    faults::hit(FaultPoint::BeforePublish)?;
    let linked = match fs::hard_link(&tmp, path) {
        Ok(()) => Ok(true),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => Ok(false),
        Err(e) => Err(e),
    };
    let _ = fs::remove_file(tmp);
    linked
}

/// Write `bytes` to `path` atomically, replacing any existing file.
///
/// As [`atomic_write_if_absent`], but the commit point is a rename over the
/// destination, for the mutable layers (metadata, indexes) where replacement is
/// the point.
///
/// # Errors
/// Any filesystem failure while writing, syncing, or renaming.
pub fn atomic_write(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let tmp = write_temp(parent_dir(path)?, bytes)?;
    #[cfg(test)]
    faults::hit(FaultPoint::BeforePublish)?;
    fs::rename(&tmp, path)
}
