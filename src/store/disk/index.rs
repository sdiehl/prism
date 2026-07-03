//! The flat index files and the advisory lock that serializes their writers.
//!
//! Three line-oriented, tab-separated, header-versioned files under `index/`,
//! each a whole-file read-modify-write rewritten atomically (temp plus rename):
//!
//! - `names` maps a canonical name to a content hash:
//!   ```text
//!   prism-store-names<TAB>v1
//!   <name><TAB><hash>
//!   ```
//! - `deps` maps a content hash to the hashes that directly depend on it (the
//!   reverse edges, for "who uses this" queries); the dependents are a
//!   space-separated list:
//!   ```text
//!   prism-store-deps<TAB>v1
//!   <hash><TAB><dependent-hash> <dependent-hash> ...
//!   ```
//! - `canonical` maps a `(class, type-head)` to the canonical instance hash
//!   (may be empty):
//!   ```text
//!   prism-store-canonical<TAB>v1
//!   <class><TAB><type-head><TAB><instance-hash>
//!   ```
//!
//! Every write takes the advisory `index/lock` first (see [`Lock`]). Readers do
//! not lock: an index write is atomic, so a reader sees one whole file or the
//! other, and the lock exists only to keep two concurrent writers from losing
//! each other's read-modify-write.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::sleep;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::{atomic_write, FIELD_SEP, INDEX_DIR, LIST_SEP, LOCK_FILE};

const NAMES_FILE: &str = "names";
const DEPS_FILE: &str = "deps";
const CANONICAL_FILE: &str = "canonical";

const NAMES_HEADER: &str = "prism-store-names\tv1";
const DEPS_HEADER: &str = "prism-store-deps\tv1";
const CANONICAL_HEADER: &str = "prism-store-canonical\tv1";

// Lock acquisition: how long to wait for a peer writer before presuming its lock
// is stale (left by a killed process) and stealing it. Generous relative to a
// read-modify-write of a flat file, so a live peer is never stolen from.
const LOCK_POLL: Duration = Duration::from_millis(5);
const LOCK_TRIES: u32 = 200;

// How many poll-then-steal rounds acquisition attempts before giving up. A held
// lock is released within one read-modify-write, so contention clears in well
// under a round; the extra rounds only guard against a pathological stall.
const STEAL_ROUNDS: u32 = 8;

// A per-process monotonic counter, so two threads in one process that contend
// for the lock still stamp distinct owner tokens.
static LOCK_NONCE: AtomicU64 = AtomicU64::new(0);

/// A `(class, type-head)` pair identifying a canonical instance binding. This is
/// the on-disk key shape; coherence enforcement owns the semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalKey {
    /// The class name (for example `Ord`).
    pub class: String,
    /// The type-head name (for example `Int`).
    pub head: String,
}

fn index_dir(root: &Path) -> PathBuf {
    root.join(INDEX_DIR)
}

// The advisory lock. `create_new` gives O_EXCL semantics; a peer's live lock
// blocks us until it releases, and a stale lock (writer killed mid-update) is
// stolen once the wait elapses so a crash can never deadlock the store. Each
// holder stamps the file with a unique owner token so a stealer and `Drop` only
// ever remove a lock they still own, never one a peer has since taken.
struct Lock {
    path: PathBuf,
    token: String,
}

// A unique owner stamp: this process's id, a nanosecond timestamp, and a
// per-process counter, distinct across every acquisition even within one process.
fn owner_token() -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let n = LOCK_NONCE.fetch_add(1, Ordering::Relaxed);
    format!("{}-{nanos}-{n}", process::id())
}

impl Lock {
    fn acquire(root: &Path) -> io::Result<Self> {
        let dir = index_dir(root);
        fs::create_dir_all(&dir)?;
        let path = dir.join(LOCK_FILE);
        let token = owner_token();
        for _ in 0..STEAL_ROUNDS {
            for _ in 0..LOCK_TRIES {
                match Self::create_stamped(&path, &token) {
                    Ok(()) => return Ok(Self { path, token }),
                    Err(e) if e.kind() == io::ErrorKind::AlreadyExists => sleep(LOCK_POLL),
                    Err(e) => return Err(e),
                }
            }
            // The holder never yielded across a full poll window, so presume it
            // died mid-update (a live writer releases within one read-modify-write)
            // and steal. Remove the lock only while it still carries the stamp we
            // timed out against, so a peer that already stole and now holds is not
            // wiped; then race to recreate under O_EXCL. Exactly one stealer's
            // `create_new` wins and holds -- a loser sees `AlreadyExists` and
            // rejoins the poll rather than proceeding as a second holder (the
            // lost update this closes). A sub-poll TOCTOU between the stamp check
            // and the remove stays possible, but the ownership-checked `Drop`
            // still prevents any cross-deletion, and the index is a rebuildable
            // cache.
            let stale = fs::read_to_string(&path).ok();
            if stale.is_some() && fs::read_to_string(&path).ok() == stale {
                let _ = fs::remove_file(&path);
            }
            match Self::create_stamped(&path, &token) {
                Ok(()) => return Ok(Self { path, token }),
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => sleep(LOCK_POLL),
                Err(e) => return Err(e),
            }
        }
        Err(io::Error::new(
            io::ErrorKind::WouldBlock,
            "index lock is contended",
        ))
    }

    // Create the lock file exclusively (O_EXCL) and stamp our owner token into it.
    fn create_stamped(path: &Path, token: &str) -> io::Result<()> {
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?
            .write_all(token.as_bytes())
    }

    // Whether the lock file still carries our stamp: true only while we hold it.
    fn owned(&self) -> bool {
        fs::read_to_string(&self.path).is_ok_and(|s| s == self.token)
    }
}

impl Drop for Lock {
    fn drop(&mut self) {
        // Release only a lock we still own. If a peer presumed us dead and stole
        // it, the file carries a different stamp and is left for its new holder.
        if self.owned() {
            let _ = fs::remove_file(&self.path);
        }
    }
}

// Read a line-oriented index file, skipping the header, returning the data
// lines. A missing file is an empty index.
fn read_lines(path: &Path, header: &str) -> io::Result<Vec<String>> {
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut lines = text.lines();
    if lines.next() != Some(header) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("malformed index header at {}", path.display()),
        ));
    }
    Ok(lines.map(str::to_string).collect())
}

pub(super) fn load_names(root: &Path) -> io::Result<BTreeMap<String, String>> {
    let mut map = BTreeMap::new();
    for line in read_lines(&index_dir(root).join(NAMES_FILE), NAMES_HEADER)? {
        if let Some((name, hash)) = line.split_once(FIELD_SEP) {
            map.insert(name.to_string(), hash.to_string());
        }
    }
    Ok(map)
}

fn write_names(root: &Path, map: &BTreeMap<String, String>) -> io::Result<()> {
    let mut body = String::from(NAMES_HEADER);
    body.push('\n');
    for (name, hash) in map {
        let _ = writeln!(body, "{name}{FIELD_SEP}{hash}");
    }
    atomic_write(&index_dir(root).join(NAMES_FILE), body.as_bytes())
}

pub(super) fn bind_names(root: &Path, bindings: &BTreeMap<String, String>) -> io::Result<()> {
    let _lock = Lock::acquire(root)?;
    let mut map = load_names(root)?;
    for (name, hash) in bindings {
        map.insert(name.clone(), hash.clone());
    }
    write_names(root, &map)
}

pub(super) fn load_deps(root: &Path) -> io::Result<BTreeMap<String, BTreeSet<String>>> {
    let mut map: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for line in read_lines(&index_dir(root).join(DEPS_FILE), DEPS_HEADER)? {
        if let Some((hash, deps)) = line.split_once(FIELD_SEP) {
            let set = map.entry(hash.to_string()).or_default();
            for d in deps.split(LIST_SEP).filter(|s| !s.is_empty()) {
                set.insert(d.to_string());
            }
        }
    }
    Ok(map)
}

fn write_deps(root: &Path, map: &BTreeMap<String, BTreeSet<String>>) -> io::Result<()> {
    let mut body = String::from(DEPS_HEADER);
    body.push('\n');
    for (hash, deps) in map {
        let list: Vec<&str> = deps.iter().map(String::as_str).collect();
        let _ = writeln!(
            body,
            "{hash}{FIELD_SEP}{}",
            list.join(&LIST_SEP.to_string())
        );
    }
    atomic_write(&index_dir(root).join(DEPS_FILE), body.as_bytes())
}

pub(super) fn add_dependents(
    root: &Path,
    edges: &BTreeMap<String, BTreeSet<String>>,
) -> io::Result<()> {
    let _lock = Lock::acquire(root)?;
    let mut map = load_deps(root)?;
    for (hash, deps) in edges {
        map.entry(hash.clone())
            .or_default()
            .extend(deps.iter().cloned());
    }
    write_deps(root, &map)
}

fn load_canonical(root: &Path) -> io::Result<BTreeMap<(String, String), String>> {
    let mut map = BTreeMap::new();
    for line in read_lines(&index_dir(root).join(CANONICAL_FILE), CANONICAL_HEADER)? {
        let mut fields = line.splitn(3, FIELD_SEP);
        if let (Some(class), Some(head), Some(hash)) = (fields.next(), fields.next(), fields.next())
        {
            map.insert((class.to_string(), head.to_string()), hash.to_string());
        }
    }
    Ok(map)
}

fn write_canonical(root: &Path, map: &BTreeMap<(String, String), String>) -> io::Result<()> {
    let mut body = String::from(CANONICAL_HEADER);
    body.push('\n');
    for ((class, head), hash) in map {
        let _ = writeln!(body, "{class}{FIELD_SEP}{head}{FIELD_SEP}{hash}");
    }
    atomic_write(&index_dir(root).join(CANONICAL_FILE), body.as_bytes())
}

pub(super) fn set_canonical(
    root: &Path,
    key: &CanonicalKey,
    instance_hash: &str,
) -> io::Result<()> {
    let _lock = Lock::acquire(root)?;
    let mut map = load_canonical(root)?;
    map.insert(
        (key.class.clone(), key.head.clone()),
        instance_hash.to_string(),
    );
    write_canonical(root, &map)
}

pub(super) fn canonical(root: &Path, key: &CanonicalKey) -> io::Result<Option<String>> {
    Ok(load_canonical(root)?.remove(&(key.class.clone(), key.head.clone())))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new(tag: &str) -> Self {
            let mut path = std::env::temp_dir();
            path.push(format!("prism-index-{tag}-{}", owner_token()));
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    // A stealer must win the lock outright: it removes the presumed-stale file
    // and holds under its own stamp.
    #[test]
    fn steal_reacquires_a_stale_lock() {
        let tmp = TempDir::new("steal");
        let root = &tmp.path;
        fs::create_dir_all(index_dir(root)).unwrap();
        fs::write(index_dir(root).join(LOCK_FILE), b"dead-writer").unwrap();

        let lock = Lock::acquire(root).expect("steals the stale lock");
        assert!(
            lock.owned(),
            "holder must carry its own stamp after a steal"
        );
        drop(lock);
        assert!(
            !index_dir(root).join(LOCK_FILE).exists(),
            "an owned lock is released on drop"
        );
    }

    // Two writers contending over an index whose lock a dead writer left behind
    // must serialize through the steal, not both take it and clobber: both
    // bindings have to survive. Pre-fix, the loser also "held" and the later
    // whole-file rewrite dropped the winner's entry.
    #[test]
    fn contended_writers_keep_both_updates() {
        let tmp = TempDir::new("contend");
        let root: Arc<PathBuf> = Arc::new(tmp.path.clone());
        fs::create_dir_all(index_dir(&root)).unwrap();
        fs::write(index_dir(&root).join(LOCK_FILE), b"dead-writer").unwrap();

        let handles: Vec<_> = ["alpha", "beta"]
            .into_iter()
            .map(|k| {
                let root = Arc::clone(&root);
                thread::spawn(move || {
                    let mut m = BTreeMap::new();
                    m.insert(k.to_string(), format!("hash-{k}"));
                    bind_names(&root, &m).unwrap();
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }

        let names = load_names(&root).unwrap();
        assert_eq!(names.get("alpha").map(String::as_str), Some("hash-alpha"));
        assert_eq!(names.get("beta").map(String::as_str), Some("hash-beta"));
    }
}
