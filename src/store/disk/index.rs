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
use std::path::{Path, PathBuf};

#[cfg(unix)]
use rustix::fs::{flock, FlockOperation};

use super::{atomic_write, FIELD_SEP, INDEX_DIR, LIST_SEP, LOCK_FILE};

const NAMES_FILE: &str = "names";
const DEPS_FILE: &str = "deps";
const CANONICAL_FILE: &str = "canonical";
const REFS_FILE: &str = "refs";

const NAMES_HEADER: &str = "prism-store-names\tv1";
const DEPS_HEADER: &str = "prism-store-deps\tv1";
const CANONICAL_HEADER: &str = "prism-store-canonical\tv1";
const REFS_HEADER: &str = "prism-store-refs\tv1";

/// A `(class, type-head)` pair identifying a canonical instance binding. This is
/// the on-disk key shape; coherence enforcement owns the semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalKey {
    /// The class name (for example `Ord`).
    pub class: String,
    /// The type-head name (for example `Int`).
    pub head: String,
}

/// A canonical index transaction rejected a divergent binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalConflict {
    pub incoming_index: usize,
    pub key: CanonicalKey,
    pub existing: String,
    pub incoming: String,
}

fn index_dir(root: &Path) -> PathBuf {
    root.join(INDEX_DIR)
}

// The advisory lock serializing index writers: an exclusive `flock` on the lock
// file. A second writer -- in this process or another -- blocks in `acquire`
// until the holder releases, and the kernel drops the lock when the holder's
// file handle closes, including on a crash, so a killed writer never leaves a
// stale lock to deadlock or race a steal against. Readers do not lock (see the
// module header). Holding the open handle is holding the lock; `Drop` (closing
// the file) releases it.
struct Lock {
    _file: fs::File,
}

impl Lock {
    fn acquire(root: &Path) -> io::Result<Self> {
        let dir = index_dir(root);
        fs::create_dir_all(&dir)?;
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(dir.join(LOCK_FILE))?;
        lock_exclusive(&file)?;
        Ok(Self { _file: file })
    }
}

// Take the exclusive advisory lock, blocking until no other handle holds it. On
// non-unix targets (the wasm build has neither real threads nor a filesystem)
// this degrades to a no-op: acquisition succeeds without mutual exclusion.
#[cfg(unix)]
fn lock_exclusive(file: &fs::File) -> io::Result<()> {
    flock(file, FlockOperation::LockExclusive).map_err(io::Error::from)
}

#[cfg(not(unix))]
fn lock_exclusive(_file: &fs::File) -> io::Result<()> {
    Ok(())
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

pub(super) fn merge_canonicals(
    root: &Path,
    bindings: &[(CanonicalKey, String)],
) -> io::Result<Result<(), CanonicalConflict>> {
    let _lock = Lock::acquire(root)?;
    let mut map = load_canonical(root)?;
    for (incoming_index, (key, incoming)) in bindings.iter().enumerate() {
        if let Some(existing) = map.get(&(key.class.clone(), key.head.clone())) {
            if existing != incoming {
                return Ok(Err(CanonicalConflict {
                    incoming_index,
                    key: key.clone(),
                    existing: existing.clone(),
                    incoming: incoming.clone(),
                }));
            }
        }
    }
    for (key, incoming) in bindings {
        map.insert((key.class.clone(), key.head.clone()), incoming.clone());
    }
    write_canonical(root, &map)?;
    Ok(Ok(()))
}

pub(super) fn canonical(root: &Path, key: &CanonicalKey) -> io::Result<Option<String>> {
    Ok(load_canonical(root)?.remove(&(key.class.clone(), key.head.clone())))
}

// The `refs` index: mutable, caller-named pointers into the immutable object
// layer (git refs). A ref names one blob by its content hash; repointing it
// leaves the old object in place. Kept apart from `names` so a definition name
// and a caller tag can never collide on one slot.
fn load_refs(root: &Path) -> io::Result<BTreeMap<String, String>> {
    let mut map = BTreeMap::new();
    for line in read_lines(&index_dir(root).join(REFS_FILE), REFS_HEADER)? {
        if let Some((name, hash)) = line.split_once(FIELD_SEP) {
            map.insert(name.to_string(), hash.to_string());
        }
    }
    Ok(map)
}

fn write_refs(root: &Path, map: &BTreeMap<String, String>) -> io::Result<()> {
    let mut body = String::from(REFS_HEADER);
    body.push('\n');
    for (name, hash) in map {
        let _ = writeln!(body, "{name}{FIELD_SEP}{hash}");
    }
    atomic_write(&index_dir(root).join(REFS_FILE), body.as_bytes())
}

pub(super) fn set_ref(root: &Path, name: &str, hash: &str) -> io::Result<()> {
    let _lock = Lock::acquire(root)?;
    let mut map = load_refs(root)?;
    map.insert(name.to_string(), hash.to_string());
    write_refs(root, &map)
}

pub(super) fn get_ref(root: &Path, name: &str) -> io::Result<Option<String>> {
    Ok(load_refs(root)?.remove(name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Arc;
    use std::thread;

    // A per-process counter so concurrent tests never collide on a temp dir.
    static NONCE: AtomicU64 = AtomicU64::new(0);

    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new(tag: &str) -> Self {
            let mut path = std::env::temp_dir();
            let n = NONCE.fetch_add(1, Ordering::Relaxed);
            path.push(format!("prism-index-{tag}-{}-{n}", std::process::id()));
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    // A lock file a dead writer left behind holds no kernel lock, so a new writer
    // acquires immediately rather than deadlocking, and re-acquires after release:
    // the crash-safety the advisory `flock` buys over a hand-rolled steal.
    #[test]
    fn stale_lock_file_does_not_block() {
        let tmp = TempDir::new("stale");
        let root = &tmp.path;
        fs::create_dir_all(index_dir(root)).unwrap();
        fs::write(index_dir(root).join(LOCK_FILE), b"dead-writer").unwrap();

        drop(Lock::acquire(root).expect("a leftover lock file must not block"));
        drop(Lock::acquire(root).expect("re-acquires after release"));
    }

    // Two writers contending over an index whose lock a dead writer left behind
    // must serialize, not both proceed and clobber: both bindings have to survive.
    // Pre-fix, a racy lock-steal let both "hold" and the later whole-file rewrite
    // dropped the winner's entry.
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

    #[test]
    fn canonical_merge_rejects_conflict_without_overwrite() {
        let tmp = TempDir::new("canonical-conflict");
        let root = &tmp.path;
        fs::create_dir_all(index_dir(root)).unwrap();
        let key = CanonicalKey {
            class: "Ord".to_string(),
            head: "Int".to_string(),
        };

        assert_eq!(
            merge_canonicals(root, &[(key.clone(), "hash-a".to_string())]).unwrap(),
            Ok(()),
        );
        assert_eq!(
            merge_canonicals(root, &[(key.clone(), "hash-b".to_string())]).unwrap(),
            Err(CanonicalConflict {
                incoming_index: 0,
                key: key.clone(),
                existing: "hash-a".to_string(),
                incoming: "hash-b".to_string(),
            }),
        );
        assert_eq!(canonical(root, &key).unwrap().as_deref(), Some("hash-a"));
    }
}
