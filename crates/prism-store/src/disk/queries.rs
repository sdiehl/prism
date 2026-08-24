use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::time::SystemTime;

use super::{
    atomic_write_if_absent, evict_shard_overflow, refresh_entry_age, runaway_estimate, shard_path,
    GcProgress, GcProgressFn, StoreHash, QUERIES_DIR, QUERY_SHARD_BUDGET, SAMPLE_SHARD,
    SHARD_COUNT,
};

#[cfg(test)]
use super::faults::{self, FaultPoint};

const QUERY_FORMAT: &str = "prism-query-index-v1";

// The query layer's own layout version, stamped at `queries/LAYOUT` when the
// first binding is published. It moves independently of the store-wide
// `STORE_FORMAT` stamp because query bindings are disposable cache metadata:
// a layout change here must never refuse the objects, certificates, and
// decision records beside them. A tree that predates this stamp (the flat
// pre-sharding layout) is never opened through the sharded paths, so its
// bindings read as ordinary misses, and `sweep_stale` removes its relic files
// unconditionally rather than migrating them.
const QUERY_LAYOUT_FILE: &str = "LAYOUT";
const QUERY_LAYOUT: &str = "prism-query-layout-v2";

// Tripwire threshold for a broken eviction path: a kind holding this many
// bindings is worth naming (once per process, see `runaway_estimate`) long
// before it grows into a disk-eating catalog.
const QUERY_KIND_WARN_ENTRIES: u64 = 1 << 20;

static KIND_SIZE_WARNED: AtomicBool = AtomicBool::new(false);

// The stale-binding sweep's walk has no total known up front, so it beats a
// running removal count every this many removals.
const QUERY_SWEEP_BEAT: u64 = 1024;

fn kind_ok(kind: &str) -> bool {
    !kind.is_empty()
        && kind
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b'-' | b'.'))
}

// A binding's path is sharded on the key like every other layer, so a hot
// kind never accumulates one flat directory holding every entry it ever
// bound: `queries/<kind>/<first 2 hex>/<rest>`.
fn path(root: &Path, kind: &str, key: &StoreHash<'_>) -> io::Result<PathBuf> {
    if !kind_ok(kind) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "query kind must contain only lowercase ASCII, digits, '-' or '.'",
        ));
    }
    Ok(shard_path(&root.join(QUERIES_DIR).join(kind), key))
}

// Parse a query entry body (shared by a single lookup and a full-store walk):
// the format tag, then the bound output hash, and nothing else.
fn decode_output(text: &str) -> io::Result<String> {
    let mut lines = text.lines();
    if lines.next() != Some(QUERY_FORMAT) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "query entry has an unknown format",
        ));
    }
    let output = lines.next().unwrap_or_default();
    StoreHash::new(output)?;
    if lines.next().is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "query entry has trailing rows",
        ));
    }
    Ok(output.to_string())
}

pub(super) fn get(root: &Path, kind: &str, key: &StoreHash<'_>) -> io::Result<Option<String>> {
    let path = path(root, kind, key)?;
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    Ok(Some(decode_output(&text)?))
}

// Walk every kind directory under `queries/`, skipping in-flight temp files
// (see `TEMP_PREFIX`) and the layer's `LAYOUT` stamp. A live binding sits in a
// shard directory and reaches `f` with its decoded output hash; a plain file
// directly under a kind is a relic of the pre-sharding flat layout and reaches
// `f` with no output, never read, so a sweep can retire a huge stale catalog
// on unlinks alone.
fn walk(
    root: &Path,
    mut f: impl FnMut(&fs::DirEntry, Option<&str>) -> io::Result<()>,
) -> io::Result<()> {
    let dir = root.join(QUERIES_DIR);
    let kinds = match fs::read_dir(&dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };
    for kind_entry in kinds {
        let kind_entry = kind_entry?;
        if !kind_entry.file_type()?.is_dir() {
            continue;
        }
        // The layer self-evicts on publish and tolerates external cleanups,
        // so a directory or entry that vanishes mid-walk is a completed
        // removal, never an error.
        let shards = match fs::read_dir(kind_entry.path()) {
            Ok(rd) => rd,
            Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
            Err(e) => return Err(e),
        };
        for shard_entry in shards {
            let shard_entry = shard_entry?;
            let name = shard_entry.file_name();
            if name.to_string_lossy().starts_with(super::TEMP_PREFIX) {
                continue;
            }
            if shard_entry.file_type()?.is_file() {
                f(&shard_entry, None)?;
                continue;
            }
            let keys = match fs::read_dir(shard_entry.path()) {
                Ok(rd) => rd,
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(e),
            };
            for key_entry in keys {
                let key_entry = key_entry?;
                let name = key_entry.file_name();
                if !key_entry.file_type()?.is_file()
                    || name.to_string_lossy().starts_with(super::TEMP_PREFIX)
                {
                    continue;
                }
                let text = match fs::read_to_string(key_entry.path()) {
                    Ok(text) => text,
                    Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                    Err(e) => return Err(e),
                };
                let output = decode_output(&text)?;
                f(&key_entry, Some(&output))?;
            }
        }
    }
    Ok(())
}

/// Every hash bound as the output of a query entry not older than `cutoff`.
/// Gc's mark phase: an object still pointed at by a surviving query binding
/// must survive the object-layer sweep. `cutoff` matches [`sweep_stale`] so an
/// entry this call would itself prune never marks its output live, regardless
/// of whether the caller is dry-running or actually sweeping.
///
/// # Errors
/// Fails on a filesystem error or a malformed query entry.
pub(super) fn live_outputs(root: &Path, cutoff: SystemTime) -> io::Result<BTreeSet<String>> {
    let mut out = BTreeSet::new();
    walk(root, |entry, output| {
        // A pre-shard relic carries no output: its binding is already
        // invalidated by the layout bump, so it never marks an object live.
        if let Some(output) = output {
            match entry.metadata().and_then(|m| m.modified()) {
                Ok(modified) if modified >= cutoff => {
                    out.insert(output.to_string());
                }
                Ok(_) => {}
                // Concurrently retired; a gone binding marks nothing live.
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    })?;
    Ok(out)
}

/// What one stale-binding sweep did.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct QuerySweepStats {
    pub removed: u64,
}

/// Remove query bindings whose file was last written before `cutoff`, plus
/// every relic of the pre-sharding flat layout regardless of age (the layout
/// bump already invalidated those bindings, so removal is the deferred bulk
/// invalidation, never a migration). A pruned binding is an ordinary future
/// cache miss (see [`get`]); nothing else in the store depends on a query
/// entry's continued existence, so this is always safe regardless of what it
/// pointed at.
///
/// # Errors
/// Fails on a filesystem error or a malformed query entry.
pub(super) fn sweep_stale(
    root: &Path,
    cutoff: SystemTime,
    dry_run: bool,
    progress: GcProgressFn<'_>,
) -> io::Result<QuerySweepStats> {
    let mut stats = QuerySweepStats::default();
    walk(root, |entry, output| {
        if output.is_some() {
            match entry.metadata().and_then(|m| m.modified()) {
                Ok(modified) if modified >= cutoff => return Ok(()),
                Ok(_) => {}
                // Concurrently retired; nothing left to remove or count.
                Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
                Err(e) => return Err(e),
            }
        }
        if !dry_run {
            match fs::remove_file(entry.path()) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
                Err(e) => return Err(e),
            }
        }
        stats.removed += 1;
        if stats.removed % QUERY_SWEEP_BEAT == 0 {
            progress(&GcProgress {
                phase: format!("sweep {QUERIES_DIR}"),
                done: 0,
                total: 0,
                removed: stats.removed,
                bytes: 0,
                salvaged: 0,
            });
        }
        Ok(())
    })?;
    Ok(stats)
}

// Stamp the layer's layout version beside the kind directories. Only the
// write path pays the existence probe; readers rely on the layout structurally
// (a pre-shard tree simply never matches a sharded path).
fn stamp_layout(root: &Path) -> io::Result<()> {
    let stamp = root.join(QUERIES_DIR).join(QUERY_LAYOUT_FILE);
    if !stamp.exists() {
        atomic_write_if_absent(&stamp, format!("{QUERY_LAYOUT}\n").as_bytes())?;
    }
    Ok(())
}

// The runaway-kind tripwire (see `runaway_estimate` for the sampling scheme):
// names the kind so the user knows which query family outgrew its bounds.
fn warn_if_runaway_kind(kind: &str, key: &StoreHash<'_>, entry: &Path) {
    if !key.as_str().starts_with(SAMPLE_SHARD) {
        return;
    }
    let Some(shard_dir) = entry.parent() else {
        return;
    };
    let threshold = QUERY_KIND_WARN_ENTRIES / SHARD_COUNT;
    if let Some(estimate) = runaway_estimate(shard_dir, threshold, &KIND_SIZE_WARNED) {
        eprintln!(
            "warning: store query kind {kind:?} holds roughly {estimate} bindings; \
             `prism store gc` prunes stale ones"
        );
    }
}

pub(super) fn put(
    root: &Path,
    kind: &str,
    key: &StoreHash<'_>,
    output: &StoreHash<'_>,
) -> io::Result<()> {
    let path = path(root, kind, key)?;
    if let Some(existing) = get(root, kind, key)? {
        if existing == output.as_str() {
            // A re-publish confirms the binding is hot; refreshing its age
            // keeps it ahead of colder entries when its shard evicts.
            refresh_entry_age(&path);
            return Ok(());
        }
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "query {kind}/{} already maps to {existing}, not {output}",
                key.as_str()
            ),
        ));
    }
    #[cfg(test)]
    faults::hit(FaultPoint::BeforeQueryPublish)?;
    stamp_layout(root)?;
    let bytes = format!("{QUERY_FORMAT}\n{}\n", output.as_str());
    if atomic_write_if_absent(&path, bytes.as_bytes())? {
        if let Some(shard_dir) = path.parent() {
            evict_shard_overflow(shard_dir, &path, QUERY_SHARD_BUDGET);
        }
        warn_if_runaway_kind(kind, key, &path);
        return Ok(());
    }
    match get(root, kind, key)? {
        Some(existing) if existing == output.as_str() => Ok(()),
        Some(existing) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "query {kind}/{} concurrently mapped to {existing}, not {output}",
                key.as_str()
            ),
        )),
        None => Err(io::Error::new(
            io::ErrorKind::NotFound,
            "query entry disappeared during concurrent commit",
        )),
    }
}
