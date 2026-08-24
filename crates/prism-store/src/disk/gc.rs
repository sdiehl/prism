//! Mark-and-sweep garbage collection over the anonymous object and metadata
//! layers, with a bulk mode for trees that have outgrown in-place sweeping.
//!
//! The store's own contract ("everything is a cache") holds for the query and
//! index layers, whose entries are the only durable references into
//! `objects/`/`meta/` this crate can see: an object still bound by a
//! surviving query output, or still pointed at by `names`/`deps`/`canonical`/
//! `refs`, survives the sweep. Content addressed only by something outside the
//! store (a `prism.lock` pin in another project, for example) is invisible
//! here; a caller that must protect such content records a `refs` entry for it
//! first (see [`super::Store::set_ref`]).
//!
//! The age cutoff is the safety margin for exactly that blind spot, and for
//! the ordinary race between an in-progress write and this sweep: an object
//! newer than the cutoff survives even when unreferenced, so a commit that has
//! not yet reached its query/index binding is never swept out from under it.
//!
//! A layer (or a single query kind) holding vastly more files than eviction's
//! ceiling predates per-shard bounding or lost its eviction path; walking it
//! in place would grind for hours. The sweep instead retires the whole tree:
//! one rename moves it to a dot-prefixed sibling at the store root (readers
//! only open exact live paths, so the layer is healthy immediately), a
//! manifest written inside the tree before the rename records its origin as
//! data, and the drain then salvages what the live set still references or
//! what was written recently enough to be an in-flight commit, removing the
//! rest. A crash mid-drain leaves the tree in place; the next sweep finds it
//! by prefix, reads the manifest, and resumes.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, SystemTime};

use super::{
    atomic_write, census, index, queries, refresh_entry_age, unique_name, META_DIR, OBJECTS_DIR,
    OBJECT_SHARD_BUDGET, QUERIES_DIR, QUERY_SHARD_BUDGET, RETIRED_FORMAT, RETIRED_MANIFEST,
    RETIRED_PREFIX, SHARD_COUNT, SHARD_HEX, TEMP_PREFIX,
};

// The sweep fans out across a tree's shard subdirectories, one disjoint chunk
// of shards per worker. Both the scan (a readdir plus a stat per file) and
// the unlinks themselves parallelize across independent directories
// (concurrent per-directory removals scale well on the filesystems that
// matter here, degrading only when few directories remain), so the cap exists
// to leave the machine usable during a sweep, not because the filesystem
// serializes the work.
const GC_MAX_WORKERS: usize = 8;

// A layer or query kind whose census exceeds its eviction ceiling (every
// shard at its cap) by this factor is retired wholesale rather than swept in
// place.
const RUNAWAY_FACTOR: u64 = 4;

// What a drain keeps besides live-set members: anything written within this
// margin of the sweep's start, covering an in-flight commit racing the
// retirement. Deliberately not the sweep's age cutoff: bulk mode exists for
// trees whose bulk is unreferenced churn, and a multi-day margin would
// salvage nearly all of it back.
const RETIRE_FRESH_MARGIN: Duration = Duration::from_hours(1);

/// What one garbage-collection pass did, or, under `dry_run`, would do.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GcStats {
    /// Stale query bindings removed.
    pub queries_removed: u64,
    /// Anonymous objects removed.
    pub objects_removed: u64,
    /// Metadata blobs removed.
    pub meta_removed: u64,
    /// Bytes reclaimed from `objects/`, the layer that dominates store size;
    /// `meta/` blobs are small and not separately tracked.
    pub bytes_removed: u64,
    /// Files a bulk retirement salvaged back into a live layer instead of
    /// removing (still referenced, or fresh enough to be an in-flight write).
    pub salvaged: u64,
}

/// One progress beat from a sweep, carrying the running totals for the named
/// phase. Beats fire once per finished shard directory, from the sweep's
/// worker threads, so the callback must be `Sync`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GcProgress {
    /// Which part of the sweep is reporting, as shown to the user.
    pub phase: String,
    /// Shard directories finished within the phase.
    pub done: u64,
    /// Shard directories the phase will touch; zero when unknown up front.
    pub total: u64,
    /// Files removed so far within the phase.
    pub removed: u64,
    /// Bytes reclaimed so far within the phase.
    pub bytes: u64,
    /// Files salvaged back into a live layer so far within the phase.
    pub salvaged: u64,
}

/// The callback a sweep reports [`GcProgress`] beats through.
pub type GcProgressFn<'a> = &'a (dyn Fn(&GcProgress) + Sync);

/// Sweep the store rooted at `root`: prune query bindings older than
/// `cutoff`, then remove any object or metadata blob older than `cutoff` that
/// no surviving query output or index entry references. `dry_run` computes
/// what would be removed without touching the filesystem.
///
/// # Errors
/// Fails on a filesystem error or a malformed query/index entry.
pub(super) fn sweep(
    root: &Path,
    cutoff: SystemTime,
    dry_run: bool,
    progress: GcProgressFn<'_>,
) -> io::Result<GcStats> {
    let mut stats = GcStats::default();

    // Bulk mode fires before any walk, so a runaway tree is renamed aside
    // (and the live store healthy) without first paying a full crawl of it.
    // Dry runs never rename; they fall through to the in-place walk, which
    // reports exact counts at walking cost.
    if !dry_run {
        retire_runaway(root)?;
    }

    stats.queries_removed = queries::sweep_stale(root, cutoff, dry_run, progress)?.removed;

    let mut live = queries::live_outputs(root, cutoff)?;
    live.extend(index::all_referenced_hashes(root)?);

    let fresh_cutoff = SystemTime::now()
        .checked_sub(RETIRE_FRESH_MARGIN)
        .unwrap_or(SystemTime::UNIX_EPOCH);
    drain_retired(root, &live, fresh_cutoff, dry_run, progress, &mut stats)?;

    let (objects_removed, object_bytes) = sweep_layer(
        &root.join(OBJECTS_DIR),
        &live,
        cutoff,
        dry_run,
        OBJECTS_DIR,
        progress,
    )?;
    stats.objects_removed += objects_removed;
    stats.bytes_removed += object_bytes;
    let (meta_removed, _) = sweep_layer(
        &root.join(META_DIR),
        &live,
        cutoff,
        dry_run,
        META_DIR,
        progress,
    )?;
    stats.meta_removed += meta_removed;

    Ok(stats)
}

// A layer's retirement threshold: every shard at its cap, times the runaway
// factor. Below it the in-place sweep is affordable; above it the tree
// predates bounding or its eviction stopped firing.
const fn layer_ceiling(shard_cap: usize) -> u64 {
    RUNAWAY_FACTOR * shard_cap as u64 * SHARD_COUNT
}

// Rename every runaway layer and query kind aside for offline draining. The
// census makes the decision cheap even when a tree holds millions of files.
fn retire_runaway(root: &Path) -> io::Result<()> {
    let census = census::take(root)?;
    for layer in [OBJECTS_DIR, META_DIR] {
        if census.files(layer) > layer_ceiling(OBJECT_SHARD_BUDGET.cap) {
            retire_tree(root, &root.join(layer), layer)?;
        }
    }
    for row in &census.layers {
        let Some(kind) = query_kind(&row.name) else {
            continue;
        };
        if row.files > layer_ceiling(QUERY_SHARD_BUDGET.cap) {
            retire_tree(root, &root.join(QUERIES_DIR).join(kind), &row.name)?;
        }
    }
    Ok(())
}

// The kind a census row (or a retired-tree origin) names, when it names one.
fn query_kind(origin: &str) -> Option<&str> {
    origin
        .strip_prefix(QUERIES_DIR)
        .and_then(|rest| rest.strip_prefix('/'))
        .filter(|kind| !kind.is_empty())
}

// Retire one tree: record its origin inside it (as data; nothing ever parses
// the directory name back), then rename it to a unique dot-prefixed sibling
// at the store root. The rename is the entire visible cost; the tree drains
// afterwards, or on a later run if this one dies first.
fn retire_tree(root: &Path, src: &Path, origin: &str) -> io::Result<()> {
    atomic_write(
        &src.join(RETIRED_MANIFEST),
        format!("{RETIRED_FORMAT}\n{origin}\n").as_bytes(),
    )?;
    fs::rename(src, unique_name(root, RETIRED_PREFIX))
}

// The origin recorded inside a retired tree, when present and well-formed.
fn read_manifest(tree: &Path) -> Option<String> {
    let text = fs::read_to_string(tree.join(RETIRED_MANIFEST)).ok()?;
    let mut lines = text.lines();
    if lines.next() != Some(RETIRED_FORMAT) {
        return None;
    }
    let origin = lines.next()?.trim();
    (!origin.is_empty()).then(|| origin.to_string())
}

// What draining one retired tree (or shard of one) did.
#[derive(Debug, Clone, Copy, Default)]
struct Drained {
    removed: u64,
    bytes: u64,
    salvaged: u64,
}

// Drain every retired tree at the store root: this run's renames plus any
// leftover from a crashed one. Hash-keyed trees (objects, meta) salvage
// entries the live set references or that were written within the fresh
// margin; a retired query kind salvages nothing (a binding is recomputed,
// never worth carrying across a layer reset). A tree without a readable
// manifest also salvages nothing: it is unreferenced by construction, so
// removal only costs cache warmth.
fn drain_retired(
    root: &Path,
    live: &BTreeSet<String>,
    fresh_cutoff: SystemTime,
    dry_run: bool,
    progress: GcProgressFn<'_>,
    stats: &mut GcStats,
) -> io::Result<()> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        if !name.starts_with(RETIRED_PREFIX) || !entry.file_type()?.is_dir() {
            continue;
        }
        let tree = entry.path();
        let origin = read_manifest(&tree);
        let origin = origin.as_deref();
        let salvage_into = match origin {
            Some(layer @ (OBJECTS_DIR | META_DIR)) => Some(root.join(layer)),
            _ => None,
        };
        let drained = drain_tree(
            &tree,
            salvage_into.as_deref(),
            live,
            fresh_cutoff,
            dry_run,
            progress,
            origin.unwrap_or("retired"),
        )?;
        match origin {
            Some(META_DIR) => stats.meta_removed += drained.removed,
            Some(origin) if query_kind(origin).is_some() => {
                stats.queries_removed += drained.removed;
            }
            _ => stats.objects_removed += drained.removed,
        }
        stats.bytes_removed += drained.bytes;
        stats.salvaged += drained.salvaged;
        if !dry_run {
            fs::remove_dir_all(&tree)?;
        }
    }
    Ok(())
}

// Drain one retired tree. Shard-directory drains fan out like the layer
// sweep; files at the tree root (the manifest, layout stamps, temp relics)
// go with the tree's final removal and are not separately counted.
fn drain_tree(
    tree: &Path,
    salvage_into: Option<&Path>,
    live: &BTreeSet<String>,
    fresh_cutoff: SystemTime,
    dry_run: bool,
    progress: GcProgressFn<'_>,
    origin: &str,
) -> io::Result<Drained> {
    let mut shard_dirs: Vec<(String, PathBuf)> = Vec::new();
    for entry in fs::read_dir(tree)? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }
        if let Some(shard) = entry.file_name().to_str() {
            shard_dirs.push((shard.to_string(), entry.path()));
        }
    }
    let total = shard_dirs.len() as u64;
    let done = AtomicU64::new(0);
    let removed = AtomicU64::new(0);
    let bytes = AtomicU64::new(0);
    let salvaged = AtomicU64::new(0);
    let phase = format!("drain {origin}");
    fan_out(&shard_dirs, |(shard, dir)| {
        let d = drain_shard(shard, dir, salvage_into, live, fresh_cutoff, dry_run)?;
        removed.fetch_add(d.removed, Ordering::Relaxed);
        bytes.fetch_add(d.bytes, Ordering::Relaxed);
        salvaged.fetch_add(d.salvaged, Ordering::Relaxed);
        progress(&GcProgress {
            phase: phase.clone(),
            done: done.fetch_add(1, Ordering::Relaxed) + 1,
            total,
            removed: removed.load(Ordering::Relaxed),
            bytes: bytes.load(Ordering::Relaxed),
            salvaged: salvaged.load(Ordering::Relaxed),
        });
        Ok(())
    })?;
    Ok(Drained {
        removed: removed.into_inner(),
        bytes: bytes.into_inner(),
        salvaged: salvaged.into_inner(),
    })
}

// Drain one shard directory of a retired tree. An entry that vanishes
// mid-drain (an external cleanup racing this walk) reads as already removed.
fn drain_shard(
    shard: &str,
    dir: &Path,
    salvage_into: Option<&Path>,
    live: &BTreeSet<String>,
    fresh_cutoff: SystemTime,
    dry_run: bool,
) -> io::Result<Drained> {
    let entries = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Drained::default()),
        Err(e) => return Err(e),
    };
    let mut out = Drained::default();
    for entry in entries {
        let entry = entry?;
        if !entry.file_type()?.is_file() {
            continue;
        }
        let name = entry.file_name();
        let Some(rest) = name.to_str() else {
            continue;
        };
        if rest.starts_with(TEMP_PREFIX) {
            continue;
        }
        let meta = match entry.metadata() {
            Ok(meta) => meta,
            Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
            Err(e) => return Err(e),
        };
        if let Some(layer) = salvage_into {
            let referenced = live.contains(&format!("{shard}{rest}"));
            let fresh = meta.modified().is_ok_and(|m| m >= fresh_cutoff);
            if referenced || fresh {
                if !dry_run {
                    salvage(&entry.path(), &layer.join(shard).join(rest))?;
                }
                out.salvaged += 1;
                continue;
            }
        }
        if !dry_run {
            match fs::remove_file(entry.path()) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(e),
            }
        }
        out.removed += 1;
        out.bytes += meta.len();
    }
    Ok(out)
}

// Move one entry back into its live layer. A hard link carries the blob over
// without a copy; an entry already republished live wins and the retired copy
// is simply dropped. The salvaged file's age is refreshed so the next
// eviction sees it as current rather than inheriting its retired-era mtime.
fn salvage(from: &Path, to: &Path) -> io::Result<()> {
    if let Some(dir) = to.parent() {
        fs::create_dir_all(dir)?;
    }
    match fs::hard_link(from, to) {
        Ok(()) => refresh_entry_age(to),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(e),
    }
    let _ = fs::remove_file(from);
    Ok(())
}

// Run `work` over every item on a bounded worker pool, one disjoint chunk of
// items per worker, surfacing the first error (or a worker panic) once the
// workers finish.
fn fan_out<T, F>(items: &[T], work: F) -> io::Result<()>
where
    T: Sync,
    F: Fn(&T) -> io::Result<()> + Sync,
{
    if items.is_empty() {
        return Ok(());
    }
    let workers = thread::available_parallelism()
        .map_or(1, NonZeroUsize::get)
        .min(GC_MAX_WORKERS);
    let chunk_len = items.len().div_ceil(workers).max(1);
    let work = &work;
    thread::scope(|scope| {
        // Collected on purpose: materializing the handles spawns every worker
        // before the first join, so the chunks run concurrently instead of
        // spawn-join serially.
        #[allow(clippy::needless_collect)]
        let handles: Vec<_> = items
            .chunks(chunk_len)
            .map(|chunk| scope.spawn(move || chunk.iter().try_for_each(work)))
            .collect();
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .unwrap_or_else(|_| Err(io::Error::other("store gc worker panicked")))
            })
            .collect::<io::Result<Vec<()>>>()
    })?;
    Ok(())
}

// Walk one sharded layer (`objects/<2hex>/<rest>` or `meta/<2hex>/<rest>`),
// removing every file whose reconstructed hash is absent from `live` and
// whose mtime is older than `cutoff`, fanning the per-shard scans out across
// the worker pool with a beat per finished shard. Returns (files removed,
// bytes removed).
fn sweep_layer(
    dir: &Path,
    live: &BTreeSet<String>,
    cutoff: SystemTime,
    dry_run: bool,
    layer: &str,
    progress: GcProgressFn<'_>,
) -> io::Result<(u64, u64)> {
    let shards = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok((0, 0)),
        Err(e) => return Err(e),
    };
    let mut shard_dirs: Vec<(String, PathBuf)> = Vec::new();
    for shard_entry in shards {
        let shard_entry = shard_entry?;
        if !shard_entry.file_type()?.is_dir() {
            continue;
        }
        let shard = shard_entry.file_name();
        let Some(shard) = shard.to_str() else {
            continue;
        };
        if shard.len() != SHARD_HEX {
            continue;
        }
        shard_dirs.push((shard.to_string(), shard_entry.path()));
    }
    let total = shard_dirs.len() as u64;
    let done = AtomicU64::new(0);
    let removed = AtomicU64::new(0);
    let bytes = AtomicU64::new(0);
    let phase = format!("sweep {layer}");
    fan_out(&shard_dirs, |(shard, path)| {
        let (r, b) = sweep_shard(shard, path, live, cutoff, dry_run)?;
        removed.fetch_add(r, Ordering::Relaxed);
        bytes.fetch_add(b, Ordering::Relaxed);
        progress(&GcProgress {
            phase: phase.clone(),
            done: done.fetch_add(1, Ordering::Relaxed) + 1,
            total,
            removed: removed.load(Ordering::Relaxed),
            bytes: bytes.load(Ordering::Relaxed),
            salvaged: 0,
        });
        Ok(())
    })?;
    Ok((removed.into_inner(), bytes.into_inner()))
}

// Sweep one shard directory. An entry that vanishes mid-sweep (an evicting
// publish or an external cleanup racing this walk) reads as already
// collected, never as an error.
fn sweep_shard(
    shard: &str,
    dir: &Path,
    live: &BTreeSet<String>,
    cutoff: SystemTime,
    dry_run: bool,
) -> io::Result<(u64, u64)> {
    let entries = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok((0, 0)),
        Err(e) => return Err(e),
    };
    let mut removed = 0u64;
    let mut bytes = 0u64;
    for file_entry in entries {
        let file_entry = file_entry?;
        if !file_entry.file_type()?.is_file() {
            continue;
        }
        let name = file_entry.file_name();
        let Some(rest) = name.to_str() else {
            continue;
        };
        if rest.starts_with(TEMP_PREFIX) {
            continue;
        }
        let hash = format!("{shard}{rest}");
        if live.contains(&hash) {
            continue;
        }
        let meta = match file_entry.metadata() {
            Ok(meta) => meta,
            Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
            Err(e) => return Err(e),
        };
        if meta.modified()? >= cutoff {
            continue;
        }
        if !dry_run {
            match fs::remove_file(file_entry.path()) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(e),
            }
        }
        removed += 1;
        bytes += meta.len();
    }
    Ok((removed, bytes))
}
