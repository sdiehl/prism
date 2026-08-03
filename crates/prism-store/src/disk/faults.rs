//! Test-only fault injection for the store's publication discipline.
//!
//! Every durable publication follows one shape: write the full bytes to a
//! uniquely named temp file, flush it, then commit with an atomic rename or
//! link. The hooks here let a test crash a writer at each stage of that shape
//! and prove restart safety on reopen: a killed writer leaves at most an inert
//! temp file, never a readable partial object, a query entry pointing at a
//! missing or wrong object, or an overwritten immutable blob.
//!
//! The seam is armed per thread and one-shot: firing disarms it, so the retry
//! after a simulated crash runs clean, exactly like a fresh process would.
//! This module and every call site are compiled only under `cfg(test)`, so
//! production builds carry no fault-checking code at all.

use std::cell::Cell;
use std::fs::File;
use std::io::{self, Write};

/// The named crash points, one per stage of the publication discipline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FaultPoint {
    /// Mid temp-file write: only a prefix of the bytes reaches disk.
    TempPartialWrite,
    /// After the full temp write, before the flush.
    BeforeFlush,
    /// After the flush, before the commit rename or link.
    AfterFlush,
    /// Immediately before the commit rename or link.
    BeforePublish,
    /// After the output object is confirmed published, before any query work.
    AfterObjectBeforeQuery,
    /// Inside query publication, after the existing-entry check, before the
    /// entry write begins.
    BeforeQueryPublish,
}

/// Marker carried by every injected error so tests can tell a simulated crash
/// from a real filesystem failure.
pub(crate) const INJECTED_MARKER: &str = "injected publication fault";

// A partial write keeps one part in this many of the payload: provably short
// for any payload of at least two bytes, nonempty so bytes really land.
const PARTIAL_WRITE_DIVISOR: usize = 2;

thread_local! {
    static ARMED: Cell<Option<FaultPoint>> = const { Cell::new(None) };
}

/// Arm `point` for the current thread; the next write path that reaches it
/// fails once.
pub(crate) fn arm(point: FaultPoint) {
    ARMED.with(|a| a.set(Some(point)));
}

/// Clear any armed point (for tests whose operation never reaches it).
pub(crate) fn disarm() {
    ARMED.with(|a| a.set(None));
}

// True exactly once after `arm(point)`: firing disarms.
fn take(point: FaultPoint) -> bool {
    ARMED.with(|a| {
        if a.get() == Some(point) {
            a.set(None);
            true
        } else {
            false
        }
    })
}

fn injected(point: FaultPoint) -> io::Error {
    io::Error::other(format!("{INJECTED_MARKER}: {point:?}"))
}

/// Fail here once when `point` is armed on this thread.
pub(crate) fn hit(point: FaultPoint) -> io::Result<()> {
    if take(point) {
        Err(injected(point))
    } else {
        Ok(())
    }
}

/// The mid-write crash: when armed, put a flushed prefix of `bytes` in the temp
/// file and fail, so the partial content is really on disk, the worst case a
/// reopening reader can face.
pub(crate) fn partial_write(file: &mut File, bytes: &[u8]) -> io::Result<()> {
    if !take(FaultPoint::TempPartialWrite) {
        return Ok(());
    }
    file.write_all(&bytes[..bytes.len() / PARTIAL_WRITE_DIVISOR])?;
    file.sync_all()?;
    Err(injected(FaultPoint::TempPartialWrite))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Barrier};
    use std::thread;

    use super::super::testutil::TempDir;
    use super::super::{Store, Written, TEMP_PREFIX};
    use super::*;

    // Distinct full-length hex identities for the corpus.
    const H_OBJ: &str = "0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec0bec";
    const H_KEY: &str = "4ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea14ea1";
    const H_OUT: &str = "0f100f100f100f100f100f100f100f100f100f100f100f100f100f100f100f10";
    const H_ALT: &str = "a17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17ea17e";

    const PAYLOAD: &[u8] = b"published object payload";
    const DIVERGENT: &[u8] = b"divergent object payload";
    const ALT_PAYLOAD: &[u8] = b"alternate query output";
    const QUERY_KIND: &str = "linked-native";
    const NAME_A: &str = "alpha";
    const NAME_B: &str = "beta";

    // Every stage of the shared temp-write, flush, commit discipline.
    const WRITE_PHASE: [FaultPoint; 4] = [
        FaultPoint::TempPartialWrite,
        FaultPoint::BeforeFlush,
        FaultPoint::AfterFlush,
        FaultPoint::BeforePublish,
    ];
    // The query-publication stages layered above it.
    const QUERY_PHASE: [FaultPoint; 2] = [
        FaultPoint::AfterObjectBeforeQuery,
        FaultPoint::BeforeQueryPublish,
    ];

    fn fresh(tag: &str) -> (TempDir, Store) {
        let tmp = TempDir::new(tag);
        let store = Store::open_or_create(&tmp.path).unwrap();
        (tmp, store)
    }

    fn reopen(tmp: &TempDir) -> Store {
        Store::open_or_create(&tmp.path).unwrap()
    }

    fn assert_injected(err: &io::Error, point: FaultPoint) {
        assert!(
            err.to_string().contains(INJECTED_MARKER),
            "{point:?}: expected an injected fault, got {err}"
        );
    }

    // All leftover in-flight files under `dir`, recursively.
    fn temp_files(dir: &Path) -> Vec<PathBuf> {
        let mut found = Vec::new();
        let Ok(entries) = fs::read_dir(dir) else {
            return found;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                found.extend(temp_files(&path));
            } else if path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with(TEMP_PREFIX))
            {
                found.push(path);
            }
        }
        found
    }

    fn bind_one(store: &Store, name: &str, hash: &str) -> io::Result<()> {
        let mut m = BTreeMap::new();
        m.insert(name.to_string(), hash.to_string());
        store.bind_names(&m)
    }

    // A crash at any write stage of object publication leaves no readable
    // partial, only an ignored temp; a retry converges to a normal publication
    // and immutability still holds against a later divergent writer.
    #[test]
    fn object_faults_leave_no_partial_and_retry_converges() {
        for point in WRITE_PHASE {
            let (tmp, store) = fresh("obj-fault");
            arm(point);
            let err = store.put(H_OBJ, PAYLOAD).unwrap_err();
            assert_injected(&err, point);

            // The crash left its temp behind, exactly like a killed writer.
            assert!(
                !temp_files(&tmp.path).is_empty(),
                "{point:?}: expected a leftover temp"
            );

            let store = reopen(&tmp);
            assert!(!store.has(H_OBJ), "{point:?}: partial object visible");
            assert!(
                store.get(H_OBJ).is_err(),
                "{point:?}: partial object readable"
            );

            assert_eq!(
                store.put(H_OBJ, PAYLOAD).unwrap(),
                Written::New,
                "{point:?}"
            );
            assert_eq!(store.get(H_OBJ).unwrap(), PAYLOAD, "{point:?}");

            // The published object is immutable despite the earlier crash.
            let err = store.put(H_OBJ, DIVERGENT).unwrap_err();
            assert!(!err.to_string().contains(INJECTED_MARKER), "{point:?}");
            assert_eq!(store.get(H_OBJ).unwrap(), PAYLOAD, "{point:?}");
        }
    }

    // A crash anywhere in query publication, including the window between
    // object and query publication, leaves a clean miss on reopen, never an
    // entry pointing at a missing or wrong object; a retry converges and a
    // divergent rebinding is still rejected.
    #[test]
    fn query_faults_never_leave_a_dangling_entry() {
        for point in WRITE_PHASE.into_iter().chain(QUERY_PHASE) {
            let (tmp, store) = fresh("query-fault");
            store.put(H_OUT, PAYLOAD).unwrap();

            arm(point);
            let err = store.put_query(QUERY_KIND, H_KEY, H_OUT).unwrap_err();
            assert_injected(&err, point);
            if WRITE_PHASE.contains(&point) {
                assert!(
                    !temp_files(&tmp.path).is_empty(),
                    "{point:?}: expected a leftover temp"
                );
            }

            let store = reopen(&tmp);
            assert_eq!(
                store.get_query(QUERY_KIND, H_KEY).unwrap(),
                None,
                "{point:?}: a torn query entry surfaced"
            );
            assert_eq!(store.get(H_OUT).unwrap(), PAYLOAD, "{point:?}");

            store.put_query(QUERY_KIND, H_KEY, H_OUT).unwrap();
            assert_eq!(
                store.get_query(QUERY_KIND, H_KEY).unwrap().as_deref(),
                Some(H_OUT),
                "{point:?}"
            );

            // Rebinding the key to a different (existing) output stays a hard
            // error and the surviving binding is unchanged.
            store.put(H_ALT, ALT_PAYLOAD).unwrap();
            assert!(
                store.put_query(QUERY_KIND, H_KEY, H_ALT).is_err(),
                "{point:?}"
            );
            assert_eq!(
                store.get_query(QUERY_KIND, H_KEY).unwrap().as_deref(),
                Some(H_OUT),
                "{point:?}"
            );
        }
    }

    // A crash while rewriting an index file preserves the prior whole file:
    // bindings committed earlier survive, the in-flight one vanishes, and a
    // retry lands it.
    #[test]
    fn index_faults_preserve_prior_bindings() {
        for point in WRITE_PHASE {
            let (tmp, store) = fresh("index-fault");
            bind_one(&store, NAME_A, H_OBJ).unwrap();

            arm(point);
            let err = bind_one(&store, NAME_B, H_OUT).unwrap_err();
            assert_injected(&err, point);

            let store = reopen(&tmp);
            assert_eq!(
                store.lookup_name(NAME_A).unwrap().as_deref(),
                Some(H_OBJ),
                "{point:?}: prior binding lost"
            );
            assert_eq!(store.lookup_name(NAME_B).unwrap(), None, "{point:?}");

            bind_one(&store, NAME_B, H_OUT).unwrap();
            assert_eq!(store.lookup_name(NAME_A).unwrap().as_deref(), Some(H_OBJ));
            assert_eq!(store.lookup_name(NAME_B).unwrap().as_deref(), Some(H_OUT));
        }
    }

    // One of two identical writers crashes mid-publication; the other and the
    // crashed writer's retry converge on exactly one published object.
    #[test]
    fn concurrent_identical_writers_converge_after_a_crash() {
        for point in WRITE_PHASE {
            let (_tmp, store) = fresh("concurrent-identical");
            let barrier = Arc::new(Barrier::new(2));

            let faulted = {
                let store = store.clone();
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    arm(point);
                    let first = store.put(H_OBJ, PAYLOAD);
                    barrier.wait();
                    let retry = store.put(H_OBJ, PAYLOAD);
                    (first, retry)
                })
            };
            let clean = {
                let store = store.clone();
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    store.put(H_OBJ, PAYLOAD)
                })
            };

            let (first, retry) = faulted.join().unwrap();
            let clean = clean.join().unwrap();
            assert_injected(&first.unwrap_err(), point);
            let survivors = [retry.unwrap(), clean.unwrap()];
            assert_eq!(
                survivors.iter().filter(|w| **w == Written::New).count(),
                1,
                "{point:?}: exactly one writer publishes, got {survivors:?}"
            );
            assert_eq!(store.get(H_OBJ).unwrap(), PAYLOAD, "{point:?}");
        }
    }

    // A writer that crashed before its commit point cannot later overwrite
    // content another writer published in the meantime: its retry collides
    // instead of silently winning.
    #[test]
    fn a_crashed_writer_cannot_overwrite_a_later_publication() {
        for point in WRITE_PHASE {
            let (tmp, store) = fresh("divergent-after-crash");
            arm(point);
            let err = store.put(H_OBJ, PAYLOAD).unwrap_err();
            assert_injected(&err, point);

            // Another writer wins the slot with different bytes (two payloads
            // on one hash models a collision; first published must win).
            store.put(H_OBJ, DIVERGENT).unwrap();

            let store = reopen(&tmp);
            let err = store.put(H_OBJ, PAYLOAD).unwrap_err();
            assert!(!err.to_string().contains(INJECTED_MARKER), "{point:?}");
            assert_eq!(store.get(H_OBJ).unwrap(), DIVERGENT, "{point:?}");
        }
    }

    // A warm hit on already-published content never re-enters the write path,
    // so an armed write fault has nothing to fire on.
    #[test]
    fn a_warm_hit_never_reaches_the_write_path() {
        let (_tmp, store) = fresh("warm-hit");
        store.put(H_OBJ, PAYLOAD).unwrap();
        for point in WRITE_PHASE {
            arm(point);
            assert_eq!(
                store.put(H_OBJ, PAYLOAD).unwrap(),
                Written::Hit,
                "{point:?}"
            );
            disarm();
        }
    }
}
