//! Crash-safe durable form of the observation trace.
//!
//! A `.replay` log is the ordered list of a run's observations (see [`trace`]).
//! For durable resume the same file is written *while* the program runs: a
//! process killed anywhere in the write must, on restart, recover the last
//! committed observation and never read a torn frame as valid, so a resumed run
//! continues from exactly the observations that reached disk.
//!
//! Two write disciplines carry that guarantee, mirroring the content-addressed
//! store's two disciplines:
//!
//! - **Atomic snapshot** ([`write_atomic`]). A whole trace is written to a
//!   uniquely named temp file, flushed, then renamed into place. The rename is
//!   atomic on POSIX, so a reader sees the complete old file or the complete new
//!   one, never a torn write; a crash before the rename leaves only inert temp
//!   scratch. This is how `run --record` persists a finished trace.
//!
//! - **Incremental append** ([`DurableLog`]). Each new observation is appended
//!   to a growing log, then a versioned sidecar index (`<log>.idx`) is rewritten
//!   atomically to name the new committed byte length. The index rename is the
//!   sole commit point: the committed extent advances only when it succeeds, so
//!   a crash at any earlier step leaves the previous committed prefix and any
//!   half-written trailing bytes are truncated on recovery, never decoded. This
//!   is the substrate a durable-resume handler appends to per observation.
//!
//! The log body is exactly the pinned `.replay` frame stream in both cases, so a
//! log written here and one written by `Replay.pr`'s `durable` handler are the
//! same bytes and either reads the other. Only the sidecar index is new, and it
//! carries its own version tag.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::debug::trace;
use crate::eval::Obs;

// The sidecar index schema tag, its own first line. A foreign or future tag is
// refused rather than misread; the trace body reuses the pinned `.replay` frame
// format and carries no separate version of its own.
const IDX_VERSION: &str = "prism-replay-idx-v1";

// The sidecar lives beside the log, sharing its path plus this suffix.
const IDX_SUFFIX: &str = "idx";

// Every in-flight write carries this prefix so a killed writer leaves only inert
// scratch a reader never opens (readers only ever open the exact log/index path).
const TEMP_PREFIX: &str = ".tmp.";

/// The sidecar index path for a log path (`<log>.idx`).
#[must_use]
pub fn index_path(log_path: &Path) -> PathBuf {
    let mut name = log_path.file_name().unwrap_or_default().to_os_string();
    name.push(".");
    name.push(IDX_SUFFIX);
    log_path.with_file_name(name)
}

// A unique temp path in `dir`; the temp prefix marks it as never a committed
// file, so a reader ignores a temp left by a killed writer.
fn unique_temp(dir: &Path) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    dir.join(format!("{TEMP_PREFIX}{pid}.{nanos}.{n}"))
}

// The directory a durable file publishes into; every such path has one.
fn parent_dir(path: &Path) -> io::Result<&Path> {
    path.parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map_or_else(|| Ok(Path::new(".")), Ok)
}

fn read_if_present(path: &Path) -> io::Result<Option<String>> {
    match fs::read_to_string(path) {
        Ok(s) => Ok(Some(s)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

// Parse the committed byte length from a sidecar index body, checking its schema
// tag first. A foreign/future tag or a malformed body is a hard error: the index
// is a durability record, not a cache, so a reader must refuse to guess.
fn parse_index(body: &str) -> io::Result<u64> {
    let mut lines = body.lines();
    let version = lines.next().unwrap_or_default();
    if version != IDX_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "replay log index has foreign schema {version:?}; \
                 this build speaks {IDX_VERSION:?}"
            ),
        ));
    }
    lines
        .next()
        .and_then(|n| n.trim().parse::<u64>().ok())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "replay log index is missing its committed length",
            )
        })
}

fn render_index(committed_len: u64) -> String {
    format!("{IDX_VERSION}\n{committed_len}\n")
}

// The recovered committed prefix of a log at `path`: the frames that are durably
// committed, and the byte length of that prefix (a frame boundary).
//
// With a sidecar index present the committed length is authoritative: the log is
// truncated to it (dropping any bytes a killed writer half-appended past the
// commit point) and that prefix must decode cleanly, so a torn tail is never read
// as valid while genuine corruption within the committed extent is a hard error.
// Without an index the file is a snapshot or a foreign trace with no committed
// boundary to trust, so it is decoded strictly in full: a malformed such file is
// rejected with a pointed diagnostic rather than silently truncated.
fn recover(path: &Path) -> io::Result<(Vec<Obs>, u64)> {
    let log = read_if_present(path)?.unwrap_or_default();
    let invalid = |e: String| io::Error::new(io::ErrorKind::InvalidData, e);
    let Some(idx_body) = read_if_present(&index_path(path))? else {
        // No committed boundary to trust: a snapshot or foreign trace, decoded
        // strictly in full so a malformed file is rejected, not truncated.
        let frames = trace::decode(&log).map_err(invalid)?;
        return Ok((frames, log.len() as u64));
    };
    let committed = parse_index(&idx_body)?;
    let committed_usize = usize::try_from(committed)
        .map_err(|_| invalid("replay log index length overflow".into()))?;
    if committed_usize > log.len() {
        return Err(invalid(format!(
            "replay log at {} is shorter ({} bytes) than its committed \
             length ({committed} bytes): committed observations were lost",
            path.display(),
            log.len()
        )));
    }
    let frames = trace::decode(&log[..committed_usize]).map_err(|e| {
        invalid(format!(
            "replay log at {} is corrupt within its committed prefix: {e}",
            path.display()
        ))
    })?;
    Ok((frames, committed))
}

/// The committed observation frames of a `.replay` log at `path`, recovering a
/// log killed mid-append to its last committed observation.
///
/// A log with a sidecar index is truncated (in the returned frames) to its
/// committed extent; a log without one is decoded to its longest well-formed
/// frame prefix. Either way a torn trailing frame is dropped, never served.
///
/// # Errors
/// Fails when the log is shorter than its committed length, when the committed
/// prefix is itself corrupt, or on a filesystem error.
pub fn committed_frames(path: &Path) -> io::Result<Vec<Obs>> {
    Ok(recover(path)?.0)
}

/// The recovered committed trace of a `.replay` log, re-encoded to its canonical
/// string form.
///
/// A clean log round-trips to identical bytes; a log killed mid-append yields its
/// committed prefix with the torn tail dropped.
///
/// # Errors
/// As [`committed_frames`].
pub fn committed_trace(path: &Path) -> io::Result<String> {
    Ok(trace::encode(&committed_frames(path)?))
}

/// Write `trace` to `path` atomically.
///
/// Full write plus flush to a unique temp in the same directory, then rename into
/// place. A reader sees the complete old file or the complete new one; a crash
/// before the rename leaves only temp scratch and the previous file intact.
///
/// # Errors
/// Fails on any filesystem error.
pub fn write_atomic(path: &Path, trace: &str) -> io::Result<()> {
    let dir = parent_dir(path)?;
    fs::create_dir_all(dir)?;
    let tmp = unique_temp(dir);
    let mut f = File::create(&tmp)?;
    #[cfg(test)]
    faults::hit(faults::FaultPoint::Open)?;
    #[cfg(test)]
    faults::partial_write(&mut f, trace.as_bytes(), faults::FaultPoint::WritePrefix)?;
    f.write_all(trace.as_bytes())?;
    #[cfg(test)]
    faults::hit(faults::FaultPoint::WriteBody)?;
    f.sync_all()?;
    #[cfg(test)]
    faults::hit(faults::FaultPoint::Flush)?;
    drop(f);
    #[cfg(test)]
    faults::hit(faults::FaultPoint::Rename)?;
    let renamed = fs::rename(&tmp, path);
    if renamed.is_err() {
        let _ = fs::remove_file(&tmp);
    }
    renamed
}

/// An open crash-safe append-only replay log.
///
/// Its committed extent is pinned by the sidecar index, and [`open`](Self::open)
/// truncates any uncommitted trailing bytes so subsequent appends land cleanly.
#[derive(Debug)]
pub struct DurableLog {
    log_path: PathBuf,
    idx_path: PathBuf,
    // Committed byte length of the log (always a frame boundary).
    committed: u64,
}

impl DurableLog {
    /// Open (creating if absent) the log at `path`, recovering it to its last
    /// committed observation. Returns the handle and the committed frames a
    /// resuming run replays before performing new observations.
    ///
    /// Uncommitted trailing bytes left by a killed writer are physically
    /// truncated, so the file holds exactly the committed prefix afterward, and
    /// the committed extent is pinned by a sidecar index before control returns.
    /// Pinning it here is what lets a crash during the very first append (before
    /// that append writes its own index) recover to the committed prefix rather
    /// than strict-decoding the uncommitted bytes as valid.
    ///
    /// # Errors
    /// Fails when the committed prefix is corrupt or on a filesystem error.
    pub fn open(path: &Path) -> io::Result<(Self, Vec<Obs>)> {
        let idx_path = index_path(path);
        let had_index = idx_path.exists();
        let (frames, committed) = recover(path)?;
        let log = Self {
            log_path: path.to_path_buf(),
            idx_path,
            committed,
        };
        // Drop any torn tail physically so future appends extend the committed
        // prefix, not garbage. A missing log is a fresh, empty committed prefix.
        if let Ok(f) = OpenOptions::new().write(true).open(&log.log_path) {
            if f.metadata().map_or(committed, |m| m.len()) != committed {
                f.set_len(committed)?;
                f.sync_all()?;
            }
        }
        // Adopt a foreign or fresh log into the append discipline by pinning its
        // committed extent, so the index is authoritative from the first append.
        if !had_index {
            log.commit_index(committed)?;
        }
        Ok((log, frames))
    }

    /// The committed byte length of the log (a frame boundary).
    #[must_use]
    pub const fn committed_len(&self) -> u64 {
        self.committed
    }

    /// Append one observation and commit it durably.
    ///
    /// The frame is appended to the log, the log is flushed, then the sidecar
    /// index is rewritten atomically to name the new committed length. The index
    /// rename is the sole commit point: on any earlier crash the observation is
    /// uncommitted and a resuming run re-performs it, so an already-committed
    /// observation is never duplicated and a torn frame is never read as valid.
    ///
    /// # Errors
    /// Fails on any filesystem error (including an injected crash under test).
    pub fn append(&mut self, obs: &Obs) -> io::Result<()> {
        let (header, payload) = trace::frame_halves(obs);
        let frame_len = (header.len() + payload.len()) as u64;

        let mut log = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_path)?;
        #[cfg(test)]
        faults::hit(faults::FaultPoint::Open)?;

        log.write_all(header.as_bytes())?;
        #[cfg(test)]
        faults::sync_then_fail(&log, faults::FaultPoint::WritePrefix)?;
        #[cfg(test)]
        faults::partial_write(&mut log, payload.as_bytes(), faults::FaultPoint::WriteBody)?;
        log.write_all(payload.as_bytes())?;
        #[cfg(test)]
        faults::hit(faults::FaultPoint::AppendLog)?;

        log.sync_all()?;
        #[cfg(test)]
        faults::hit(faults::FaultPoint::Flush)?;

        self.commit_index(self.committed + frame_len)?;
        self.committed += frame_len;
        Ok(())
    }

    // Rewrite the sidecar index to `committed_len` atomically (temp write, flush,
    // rename). The rename replaces the previous index in one step, so a crash
    // before it leaves the previous committed length authoritative.
    fn commit_index(&self, committed_len: u64) -> io::Result<()> {
        let dir = parent_dir(&self.idx_path)?;
        let tmp = unique_temp(dir);
        let mut f = File::create(&tmp)?;
        f.write_all(render_index(committed_len).as_bytes())?;
        f.sync_all()?;
        #[cfg(test)]
        faults::hit(faults::FaultPoint::UpdateIndex)?;
        drop(f);
        #[cfg(test)]
        faults::hit(faults::FaultPoint::Rename)?;
        let renamed = fs::rename(&tmp, &self.idx_path);
        if renamed.is_err() {
            let _ = fs::remove_file(&tmp);
        }
        renamed
    }
}

/// Test-only fault injection for the durable log's persistence discipline.
///
/// One named crash point per persistence step lets a test kill a writer at each
/// stage and prove restart safety on reopen. The seam is armed per thread and
/// one-shot: firing disarms it, so the retry after a simulated crash runs clean,
/// exactly like a fresh process. Compiled only under `cfg(test)`, so production
/// builds carry no fault-checking code.
#[cfg(test)]
pub(crate) mod faults {
    use std::cell::Cell;
    use std::fs::File;
    use std::io::{self, Write};

    /// The persistence steps a durable write passes through, the crash matrix
    /// from the fault-injection specification: open, write prefix, write body,
    /// flush, rename, update index, append log.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum FaultPoint {
        /// After opening the file, before any bytes are written.
        Open,
        /// After the frame header (its self-delimiting prefix) reaches disk.
        WritePrefix,
        /// Mid frame body: only a prefix of the payload reaches disk.
        WriteBody,
        /// After the whole frame is appended, before the log is flushed.
        AppendLog,
        /// After the log is flushed, before the index commit.
        Flush,
        /// After the new index temp is written, before the commit rename.
        UpdateIndex,
        /// At the commit rename itself (the atomic commit point).
        Rename,
    }

    /// Marker on every injected error so tests tell a simulated crash from a real
    /// filesystem failure.
    pub(crate) const INJECTED_MARKER: &str = "injected durable-log fault";

    // A partial write keeps one part in this many of the payload: provably short
    // for any payload of at least two bytes, nonempty so bytes really land.
    const PARTIAL_WRITE_DIVISOR: usize = 2;

    thread_local! {
        static ARMED: Cell<Option<FaultPoint>> = const { Cell::new(None) };
    }

    /// Arm `point` for the current thread; the next write that reaches it fails
    /// once.
    pub(crate) fn arm(point: FaultPoint) {
        ARMED.with(|a| a.set(Some(point)));
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

    /// Flush already-written bytes durable, then fail, so the partial frame is
    /// really on disk (the worst case a reopening reader can face).
    pub(crate) fn sync_then_fail(file: &File, point: FaultPoint) -> io::Result<()> {
        if take(point) {
            file.sync_all()?;
            Err(injected(point))
        } else {
            Ok(())
        }
    }

    /// The mid-write crash: put a flushed prefix of `bytes` on disk and fail, so
    /// a genuinely torn frame body reaches the file.
    pub(crate) fn partial_write(
        file: &mut File,
        bytes: &[u8],
        point: FaultPoint,
    ) -> io::Result<()> {
        if !take(point) {
            return Ok(());
        }
        file.write_all(&bytes[..bytes.len() / PARTIAL_WRITE_DIVISOR])?;
        file.sync_all()?;
        Err(injected(point))
    }
}

#[cfg(test)]
mod tests;
