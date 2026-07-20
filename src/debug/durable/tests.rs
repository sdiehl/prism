//! The crash and fault-injection matrix for the durable replay log.
//!
//! A failure is injected after each persistence step (open, write prefix, write
//! body, flush, rename, update index, append log) of the two write disciplines,
//! and every acceptance gate is proven on restart:
//!
//! 1. restart yields the complete old state or the complete new state, never a
//!    partial or torn read;
//! 2. a torn write is never read as valid;
//! 3. replay never duplicates an already-committed observation;
//! 4. the resumed run's observation trace equals the uninterrupted run's.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use super::faults::{self, FaultPoint, INJECTED_MARKER};
use super::{committed_frames, committed_trace, index_path, write_atomic, DurableLog};
use crate::debug::trace;
use crate::eval::Obs;

// Every persistence step of the incremental append discipline, the full crash
// matrix from the fault-injection specification.
const APPEND_PHASE: [FaultPoint; 7] = [
    FaultPoint::Open,
    FaultPoint::WritePrefix,
    FaultPoint::WriteBody,
    FaultPoint::AppendLog,
    FaultPoint::Flush,
    FaultPoint::UpdateIndex,
    FaultPoint::Rename,
];

// The steps the atomic-snapshot discipline passes through (it neither appends nor
// keeps an index).
const SNAPSHOT_PHASE: [FaultPoint; 5] = [
    FaultPoint::Open,
    FaultPoint::WritePrefix,
    FaultPoint::WriteBody,
    FaultPoint::Flush,
    FaultPoint::Rename,
];

// A private temp directory per test, cleaned on drop.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("prism_durable_{}_{tag}_{n}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("temp dir");
        Self { path }
    }

    fn log(&self) -> PathBuf {
        self.path.join("run.replay")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn assert_injected(err: &io::Error, point: FaultPoint) {
    assert!(
        err.to_string().contains(INJECTED_MARKER),
        "{point:?}: expected an injected fault, got {err}"
    );
}

// A committed log built by appending `frames` cleanly.
fn seed(path: &Path, frames: &[Obs]) {
    let (mut log, existing) = DurableLog::open(path).expect("open fresh log");
    assert!(existing.is_empty(), "a fresh log has no committed frames");
    for f in frames {
        log.append(f).expect("clean append");
    }
}

// -- Gate 1 and 2: append recovers to the committed prefix ----------------------

// A crash at any of the seven append steps leaves the previous committed prefix
// intact and drops the torn tail; the retry commits the new observation. Restart
// yields the complete old state, then the complete new state, never a partial or
// torn read, and a torn frame is never decoded.
#[test]
fn append_faults_recover_to_committed_prefix() {
    let prefix = [Obs::Out, Obs::Int(7), Obs::Str("hello".into())];
    let next = Obs::Int(42);
    for point in APPEND_PHASE {
        let dir = TempDir::new("append-fault");
        let log_path = dir.log();
        seed(&log_path, &prefix);
        let committed_before = fs::read_to_string(&log_path).unwrap_or_default();

        // Crash while committing the next observation.
        let (mut log, before) = DurableLog::open(&log_path).expect("reopen");
        assert_eq!(before, prefix, "{point:?}: committed prefix loads");
        faults::arm(point);
        let err = log.append(&next).expect_err("the armed step fails");
        assert_injected(&err, point);
        drop(log);

        // Restart: exactly the old committed prefix, torn tail dropped, and the
        // physical log truncated back to the committed boundary.
        let (retry_log, recovered) = DurableLog::open(&log_path).expect("recover");
        assert_eq!(
            recovered, prefix,
            "{point:?}: restart yields the complete old state"
        );
        assert_eq!(
            fs::read_to_string(&log_path).unwrap_or_default(),
            committed_before,
            "{point:?}: the torn tail is physically truncated on recovery"
        );

        // The retry converges to the complete new state.
        let mut retry_log = retry_log;
        retry_log.append(&next).expect("retry commits");
        drop(retry_log);
        let mut want = prefix.to_vec();
        want.push(next.clone());
        assert_eq!(
            committed_frames(&log_path).unwrap(),
            want,
            "{point:?}: retry yields the complete new state"
        );
    }
}

// A genuinely torn frame body (a partial payload flushed to disk) is never read
// as a valid observation: recovery truncates it, and the committed frames hold
// only whole observations.
#[test]
fn torn_body_is_never_read_as_valid() {
    let dir = TempDir::new("torn-body");
    let log_path = dir.log();
    seed(&log_path, &[Obs::Int(1)]);
    let clean_len = fs::metadata(&log_path).unwrap().len();

    // A long payload so the half-written body is unmistakably torn.
    let mut log = DurableLog::open(&log_path).unwrap().0;
    faults::arm(FaultPoint::WriteBody);
    let err = log
        .append(&Obs::Str("a-long-observation-payload".into()))
        .expect_err("torn body fails");
    assert_injected(&err, FaultPoint::WriteBody);
    drop(log);

    // The torn bytes really reached disk before recovery.
    assert!(
        fs::metadata(&log_path).unwrap().len() > clean_len,
        "the partial body was flushed to the file"
    );

    // A read-only recovery drops the torn frame: only whole observations survive.
    assert_eq!(
        committed_frames(&log_path).unwrap(),
        vec![Obs::Int(1)],
        "the torn frame is dropped, only whole observations survive"
    );

    // Reopening for append truncates the torn tail physically, so the file is
    // back to exactly the committed prefix and the next append lands clean.
    let (_log, recovered) = DurableLog::open(&log_path).unwrap();
    assert_eq!(recovered, vec![Obs::Int(1)]);
    assert_eq!(fs::metadata(&log_path).unwrap().len(), clean_len);
}

// A committed length that outruns the log means committed bytes were lost: a hard
// error with a pointed diagnostic, never a silent short read.
#[test]
fn a_log_shorter_than_its_index_is_rejected() {
    let dir = TempDir::new("short-log");
    let log_path = dir.log();
    seed(&log_path, &[Obs::Int(1), Obs::Int(2)]);
    // Corrupt the log by dropping bytes without moving the index back.
    fs::write(&log_path, "I1:1").unwrap();
    let err = committed_frames(&log_path).expect_err("short log rejected");
    assert!(
        err.to_string().contains("committed observations were lost"),
        "expected a pointed short-log diagnostic, got {err}"
    );
}

// -- Gate 1: the atomic snapshot leaves the old or the new whole file -----------

// A crash at any step of the snapshot write leaves the previous file complete and
// readable; the retry replaces it atomically. Never a torn intermediate file.
#[test]
fn snapshot_faults_leave_old_or_new_whole_file() {
    let old = trace::encode(&[Obs::Int(1), Obs::Out]);
    let new = trace::encode(&[Obs::Int(2), Obs::Out, Obs::Int(3)]);
    for point in SNAPSHOT_PHASE {
        let dir = TempDir::new("snapshot-fault");
        let log_path = dir.log();
        write_atomic(&log_path, &old).expect("seed old");

        faults::arm(point);
        let err = write_atomic(&log_path, &new).expect_err("armed snapshot fails");
        assert_injected(&err, point);

        assert_eq!(
            fs::read_to_string(&log_path).unwrap(),
            old,
            "{point:?}: the old whole file survives the crash"
        );

        write_atomic(&log_path, &new).expect("retry");
        assert_eq!(
            fs::read_to_string(&log_path).unwrap(),
            new,
            "{point:?}: the retry lands the new whole file"
        );
    }
}

// -- Gates 3 and 4: durable resume is exactly-once and trace-preserving ---------

// One workflow step: an input observation yielding a pinned value, or an output
// with its text.
#[derive(Clone)]
enum Step {
    In(i64),
    Out(&'static str),
}

// The frame each step commits, so a test can predict the committed prefix at any
// crash point.
fn step_frame(step: &Step) -> Obs {
    match step {
        Step::In(v) => Obs::Int(*v),
        Step::Out(_) => Obs::Out,
    }
}

// Drive `script` against the durable log at `path`, mirroring `Replay.pr`'s
// `durable` handler: replay every already-committed observation with no real
// effect, then perform each new one. An input serves its committed frame or
// performs the pinned read and commits it; an output replays (drops) a committed
// boundary or commits the boundary and *then* emits, so a resumed run never
// re-emits an already-committed output. `crash` arms a fault just before the
// k-th new observation of this run, simulating a process death mid-persist.
fn drive(
    path: &Path,
    script: &[Step],
    emitted: &mut Vec<String>,
    crash: Option<(usize, FaultPoint)>,
) -> io::Result<()> {
    let (mut log, committed) = DurableLog::open(path)?;
    let mut cursor = 0;
    let mut live = 0;
    for step in script {
        if cursor < committed.len() {
            // Replay: the observation already reached disk, so serve or drop it.
            assert_eq!(
                committed[cursor],
                step_frame(step),
                "replayed trace matches the program"
            );
            cursor += 1;
            continue;
        }
        if let Some((k, point)) = crash {
            if k == live {
                faults::arm(point);
            }
        }
        match step {
            Step::In(v) => log.append(&Obs::Int(*v))?,
            Step::Out(text) => {
                log.append(&Obs::Out)?;
                emitted.push((*text).to_string());
            }
        }
        live += 1;
    }
    Ok(())
}

#[test]
fn durable_resume_is_exactly_once_and_trace_equals_uninterrupted() {
    let script = [
        Step::Out("start"),
        Step::In(10),
        Step::Out("middle"),
        Step::In(20),
        Step::Out("nearly"),
        Step::In(30),
        Step::Out("done"),
    ];

    // The uninterrupted reference: its emitted outputs and its committed trace.
    let ref_dir = TempDir::new("resume-ref");
    let ref_path = ref_dir.log();
    let mut ref_emitted = Vec::new();
    drive(&ref_path, &script, &mut ref_emitted, None).expect("uninterrupted run");
    let ref_frames = committed_frames(&ref_path).unwrap();
    assert_eq!(ref_emitted, ["start", "middle", "nearly", "done"]);

    // Crash at every observation index, at every persistence step, then resume.
    for point in APPEND_PHASE {
        for crash_at in 0..script.len() {
            let dir = TempDir::new("resume-crash");
            let path = dir.log();

            // Run 1 crashes while committing the crash_at-th observation.
            let mut emitted = Vec::new();
            let err = drive(&path, &script, &mut emitted, Some((crash_at, point)))
                .expect_err("the armed run crashes");
            assert_injected(&err, point);

            // Restart yields exactly the observations committed before the crash:
            // a complete old state, never a torn one.
            let recovered = committed_frames(&path).unwrap();
            let want_prefix: Vec<Obs> = script[..crash_at].iter().map(step_frame).collect();
            assert_eq!(
                recovered, want_prefix,
                "{point:?}@{crash_at}: restart is the complete committed prefix"
            );

            // Resume runs the whole script again; the committed prefix is replayed
            // with no real effect and the remainder is performed.
            drive(&path, &script, &mut emitted, None).expect("resume finishes");

            // Gate 4: the resumed run's observation trace equals the uninterrupted
            // run's, byte for byte.
            assert_eq!(
                committed_frames(&path).unwrap(),
                ref_frames,
                "{point:?}@{crash_at}: resumed trace equals the uninterrupted trace"
            );
            // Gate 3: every output is emitted exactly once across crash and resume,
            // never duplicated and (for a pre-commit crash) never lost.
            assert_eq!(
                emitted, ref_emitted,
                "{point:?}@{crash_at}: exactly-once emission across the crash"
            );
        }
    }
}

// -- Version compatibility fixture ----------------------------------------------

const FIXTURE_LOG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/replay/durable.replay"
);
const FIXTURE_IDX: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/replay/durable.replay.idx"
);

// The committed replay-log fixture and its `prism-replay-idx-v1` sidecar. Current
// reads current byte for byte, a future schema is refused, and a partial index
// recovers the committed prefix. Re-bless with PRISM_BLESS_REPLAY=1.
#[test]
fn idx_v1_compat_fixture() {
    let frames = [Obs::Out, Obs::Int(1), Obs::Out, Obs::Int(2)];
    let log_bytes = trace::encode(&frames);
    if std::env::var("PRISM_BLESS_REPLAY").is_ok() {
        fs::write(FIXTURE_LOG, &log_bytes).expect("write replay fixture");
        fs::write(FIXTURE_IDX, super::render_index(log_bytes.len() as u64))
            .expect("write idx fixture");
    }

    // current reads current: the golden bytes recover to the exact frames.
    let want_log = fs::read_to_string(FIXTURE_LOG)
        .expect("missing tests/fixtures/replay/durable.replay; bless with PRISM_BLESS_REPLAY=1");
    assert_eq!(want_log, log_bytes, "fixture log bytes drifted");
    assert_eq!(
        committed_frames(Path::new(FIXTURE_LOG)).unwrap(),
        frames,
        "fixture recovers to its committed frames"
    );
    assert_eq!(
        committed_trace(Path::new(FIXTURE_LOG)).unwrap(),
        want_log,
        "recovered trace round-trips the fixture bytes"
    );

    // A working copy for the negative and partial cases, so the committed fixture
    // stays pristine.
    let dir = TempDir::new("fixture");
    let log = dir.log();
    let idx = index_path(&log);
    fs::write(&log, &want_log).unwrap();

    // current rejects an unsupported schema with a pointed diagnostic.
    fs::write(&idx, format!("prism-replay-idx-v2\n{}\n", want_log.len())).unwrap();
    let err = committed_frames(&log).expect_err("future schema is refused");
    assert!(
        err.to_string().contains("foreign schema"),
        "expected a version diagnostic, got {err}"
    );

    // A partial committed length recovers only the committed prefix, never the
    // uncommitted tail.
    fs::write(&idx, super::render_index(7)).unwrap();
    assert_eq!(
        committed_frames(&log).unwrap(),
        vec![Obs::Out, Obs::Int(1)],
        "a partial index recovers the committed prefix"
    );
}
