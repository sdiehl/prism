//! End-to-end durable-resume driver: a running interpreter program persists each
//! observation to a crash-safe log and, after a mid-run crash, resumes byte for
//! byte by replaying the committed prefix and continuing live.
//!
//! The substrate's own fault matrix (`src/debug/durable/tests.rs`) proves the log
//! is crash-safe against a hand-written driver; this proves the *interpreter* is
//! wired to it correctly: the machine's observe sites replay the committed prefix
//! with no real IO, then append each new observation, and the resumed observation
//! trace equals an uninterrupted run's.
//!
//! Capabilities whose live value is a pure function of the (fixed) external world
//! are what make a resumed run comparable to a separate uninterrupted run: a file
//! read of an unchanged file yields the same bytes however many times it runs, so
//! the replayed prefix and the live tail agree with the reference. A process-local
//! generator (`rng_rand`) is deliberately not used here: replay serves its recorded
//! draws without advancing the generator, so its live tail is genuinely fresh, the
//! same semantics as `Replay.pr`'s `durable` handler but not comparable against a
//! distinct uninterrupted run.

use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use prism::debug::durable::committed_frames;
use prism::debug::trace;
use prism::eval::Obs;
use prism::{default_roots, durable_run_on, record_on_with_args, with_prelude, Config};

// A private temp directory per test, cleaned on drop.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "prism_durable_drv_{}_{tag}_{n}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("temp dir");
        Self { path }
    }

    fn join(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// A program that reads a fixed file three times and prints its contents each time,
// then returns the total length. Each read yields the same bytes, so the observed
// trace is identical whether the run is uninterrupted or crashed-then-resumed. The
// reads are `Str` frames and the prints are `Out` boundaries, interleaved, so crash
// points land on both sides of the replay/live boundary.
fn program(data_path: &Path) -> String {
    let p = data_path.display();
    with_prelude(&format!(
        "fn main() =\n  \
           let a = read_file(\"{p}\")\n  \
           print(a)\n  \
           let b = read_file(\"{p}\")\n  \
           print(b)\n  \
           let c = read_file(\"{p}\")\n  \
           print(c)\n  \
           str_len(a) + str_len(b) + str_len(c)\n"
    ))
}

// The reference `.replay` frames of an uninterrupted recording of the program, plus
// the byte-identical live output it streamed.
fn reference(src: &str, roots: &[prism::resolve::Root], cfg: &Config) -> (Vec<Obs>, Vec<u8>) {
    let mut out = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let (exit, encoded, _) =
        record_on_with_args(src, roots, &mut out, &mut input, cfg, Vec::new()).expect("record");
    assert_eq!(
        exit, None,
        "the reference program returns a value, not exit"
    );
    (
        trace::decode(&encoded).expect("decode reference trace"),
        out,
    )
}

#[test]
fn durable_resume_is_byte_identical_to_uninterrupted() {
    let dir = TempDir::new("resume");
    let data = dir.join("input.txt");
    // A payload with a ':' and a newline, so the persisted string frames exercise
    // the length-prefixed codec on a payload that contains the delimiter.
    fs::write(&data, "alpha:1\nbeta:22\n").expect("seed input file");

    let src = program(&data);
    let roots = default_roots(&dir.path);
    let cfg = Config::default();

    let (ref_frames, ref_out) = reference(&src, &roots, &cfg);
    let n = ref_frames.len();
    assert!(
        n >= 6,
        "program should produce several observations, got {n}"
    );

    // An uninterrupted durable run commits exactly the reference trace and streams
    // exactly the reference output: the durable handler is invisible except for the
    // log it leaves behind.
    {
        let log = dir.join("clean.replay");
        let mut out = Vec::new();
        let mut input = Cursor::new(Vec::new());
        let run = durable_run_on(
            &src,
            &roots,
            &mut out,
            &mut input,
            &cfg,
            Vec::new(),
            &log,
            None,
        )
        .expect("clean durable run");
        assert!(!run.halted, "an unbudgeted run finishes");
        assert_eq!(run.replayed, 0, "a fresh log replays nothing");
        assert_eq!(run.committed, n, "a clean run commits the whole trace");
        assert_eq!(run.exit, None);
        assert_eq!(
            committed_frames(&log).unwrap(),
            ref_frames,
            "clean == reference"
        );
        assert_eq!(out, ref_out, "clean output == reference output");
    }

    // Crash after every possible observation count, then resume, and prove the
    // resumed committed trace and the exactly-once output both equal the reference.
    for crash_at in 0..=n {
        let log = dir.join(&format!("crash_{crash_at}.replay"));

        // Run 1 stops after `crash_at` observations, committing exactly that prefix.
        let mut crashed_out = Vec::new();
        let mut input1 = Cursor::new(Vec::new());
        let run1 = durable_run_on(
            &src,
            &roots,
            &mut crashed_out,
            &mut input1,
            &cfg,
            Vec::new(),
            &log,
            Some(crash_at),
        )
        .expect("budgeted first run");
        assert_eq!(run1.replayed, 0, "the first run replays nothing");
        assert_eq!(
            run1.committed, crash_at,
            "{crash_at}: exactly the budgeted prefix is committed"
        );
        assert_eq!(
            run1.halted,
            crash_at < n,
            "{crash_at}: halted iff cut short"
        );
        assert_eq!(
            committed_frames(&log).unwrap(),
            ref_frames[..crash_at].to_vec(),
            "{crash_at}: the crash leaves the committed prefix"
        );

        // Run 2 resumes: it replays the committed prefix with no real IO, then
        // performs the remaining observations live.
        let mut resumed_out = Vec::new();
        let mut input2 = Cursor::new(Vec::new());
        let run2 = durable_run_on(
            &src,
            &roots,
            &mut resumed_out,
            &mut input2,
            &cfg,
            Vec::new(),
            &log,
            None,
        )
        .expect("resume run");
        assert!(!run2.halted, "{crash_at}: the resume finishes");
        assert_eq!(
            run2.replayed, crash_at,
            "{crash_at}: the resume replays exactly the committed prefix"
        );
        assert_eq!(
            run2.committed, n,
            "{crash_at}: the resume commits the whole trace"
        );
        assert_eq!(run2.exit, None);

        // Gate: the resumed committed trace equals the uninterrupted trace.
        assert_eq!(
            committed_frames(&log).unwrap(),
            ref_frames,
            "{crash_at}: resumed trace equals the uninterrupted trace"
        );

        // Gate: every output fires exactly once across the crash. A replayed prefix
        // output is dropped (never re-emitted), so the two runs' streamed output
        // concatenates to exactly one uninterrupted run's.
        let mut joined = crashed_out.clone();
        joined.extend_from_slice(&resumed_out);
        assert_eq!(
            joined, ref_out,
            "{crash_at}: outputs are exactly-once across the crash"
        );
    }
}

// A resume from an empty (never-created) log is just an ordinary full run: opening
// a missing log yields an empty committed prefix.
#[test]
fn durable_run_creates_a_fresh_log() {
    let dir = TempDir::new("fresh");
    let data = dir.join("input.txt");
    fs::write(&data, "payload").expect("seed input");
    let src = program(&data);
    let roots = default_roots(&dir.path);
    let cfg = Config::default();

    let log = dir.join("new.replay");
    assert!(!log.exists(), "log does not exist yet");
    let mut out = Vec::new();
    let mut input: Cursor<Vec<u8>> = Cursor::new(Vec::new());
    let run = durable_run_on(
        &src,
        &roots,
        &mut out,
        &mut input,
        &cfg,
        Vec::new(),
        &log,
        None,
    )
    .expect("fresh durable run");
    assert_eq!(run.replayed, 0);
    assert!(run.committed > 0, "a run with observations commits frames");
    assert!(log.exists(), "the log is created");
    // The committed trace round-trips and recovers cleanly.
    let _ = committed_frames(&log).expect("committed frames recover");
}
