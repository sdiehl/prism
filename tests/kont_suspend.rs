// The suspend/resume round-trip. Pausing a running program at a step
// budget, serializing the whole live continuation as a `kont` envelope, and
// resuming it from those bytes reproduces an uninterrupted run byte for byte, at
// the start and at every mid-computation point. Code identity is checked by the
// bundle digest, so a snapshot cannot resume against a different program.

mod common;

use std::io::Cursor;
use std::path::Path;

use prism::eval::kont::{decode_kont, encode_kont};
use prism::eval::{resume_kont, run_suspending, Checkpoint};
use prism::resolve::default_roots;
use prism::{core_of, interpret_io_on, resume_on, suspend_on, with_prelude, Config, SuspendResult};

fn cfg() -> Config {
    Config::from_env()
}

fn roots() -> Vec<prism::resolve::Root> {
    default_roots(Path::new("."))
}

// A recursive printer: many machine steps and many output boundaries, so a step
// budget can pause the machine between, before, and after any of them.
const COUNTER: &str = r"
fn go(i, n) =
  if i >= n then
    ()
  else
    println(show_int(i * i))
    go(i + 1, n)

fn main() = go(0, 8)
";

fn uninterrupted(full: &str) -> String {
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    interpret_io_on(full, &roots(), &mut out, &mut input, &cfg()).expect("uninterrupted run");
    String::from_utf8(out).expect("utf8")
}

#[test]
fn suspend_and_resume_reproduces_output_at_every_cut() {
    // Compile once and drive the interpreter directly (recompiling per budget is
    // needless here), but still round-trip every snapshot through the `kont`
    // codec's bytes so this exercises encode + decode at every cut, not just the
    // in-memory continuation.
    let core = core_of(COUNTER).expect("compile");
    let want = uninterrupted(&with_prelude(COUNTER));
    assert!(!want.is_empty(), "the program prints");

    let mut saw_true_midpoint = false;
    // A dense sweep over every machine step from before the first through past the
    // last, so the run is cut at each of its many transitions.
    for budget in 0..600 {
        let mut prefix: Vec<u8> = Vec::new();
        let mut input = Cursor::new(Vec::new());
        let outcome = run_suspending(&core, "bundle".into(), budget, &mut prefix, &mut input)
            .expect("suspend");
        let prefix = String::from_utf8(prefix).unwrap();
        match outcome {
            Checkpoint::Done(_) => {
                assert_eq!(
                    prefix, want,
                    "a completed run at budget {budget} equals the uninterrupted run"
                );
            }
            Checkpoint::Suspended(kont) => {
                // encode -> bytes -> decode, so the resumed continuation is the one
                // reconstructed from the wire, not the live one.
                let bytes = encode_kont(&kont).expect("encode");
                let kont2 = decode_kont(&bytes).expect("decode");
                let mut suffix: Vec<u8> = Vec::new();
                let mut input2 = Cursor::new(Vec::new());
                resume_kont(&core, kont2, &mut suffix, &mut input2).expect("resume");
                let suffix = String::from_utf8(suffix).unwrap();
                assert_eq!(
                    format!("{prefix}{suffix}"),
                    want,
                    "prefix++suffix equals the uninterrupted run at budget {budget}"
                );
                if !prefix.is_empty() && !suffix.is_empty() {
                    saw_true_midpoint = true;
                }
            }
        }
    }
    assert!(
        saw_true_midpoint,
        "at least one budget suspended mid-computation (non-empty prefix and suffix)"
    );
}

#[test]
fn suspend_at_start_resumes_to_the_whole_run() {
    let full = with_prelude(COUNTER);
    let want = uninterrupted(&full);

    let mut prefix: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let SuspendResult::Suspended(bytes) =
        suspend_on(&full, &roots(), &mut prefix, &mut input, 0, &cfg()).expect("suspend at 0")
    else {
        panic!("budget 0 suspends before the first step");
    };
    assert!(prefix.is_empty(), "nothing runs before the first step");

    let mut suffix: Vec<u8> = Vec::new();
    let mut input2 = Cursor::new(Vec::new());
    resume_on(&full, &roots(), &bytes, &mut suffix, &mut input2, &cfg())
        .expect("resume from start");
    assert_eq!(String::from_utf8(suffix).unwrap(), want);
}

#[test]
fn resume_against_a_different_program_is_refused_by_hash() {
    let full = with_prelude(COUNTER);

    // Suspend somewhere in the middle.
    let mut prefix: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let SuspendResult::Suspended(bytes) =
        suspend_on(&full, &roots(), &mut prefix, &mut input, 20, &cfg()).expect("suspend")
    else {
        panic!("budget 20 suspends mid-run");
    };

    // A different program: same shape, different constant, so a different bundle.
    let other = with_prelude(&COUNTER.replace("go(0, 8)", "go(0, 9)"));
    let mut out: Vec<u8> = Vec::new();
    let mut input2 = Cursor::new(Vec::new());
    let err = resume_on(&other, &roots(), &bytes, &mut out, &mut input2, &cfg())
        .expect_err("resuming against a different program is refused");
    let msg = err.to_string();
    assert!(
        msg.contains("code-identity mismatch"),
        "the refusal names the code-identity mismatch: {msg}"
    );
}
