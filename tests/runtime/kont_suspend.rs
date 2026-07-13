// The suspend/resume round-trip. Pausing a running program at a step
// budget, serializing the whole live continuation as a `kont` envelope, and
// resuming it from those bytes reproduces an uninterrupted run byte for byte, at
// the start and at every mid-computation point. Code identity is checked by the
// bundle digest, so a snapshot cannot resume against a different program.

use std::io::Cursor;
use std::path::Path;

use prism::eval::kont::{decode_kont, encode_kont};
use prism::eval::{resume_kont_observed, run_observed_with_args, run_suspending, Checkpoint};
use prism::resolve::default_roots;
use prism::{
    core_of, interpret_io_on, resume_on, suspend_line_cuts, suspend_on, with_prelude, Config,
    SuspendResult,
};

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

const TELEPORT: &str = include_str!("../../examples/teleport.pr");

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
    let mut observed_out = Vec::new();
    let mut observed_input = Cursor::new(Vec::new());
    let uninterrupted_trace =
        run_observed_with_args(&core, &mut observed_out, &mut observed_input, Vec::new())
            .observations;
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
                let resumed = resume_kont_observed(&core, kont2, &mut suffix, &mut input2);
                assert_eq!(
                    resumed.observations, uninterrupted_trace,
                    "suspend/resume preserves the complete observation trace at budget {budget}"
                );
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
    let SuspendResult::Suspended { bytes, .. } =
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
    let SuspendResult::Suspended { bytes, .. } =
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
        msg.contains("execution-identity mismatch"),
        "the refusal names the execution-identity mismatch: {msg}"
    );
}

// A snapshot is bound to the scheduler policy it was taken under: resuming it
// under a different policy is refused before a step runs, because a scheduler
// change reorders concurrent execution and the suffix need not equal the
// uninterrupted run. Checks that a cooperative-FIFO snapshot cannot resume
// under LIFO.
#[test]
fn resume_under_a_different_scheduler_is_refused() {
    let full = with_prelude(COUNTER);
    let mut cooperative = cfg();
    cooperative.scheduler = prism::Scheduler::Cooperative;

    let mut prefix: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let SuspendResult::Suspended { bytes, .. } =
        suspend_on(&full, &roots(), &mut prefix, &mut input, 20, &cooperative).expect("suspend")
    else {
        panic!("budget 20 suspends mid-run");
    };

    let mut lifo = cfg();
    lifo.scheduler = prism::Scheduler::Lifo;
    let mut out: Vec<u8> = Vec::new();
    let mut input2 = Cursor::new(Vec::new());
    let err = resume_on(&full, &roots(), &bytes, &mut out, &mut input2, &lifo)
        .expect_err("resuming under a different scheduler policy is refused");
    assert!(
        err.to_string().contains("execution-identity mismatch"),
        "the refusal names the execution-identity mismatch: {err}"
    );
}

#[test]
fn teleport_demo_resume_matches_uninterrupted_run_and_refuses_tamper() {
    let full = with_prelude(TELEPORT);
    let want = uninterrupted(&full);
    assert!(
        want.contains("step 10"),
        "the teleport fixture prints the full run"
    );

    let cuts = suspend_line_cuts(&full, &roots(), &cfg()).expect("line cuts");
    assert!(
        cuts.len() > 2,
        "the teleport fixture has several interior line boundaries"
    );
    let cut = cuts[cuts.len() / 2];

    let mut prefix: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let SuspendResult::Suspended { bytes, .. } =
        suspend_on(&full, &roots(), &mut prefix, &mut input, cut, &cfg()).expect("suspend")
    else {
        panic!("interior line cut suspends the teleport demo");
    };

    let mut suffix: Vec<u8> = Vec::new();
    let mut input2 = Cursor::new(Vec::new());
    resume_on(&full, &roots(), &bytes, &mut suffix, &mut input2, &cfg()).expect("resume");
    let resumed = [prefix.as_slice(), suffix.as_slice()].concat();
    assert_eq!(
        String::from_utf8(resumed).expect("utf8"),
        want,
        "sender prefix followed by receiver suffix equals an uninterrupted run"
    );

    let mut tampered = bytes.clone();
    let tampered_index = tampered.len() / 2;
    tampered[tampered_index] ^= 0x01;
    let mut refused_out: Vec<u8> = Vec::new();
    let mut input3 = Cursor::new(Vec::new());
    let err = resume_on(
        &full,
        &roots(),
        &tampered,
        &mut refused_out,
        &mut input3,
        &cfg(),
    )
    .expect_err("tampered envelope is refused");
    let msg = err.to_string();
    assert!(
        msg.contains("malformed snapshot") || msg.contains("kont") || msg.contains("checksum"),
        "the refusal names the envelope problem: {msg}"
    );
    assert!(
        refused_out.is_empty(),
        "tamper is refused before any receiver output is emitted"
    );
}

// The step ruler marks every observation with the machine step it fired at, in
// strictly increasing step order, and its previews carry the printed text. The
// indices are pure functions of the source, so the ruler is how a suspend
// budget is picked deliberately instead of guessed.
#[test]
fn step_ruler_marks_every_observation_in_step_order() {
    let full = with_prelude(COUNTER);
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let ruler =
        prism::step_ruler_on(&full, &roots(), &mut out, &mut input, &cfg()).expect("ruled run");

    assert_eq!(ruler.format, prism::STEP_RULER_FORMAT);
    // Eight `println`s, each a print plus a newline boundary.
    assert_eq!(ruler.rows.len(), 16, "one mark per output boundary");
    assert!(
        ruler.rows.windows(2).all(|w| w[0].step < w[1].step),
        "marks are strictly increasing on the step clock"
    );
    let last = ruler.rows.last().expect("nonempty");
    assert!(
        ruler.total_steps >= last.step,
        "the total covers every mark"
    );
    let prints: Vec<&str> = ruler
        .rows
        .iter()
        .filter(|r| r.op == "Console.print")
        .map(|r| r.preview.as_str())
        .collect();
    assert_eq!(prints[0], "0", "the first print's preview is its text");
    assert_eq!(prints[7], "49", "the last print's preview is its text");
    // The ruled run is an ordinary run: the transcript is untouched.
    assert_eq!(String::from_utf8(out).expect("utf8"), uninterrupted(&full));
}

// A suspend reports where it fell on the observation timeline, and that report
// agrees with the full ruler: the observations before the cut are exactly the
// ruler's marks at or before the budget.
#[test]
fn suspend_cut_report_agrees_with_the_ruler() {
    let full = with_prelude(COUNTER);
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let ruler =
        prism::step_ruler_on(&full, &roots(), &mut out, &mut input, &cfg()).expect("ruled run");
    let budget = ruler.rows[4].step; // mid-run, right on an observation's step

    let mut prefix: Vec<u8> = Vec::new();
    let mut input2 = Cursor::new(Vec::new());
    let SuspendResult::Suspended { cut, .. } =
        suspend_on(&full, &roots(), &mut prefix, &mut input2, budget, &cfg()).expect("suspend")
    else {
        panic!("a mid-run budget suspends");
    };
    // A mark labels the step during whose transition it fired, and `--at N`
    // executes steps 1..=N before pausing, so the mark AT the budget step has
    // already fired by the cut.
    let before: Vec<_> = ruler.rows.iter().filter(|r| r.step <= budget).collect();
    assert_eq!(cut.observations, before.len());
    let last = cut.last.expect("observations before the cut");
    let want = before.last().expect("nonempty prefix");
    assert_eq!((last.step, last.op.as_str()), (want.step, want.op.as_str()));

    // A budget of 0 pauses before anything fires: an empty timeline, honestly.
    let mut none_out: Vec<u8> = Vec::new();
    let mut input3 = Cursor::new(Vec::new());
    let SuspendResult::Suspended { cut, .. } =
        suspend_on(&full, &roots(), &mut none_out, &mut input3, 0, &cfg()).expect("suspend at 0")
    else {
        panic!("budget 0 suspends before the first step");
    };
    assert_eq!(cut.observations, 0);
    assert!(cut.last.is_none());
}
