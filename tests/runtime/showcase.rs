// Showcase byproducts of the content-addressed store: the behavior diff, the
// `.replay` record/replay round trip, the durable exactly-once resume, and the
// reverse-step debugger. Each checks the core guarantee end to end.

use prism::debug::trace;
use prism::resolve::default_roots;
use prism::{debug_on, diff_on, interpret_io_on, record_on, replay_on, with_prelude, Config};
use std::io::Cursor;
use std::path::{Path, PathBuf};

fn cfg() -> Config {
    Config::from_env()
}

fn roots() -> Vec<prism::resolve::Root> {
    default_roots(Path::new("."))
}

fn diff(old: &str, new: &str) -> String {
    diff_on(&with_prelude(old), &with_prelude(new), &roots(), &cfg()).expect("diff")
}

// The corpus `collatz` program: two `var`/`while` loops over a shared step.
const COLLATZ: &str = "\
fn collatz_step(n) =
  if even(n) then
    n / 2
  else
    3 * n + 1

fn collatz_len(start : Int) : Int =
  var n := start
  var acc := 0
  while n /= 1 do
    n := collatz_step(n)
    acc += 1
  acc + 1

fn collatz_max(start : Int) : Int =
  var n := start
  var peak := start
  while n /= 1 do
    peak := max(n, peak)
    n := collatz_step(n)
  peak

fn main() =
  println(collatz_len(27))
  println(collatz_max(27))
";

// A mechanical refactor of COLLATZ: functions reordered (both `var` loops swapped
// relative to each other), every local and parameter renamed, comments rewritten,
// whitespace changed. Nothing about behavior moves.
const COLLATZ_REFACTOR: &str = "\
-- reordered, renamed, reformatted; same behavior
fn main() =
  println(collatz_len(27))
  println(collatz_max(27))

fn collatz_max(origin : Int) : Int =
  var cur := origin
  var peak := origin
  while cur /= 1 do
    peak := max(cur, peak)
    cur := collatz_step(cur)
  peak

fn collatz_len(origin : Int) : Int =
  var cur := origin
  var count := 0
  while cur /= 1 do
    cur := collatz_step(cur)
    count += 1
  count + 1

fn collatz_step(m) =
  if even(m) then
    m / 2
  else
    3 * m + 1
";

// A real logic edit: the odd-case constant in the shared `collatz_step` moves.
const COLLATZ_EDIT: &str = "\
fn collatz_step(n) =
  if even(n) then
    n / 2
  else
    3 * n + 7

fn collatz_len(start : Int) : Int =
  var n := start
  var acc := 0
  while n /= 1 do
    n := collatz_step(n)
    acc += 1
  acc + 1

fn collatz_max(start : Int) : Int =
  var n := start
  var peak := start
  while n /= 1 do
    peak := max(n, peak)
    n := collatz_step(n)
  peak

fn main() =
  println(collatz_len(27))
  println(collatz_max(27))
";

#[test]
fn pure_refactor_diffs_to_zero() {
    // The flagship: rename locals and params, reorder the two `var` loops, rewrite
    // comments, reformat. Every content hash holds, so the diff is exactly zero.
    let out = diff(COLLATZ, COLLATZ_REFACTOR);
    assert_eq!(
        out,
        "diff: 0 changed, 0 added, 0 removed, 4 unchanged\n\
         text-only: 3 respelled, behavior held (collatz_len, collatz_max, collatz_step)\n\
         cone: 0 affected\n",
        "a pure refactor is zero behavioral changes with the respellings named"
    );
}

// The same two comparisons through the structured surface: the JSON carries the
// behavioral/text-only split, is deterministic, and a logic edit lands in
// `behavioral` with its dependents in the cone.
#[test]
fn source_diff_json_classifies_behavior_and_text() {
    let d = prism::source_diff_on(
        &with_prelude(COLLATZ),
        &with_prelude(COLLATZ_REFACTOR),
        &roots(),
        &cfg(),
    )
    .expect("diff");
    assert!(d.behavioral.is_empty() && d.added.is_empty() && d.removed.is_empty());
    let respelled: Vec<&str> = d.text_only.iter().map(|t| t.name.as_str()).collect();
    assert_eq!(respelled, ["collatz_len", "collatz_max", "collatz_step"]);
    let once = serde_json::to_string(&d).unwrap();
    let d2 = prism::source_diff_on(
        &with_prelude(COLLATZ),
        &with_prelude(COLLATZ_REFACTOR),
        &roots(),
        &cfg(),
    )
    .expect("diff");
    assert_eq!(once, serde_json::to_string(&d2).unwrap(), "deterministic");

    let e = prism::source_diff_on(
        &with_prelude(COLLATZ),
        &with_prelude(COLLATZ_EDIT),
        &roots(),
        &cfg(),
    )
    .expect("diff");
    assert!(
        e.behavioral.iter().any(|c| c.name == "collatz_step"),
        "the logic edit is behavioral: {e:?}"
    );
    assert!(
        e.dependents.iter().any(|n| n == "collatz_len"),
        "dependents ride the cone: {e:?}"
    );
}

#[test]
fn logic_edit_reports_the_changed_def_and_its_exact_cone() {
    // Editing the shared `collatz_step` moves exactly one definition's own content;
    // its dependents cone is precisely the two callers plus `main`.
    let out = diff(COLLATZ, COLLATZ_EDIT);
    let mut lines = out.lines();
    assert_eq!(
        lines.next().unwrap(),
        "diff: 1 changed, 0 added, 0 removed, 0 unchanged"
    );
    // The one changed line: `~ collatz_step  <old16> -> <new16>`.
    let changed = lines.next().unwrap();
    assert!(
        changed.starts_with("  ~ collatz_step  "),
        "changed line was {changed:?}"
    );
    let hashes: Vec<&str> = changed
        .trim_start()
        .trim_start_matches("~ collatz_step  ")
        .split(" -> ")
        .collect();
    assert_eq!(hashes.len(), 2, "old -> new abbreviated hashes");
    assert!(
        hashes[0] != hashes[1]
            && hashes[0].len() == 16
            && hashes
                .iter()
                .all(|h| h.bytes().all(|b| b.is_ascii_hexdigit())),
        "two distinct 16-hex behavior hashes, got {hashes:?}"
    );
    assert_eq!(
        lines.next().unwrap(),
        "cone: 3 affected (collatz_len, collatz_max, main)"
    );
    assert!(lines.next().is_none(), "no trailing output");
}

// Record a program against a fixed input, then replay it with no input, asserting
// the transcript is reproduced byte for byte.
const GREET: &str = "\
fn main() =
  println(\"name?\")
  let who = read_line()
  println(\"hi {who}\")
  println(\"n={mod(rand(), 100)}\")
";

#[test]
fn replay_reproduces_the_recorded_run_byte_for_byte() {
    let full = with_prelude(GREET);
    // Record against the input "Ada".
    let mut rec_out: Vec<u8> = Vec::new();
    let mut rec_in = Cursor::new(b"Ada\n".to_vec());
    let (_exit, trace_str, n_obs) =
        record_on(&full, &roots(), &mut rec_out, &mut rec_in, &cfg()).expect("record");
    assert!(n_obs > 0, "the run made observations");

    // Replay with NO input; the trace must serve every read.
    let mut replay_out: Vec<u8> = Vec::new();
    replay_on(&full, &roots(), &mut replay_out, &trace_str, &cfg()).expect("replay");

    assert_eq!(
        replay_out, rec_out,
        "replay output must be byte-identical to the recorded run"
    );
    // And the trace round-trips through the codec.
    assert_eq!(
        trace::encode(&trace::decode(&trace_str).unwrap()),
        trace_str
    );
}

#[test]
fn debugger_steps_forward_and_back_over_the_trace() {
    let full = with_prelude(GREET);
    // Record a trace to step through.
    let mut rec_out: Vec<u8> = Vec::new();
    let mut rec_in = Cursor::new(b"Ada\n".to_vec());
    let (_e, trace_str, n_obs) =
        record_on(&full, &roots(), &mut rec_out, &mut rec_in, &cfg()).expect("record");

    // Step forward three observations, print state, step back once, quit.
    let mut cmds = Cursor::new(b"n\nn\nn\nb\nq\n".to_vec());
    let mut ui: Vec<u8> = Vec::new();
    debug_on(&full, &roots(), &trace_str, &mut cmds, &mut ui, &cfg()).expect("debug");
    let transcript = String::from_utf8(ui).unwrap();

    // The banner reports how many observations loaded, and stepping shows the
    // observation index climbing then falling by one (the honest reverse step).
    assert!(
        transcript.contains(&format!("loaded {n_obs} observations")),
        "banner names the trace length; transcript:\n{transcript}"
    );
    assert!(transcript.contains("[0/"), "starts before any observation");
    assert!(
        transcript.contains("[3/"),
        "reaches observation 3 going forward"
    );
    // The last forward step reads the recorded line; stepping back returns to 2.
    assert!(
        transcript.contains("read \"Ada\""),
        "the string observation is shown by tag and payload"
    );
    let last_status = transcript
        .lines()
        .filter_map(|l| l.rsplit("(debug) ").next())
        .rfind(|l| l.starts_with('['))
        .unwrap_or("");
    assert!(
        last_status.starts_with("[2/"),
        "stepping back lands on observation 2; last status was {last_status:?}"
    );
}

// A durable workflow that reads a config once, draws three randoms, and prints a
// line per step, crashing after the `stop`-th draw when `stop >= 0`. The log path
// is baked in so a test can point it at a private temp file; the crash/resume
// shape mirrors `examples/durable.pr`.
fn durable_program(log: &str, cfg_path: &str, stop: i64) -> String {
    format!(
        "import Replay (..)\n\
         fn draw(total, stop, done, acc) =\n\
        \x20 if done > total then\n\
        \x20   acc\n\
        \x20 else\n\
        \x20   let r = rng_rand()\n\
        \x20   let acc2 = acc + r\n\
        \x20   if stop >= 0 && done >= stop then\n\
        \x20     error(2)\n\
        \x20   println(\"step {{done}}\")\n\
        \x20   draw(total, stop, done + 1, acc2)\n\
         fn flow(total, stop, u) =\n\
        \x20 let c = read_file(\"{cfg_path}\")\n\
        \x20 println(\"cfg {{str_len(c)}}\")\n\
        \x20 draw(total, stop, 1, 0)\n\
         fn main() =\n\
        \x20 write_file(\"{cfg_path}\", \"abc\")\n\
        \x20 let resuming = prim_file_exists(\"{log}\") && str_len(prim_read_file(\"{log}\")) > 0\n\
        \x20 if resuming then\n\
        \x20   durable(\"{log}\", \\(u) -> flow(3, 0 - 1, u))\n\
        \x20   ()\n\
        \x20 else\n\
        \x20   durable(\"{log}\", \\(u) -> flow(3, {stop}, u))\n\
        \x20   ()\n"
    )
}

fn temp_path(stem: &str) -> PathBuf {
    std::env::temp_dir().join(format!("prism_showcase_{}_{stem}", std::process::id()))
}

fn run_capture(src: &str) -> (String, bool) {
    let full = with_prelude(src);
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let res = interpret_io_on(&full, &roots(), &mut out, &mut input, &cfg());
    (String::from_utf8(out).unwrap(), res.is_err())
}

#[test]
fn durable_resume_is_exactly_once_across_a_crash() {
    let log = temp_path("durable.log");
    let cfg_path = temp_path("durable.cfg");
    let _ = std::fs::remove_file(&log);
    let _ = std::fs::remove_file(&cfg_path);
    let log_s = log.to_string_lossy();
    let cfg_s = cfg_path.to_string_lossy();

    // Run 1: crashes after the 2nd draw (before printing step 2's successor).
    let prog1 = durable_program(&log_s, &cfg_s, 2);
    let (out1, crashed) = run_capture(&prog1);
    assert!(crashed, "run 1 crashes at the stop step");

    // Run 2: the log exists, so main takes the resume branch (which draws with no
    // crash) and finishes. Its fresh branch is dead here, so its `stop` (9, past
    // the last step) only needs to parse.
    let prog2 = durable_program(&log_s, &cfg_s, 9);
    let (out2, errored) = run_capture(&prog2);
    assert!(!errored, "run 2 finishes cleanly");

    // The concatenation of the two runs prints each step exactly once: no output
    // is lost at the crash and none is duplicated on resume.
    let combined = format!("{out1}{out2}");
    assert_eq!(combined.matches("cfg 3").count(), 1, "config line once");
    for step in 1..=3 {
        assert_eq!(
            combined.matches(&format!("step {step}")).count(),
            1,
            "step {step} printed exactly once across crash+resume; combined was:\n{combined}"
        );
    }

    // The persisted log is a `.replay` trace in the shared frame format: it decodes
    // and round-trips through the Rust codec, proving cross-language agreement with
    // `Replay.pr`'s own serialization.
    let log_bytes = std::fs::read_to_string(&log).expect("durable log written");
    let frames = trace::decode(&log_bytes).expect("durable log is a valid .replay trace");
    assert_eq!(trace::encode(&frames), log_bytes, "log round-trips");

    let _ = std::fs::remove_file(&log);
    let _ = std::fs::remove_file(&cfg_path);
}

// A deterministic program (no input) that exercises `var`/`while` so the native
// backend and the interpreter both have real work to agree on.
const ATTEST_PROG: &str = "\
fn collatz_len(start : Int) : Int =
  var n := start
  var acc := 0
  while n /= 1 do
    n := if even(n) then n / 2 else 3 * n + 1
    acc += 1
  acc + 1

fn main() =
  println(\"attest me\")
  println(collatz_len(27))
";

#[test]
fn attest_emits_the_green_identical_line() {
    // The attestation builds a native binary; without a C compiler it is
    // meaningless, so skip rather than fail vacuously (mirrors the parity oracle).
    if !crate::support::have(&crate::support::cc()) {
        eprintln!("skipping attest test: no C compiler (set PRISM_CC)");
        return;
    }
    let out = prism::attest_on(&with_prelude(ATTEST_PROG), &roots(), &cfg()).expect("attest");
    let first = out.lines().next().unwrap();
    assert!(
        first.starts_with("attested: ") && first.contains(" identical across LLVM, "),
        "attest line was {first:?}"
    );
    // The identity is the 64-hex whole-program namespace root.
    let root = first
        .trim_start_matches("attested: ")
        .split(' ')
        .next()
        .unwrap();
    assert!(
        root.len() == 64 && root.bytes().all(|b| b.is_ascii_hexdigit()),
        "root was {root:?}"
    );
}

// -- committed goldens for the diff surface -------------------------------------

// The three text shapes and the JSON projection, stored as snapshots so any
// change to the diff's wording, ordering, or serialization is a reviewed diff
// against a committed golden rather than a silent drift.
fn assert_showcase_snapshot(name: &str, value: impl AsRef<str>) {
    insta::with_settings!({
        snapshot_path => "../snapshots",
        prepend_module_to_snapshot => false,
    }, {
        insta::assert_snapshot!(format!("showcase__{name}"), value.as_ref());
    });
}

#[test]
fn diff_text_refactor_golden() {
    assert_showcase_snapshot("diff_text_refactor", diff(COLLATZ, COLLATZ_REFACTOR));
}

#[test]
fn diff_text_edit_golden() {
    assert_showcase_snapshot("diff_text_edit", diff(COLLATZ, COLLATZ_EDIT));
}

#[test]
fn diff_text_add_remove_golden() {
    let old = "fn keep(x : Int) : Int = x + 1\n\nfn gone(x : Int) : Int = x * 2\n\nfn main() : Int = keep(1) + gone(2)\n";
    let new = "fn keep(x : Int) : Int = x + 1\n\nfn fresh(x : Int) : Int = x * 3\n\nfn main() : Int = keep(1) + fresh(2)\n";
    assert_showcase_snapshot("diff_text_add_remove", diff(old, new));
}

#[test]
fn diff_json_edit_golden() {
    let d = prism::source_diff_on(
        &with_prelude(COLLATZ),
        &with_prelude(COLLATZ_EDIT),
        &roots(),
        &cfg(),
    )
    .expect("diff");
    assert_showcase_snapshot(
        "diff_json_edit",
        serde_json::to_string_pretty(&d).expect("serialize"),
    );
}
