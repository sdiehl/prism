//! Incremental-computation (`Incr`) behavior gates.
//!
//! The leaderboard flagship must reproduce the spec's console byte-for-byte
//! (the recompute lines and the early-cutoff moment are the demo), and the
//! differential oracle must report that incremental evaluation equals
//! from-scratch evaluation. Interpreter-vs-native parity for both `.pr` files is
//! covered by the parity corpus (both live under the scanned directories).

use prism::{default_roots, interpret_io_on, with_prelude, Config, Root};
use std::fs;
use std::io::Cursor;
use std::path::Path;

fn run(rel: &str) -> String {
    let src = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)).unwrap();
    prism::interpret(&prism::with_prelude(&src)).unwrap().term
}

fn roots() -> Vec<Root> {
    default_roots(Path::new("."))
}

/// Run `src` against the real filesystem (durable snapshots write and read a
/// file), capturing stdout and whether the run errored. Mirrors the showcase
/// durable harness.
fn run_io(src: &str) -> (String, bool) {
    let full = with_prelude(src);
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let res = interpret_io_on(&full, &roots(), &mut out, &mut input, &Config::from_env());
    (String::from_utf8(out).unwrap(), res.is_err())
}

// A durable program computing `get(a) + 40` with `a = 2` (so `42`), tagged `cc`,
// snapshotting to `snap`. Used to prove every kind of bad snapshot cold-starts.
fn cc_program(snap: &str) -> String {
    format!(
        r#"import Incr (..)

fn main() =
  let r = run_incr_durable("{snap}", "cc") fn
    let a = input(2)
    let m = memo(\() -> get(a) + 40)
    show_int(get(m))
  println(r)
"#
    )
}

// An input-dependent-creation program: `base` is a prefix memo (persisted),
// `extra` is created only after the first `get` closes the prefix (dynamic,
// scratch-only). Prints `get(extra) + get(base)` = 100 + 11 = 111.
fn adversarial_program(snap: &str) -> String {
    format!(
        r#"import Incr (..)

fn main() =
  let r = run_incr_durable("{snap}", "adv") fn
    let a = input(1)
    let base = memo(\() -> get(a) + 10)
    let hot = get(base)
    let extra =
      if hot > 5 then
        memo(\() -> get(a) * 100)
      else
        memo(\() -> get(a) * 7)
    show_int(get(extra) + hot)
  println(r)
"#
    )
}

// The store-substrate twin of `cc_program`: the same `get(a) + 40 = 42` durable
// computation, but persisted onto the content-addressed store rooted at `root`
// (tag `cc`) via `run_incr_store` rather than a snapshot file.
fn store_program(root: &str) -> String {
    format!(
        r#"import Incr (..)

fn main() =
  let r = run_incr_store("{root}", "cc") fn
    let a = input(2)
    let m = memo(\() -> get(a) + 40)
    show_int(get(m))
  println(r)
"#
    )
}

// Every regular file under `dir`, recursively. Used to reach the one anonymous
// object a pure durable run writes so a test can tamper or drop it.
fn files_under(dir: &Path) -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                out.extend(files_under(&p));
            } else {
                out.push(p);
            }
        }
    }
    out
}

// A warm run reusing the store-backed snapshot prints byte-for-byte what the cold
// run printed: the store bridge preserves the durable north-star property (the
// persisted memo table changes cost, never output), and a second store commit of
// an unchanged snapshot writes no new object.
#[test]
fn store_warm_output_matches_cold() {
    let root = format!("target/incr_store_{}", std::process::id());
    let _ = fs::remove_dir_all(&root);
    let prog = store_program(&root);

    let (cold, cold_err) = run_io(&prog);
    assert!(!cold_err, "cold run finishes cleanly");
    assert!(cold.contains("42"), "cold run computes 42, got {cold:?}");

    let objects = Path::new(&root).join("objects");
    let before = files_under(&objects).len();
    assert!(before >= 1, "the cold run writes at least one store object");

    let (warm, warm_err) = run_io(&prog);
    assert!(!warm_err, "warm run finishes cleanly");
    assert_eq!(cold, warm, "warm output is byte-identical to cold");
    assert_eq!(
        files_under(&objects).len(),
        before,
        "an unchanged snapshot re-commits to the same object, writing none"
    );
    let _ = fs::remove_dir_all(&root);
}

// A store entry that is dropped (the whole store removed) or tampered (one object
// byte bumped, so it no longer hashes to its ref) is a silent cold start: the
// program still computes 42, never errors, never serves a corrupted value. The
// content-addressing is what turns tampering into a cold start.
#[test]
fn store_dropped_or_corrupt_entry_cold_starts() {
    let root = format!("target/incr_store_bad_{}", std::process::id());
    let prog = store_program(&root);

    // Dropped: no store at all cold-starts to 42.
    let _ = fs::remove_dir_all(&root);
    let (dropped, dropped_err) = run_io(&prog);
    assert!(
        !dropped_err && dropped.contains("42"),
        "missing store cold-starts to 42, got {dropped:?}"
    );

    // Populate, then tamper the single anonymous object: flip a byte so its
    // content hash no longer matches the ref.
    let _ = fs::remove_dir_all(&root);
    run_io(&prog);
    let objects = Path::new(&root).join("objects");
    let obj = files_under(&objects)
        .into_iter()
        .next()
        .expect("a store object exists after a run");
    let mut bytes = fs::read(&obj).unwrap();
    let last = bytes.len() - 1;
    bytes[last] = bytes[last].wrapping_add(1);
    fs::write(&obj, &bytes).unwrap();

    let (tampered, tampered_err) = run_io(&prog);
    assert!(
        !tampered_err && tampered.contains("42"),
        "tampered object cold-starts to 42, got {tampered:?}"
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn leaderboard_matches_spec_output() {
    let out = run("examples/leaderboard.pr");
    let expected = "\
== opening scores ==
  recompute: total
  recompute: banner
  recompute: champion
  recompute: ranking
total=15  banner=trinity is winning!

== neo +2 (still last) ==
  recompute: total
  recompute: ranking
  recompute: champion
total=17  banner=trinity is winning!

== neo +6 (takes the lead) ==
  recompute: total
  recompute: ranking
  recompute: champion
  recompute: banner
total=23  banner=neo is winning!
";
    assert_eq!(out, expected, "leaderboard console drifted from the spec");
}

#[test]
fn incremental_equals_from_scratch() {
    let out = run("tests/cases/run/incr_diff.pr");
    assert!(
        out.contains("incremental == from-scratch: PASS"),
        "differential oracle failed: {out}"
    );
}

// A warm run of the pure durable demo reuses every prefix memo from the snapshot,
// yet prints byte-for-byte what the cold run printed. This is the north-star
// property for the durable path: the snapshot changes cost, never output.
#[test]
fn durable_warm_output_matches_cold() {
    let snap = Path::new("target/incr_warm.snap");
    let _ = fs::remove_file(snap);
    let src =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/incr_warm.pr"))
            .unwrap();

    let (cold, cold_err) = run_io(&src);
    assert!(!cold_err, "cold run finishes cleanly");
    assert!(snap.exists(), "the cold run writes the snapshot");
    let header = fs::read_to_string(snap).unwrap();
    let header = header.lines().next().unwrap();
    assert!(
        header.starts_with("prism-incr-snapshot\t1\tincr-warm-v1\t"),
        "snapshot carries a versioned, program-tagged header: {header:?}"
    );

    let (warm, warm_err) = run_io(&src);
    assert!(!warm_err, "warm run finishes cleanly");
    assert_eq!(cold, warm, "warm output is byte-identical to cold");
    assert!(
        cold.contains("total=15  count=3  avg=5"),
        "demo output drifted: {cold}"
    );
    let _ = fs::remove_file(snap);
}

// Every kind of unusable snapshot (garbage, a decodable-but-junk body, a foreign
// tag, a stale version, a wrong digest, and a real snapshot whose body was
// tampered so its digest no longer matches) is a silent cold start: the program
// still computes 42, never errors, never partially loads.
#[test]
fn durable_bad_snapshot_cold_starts() {
    let snap = format!("target/incr_cc_{}.snap", std::process::id());
    let prog = cc_program(&snap);

    let check = |content: &str, label: &str| {
        fs::write(&snap, content).unwrap();
        let (out, err) = run_io(&prog);
        assert!(!err, "{label}: cold start never errors");
        assert!(
            out.contains("42"),
            "{label}: cold-starts to 42, got {out:?}"
        );
    };
    check("total garbage, not a snapshot", "garbage");
    check(
        "prism-incr-snapshot\t1\tcc\t00\n9,9,notanint,,\n",
        "valid header, junk body",
    );
    check(
        "prism-incr-snapshot\t1\tOTHER\t00\n2,1,50,\n",
        "foreign tag",
    );
    check("prism-incr-snapshot\t2\tcc\t00\n2,1,50,\n", "stale version");
    check(
        "prism-incr-snapshot\t1\tcc\tWRONGDIGEST\n2,1,50,\n",
        "wrong digest",
    );

    // A real, valid snapshot whose body is then tampered (one byte value bumped):
    // the header digest no longer matches, so it cold-starts rather than serving a
    // corrupted value.
    let _ = fs::remove_file(&snap);
    run_io(&prog);
    let good = fs::read_to_string(&snap).unwrap();
    let (head, body) = good.split_once('\n').unwrap();
    let mut vals: Vec<i64> = body
        .trim_end_matches(',')
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().unwrap())
        .collect();
    let last = vals.len() - 1;
    vals[last] = (vals[last] + 1) % 256;
    let tampered = vals
        .iter()
        .map(i64::to_string)
        .collect::<Vec<_>>()
        .join(",");
    fs::write(&snap, format!("{head}\n{tampered},")).unwrap();
    let (out, err) = run_io(&prog);
    assert!(
        !err && out.contains("42"),
        "tampered body cold-starts to 42, got {out:?}"
    );
    let _ = fs::remove_file(&snap);
}

// Adversarial condition for the prefix rule: a program that creates a memo only
// after the first `get` (input-dependent creation). Its dynamic node is
// scratch-only, so a warm run recomputes it while reusing the prefix memo, and the
// output stays byte-identical to a cold run. A prefix-rule regression that
// persisted the dynamic node under its creation index could return a stale value
// here; byte-identical output is the guard.
#[test]
fn durable_input_dependent_creation_warm_matches_cold() {
    let snap = format!("target/incr_adv_{}.snap", std::process::id());
    let prog = adversarial_program(&snap);
    let _ = fs::remove_file(&snap);

    let (cold, cold_err) = run_io(&prog);
    let (warm, warm_err) = run_io(&prog);
    assert!(!cold_err && !warm_err, "both runs finish cleanly");
    assert_eq!(
        cold, warm,
        "warm output byte-identical to cold under input-dependent creation"
    );
    assert!(cold.contains("111"), "expected 111, got {cold:?}");
    let _ = fs::remove_file(&snap);
}

// ---------- trace-replay-on-hit (effectful durable memos) ----------

// A durable trace-replay program: a memo that PRINTS `FIRE` when it fires and
// computes `get(a) + 40 = 42`, plus a nested memo `n` that PRINTS `NEST` and
// doubles the result. The pure `run_incr_durable` would reject a printing memo;
// `run_incr_durable_replay` records each memo's output and replays it on a hit,
// so cold and warm print the same bytes. The nested memo exercises the trace
// splice (a child's output rides its parent's trace in call order).
fn trace_program(snap: &str) -> String {
    format!(
        r#"import Incr (..)

fn main() =
  run_incr_durable_replay("{snap}", "tr") fn
    let a = input(2)
    let base = memo() fn
      println("FIRE")
      get(a) + 40
    let nested = memo() fn
      println("NEST before")
      let b = get(base)
      println("NEST after")
      b * 2
    println(show_int(get(nested)))
"#
    )
}

// The cold run records every memo's output trace; the warm run replays it and
// skips every thunk, yet prints byte-for-byte what the cold run printed,
// INCLUDING the effects (`FIRE`, `NEST before/after`) and in the same nested
// order. This is the north star: a durable hit re-emits the recorded effects,
// so a warm run is observationally identical to a cold one.
#[test]
fn trace_replay_warm_output_matches_cold_including_effects() {
    let snap = format!("target/incr_trace_{}.snap", std::process::id());
    let prog = trace_program(&snap);
    let _ = fs::remove_file(&snap);

    let (cold, cold_err) = run_io(&prog);
    assert!(!cold_err, "cold run finishes cleanly, got {cold:?}");
    assert!(snap_exists(&snap), "the cold run writes a trace snapshot");
    assert_eq!(
        cold, "NEST before\nFIRE\nNEST after\n84\n",
        "cold run fires the memos in nested call order"
    );

    let (warm, warm_err) = run_io(&prog);
    assert!(!warm_err, "warm run finishes cleanly, got {warm:?}");
    assert_eq!(
        cold, warm,
        "warm output is byte-identical to cold, effects included"
    );
    let _ = fs::remove_file(&snap);
}

// Exactly-once-equivalence: each recorded effect is re-emitted once on a warm
// run, never doubled (replay AND recompute both firing) or dropped (a hit
// staying silent). Counting the fire markers in cold and warm and asserting they
// are equal and nonzero is the guard that would catch either fault.
#[test]
fn trace_replay_effects_are_exactly_once() {
    let snap = format!("target/incr_once_{}.snap", std::process::id());
    let prog = trace_program(&snap);
    let _ = fs::remove_file(&snap);

    let (cold, _) = run_io(&prog);
    let (warm, _) = run_io(&prog);
    for marker in ["FIRE", "NEST before", "NEST after"] {
        let c = cold.matches(marker).count();
        let w = warm.matches(marker).count();
        assert_eq!(c, 1, "cold emits `{marker}` exactly once, got {c}");
        assert_eq!(
            w, c,
            "warm re-emits `{marker}` exactly as often as cold (no double/drop)"
        );
    }
    let _ = fs::remove_file(&snap);
}

// A dropped snapshot (removed) or a corrupted one (body tampered so the header
// digest no longer matches) is a silent cold start: the memos re-fire, print the
// same bytes, and the run never errors. The recorded trace is a cache, never a
// source of truth.
#[test]
fn trace_replay_dropped_or_corrupt_cold_starts() {
    let snap = format!("target/incr_trbad_{}.snap", std::process::id());
    let prog = trace_program(&snap);

    // Baseline cold output to compare every cold start against.
    let _ = fs::remove_file(&snap);
    let (baseline, base_err) = run_io(&prog);
    assert!(!base_err, "baseline cold run is clean");

    // Dropped: no snapshot at all cold-starts to the same bytes.
    let _ = fs::remove_file(&snap);
    let (dropped, dropped_err) = run_io(&prog);
    assert!(!dropped_err, "missing snapshot never errors");
    assert_eq!(
        dropped, baseline,
        "missing snapshot cold-starts identically"
    );

    // Corrupted: write a real snapshot, tamper its body (bump one byte value) so
    // the header digest fails, and confirm it cold-starts rather than serving a
    // corrupted trace.
    let _ = fs::remove_file(&snap);
    run_io(&prog);
    let good = fs::read_to_string(&snap).unwrap();
    let (head, body) = good.split_once('\n').unwrap();
    let tampered = format!("{head}\n{body}x");
    fs::write(&snap, tampered).unwrap();
    let (corrupt, corrupt_err) = run_io(&prog);
    assert!(!corrupt_err, "corrupt snapshot never errors");
    assert_eq!(
        corrupt, baseline,
        "corrupt snapshot cold-starts identically"
    );

    // A foreign tag is a cold start too: the same digest-checked header carries
    // the caller identity, so a snapshot written under another tag is ignored.
    let _ = fs::remove_file(&snap);
    fs::write(&snap, "prism-incr-trace-snapshot\t1\tOTHER\t00\n\n").unwrap();
    let (foreign, foreign_err) = run_io(&prog);
    assert!(!foreign_err, "foreign-tag snapshot never errors");
    assert_eq!(foreign, baseline, "foreign tag cold-starts identically");
    let _ = fs::remove_file(&snap);
}

fn snap_exists(path: &str) -> bool {
    Path::new(path).exists()
}
