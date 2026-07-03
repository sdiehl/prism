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
// property for B1's durable half: the snapshot changes cost, never output.
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
