// Functional oracles for the Time and JSON substrate halves. Parity (native
// == interpreter) and leak-freedom are covered by the corpus for the examples in
// `examples/`; these tests check the behaviors a differential corpus cannot see: the
// exact canonical JSON bytes, the exact-or-error number policy, positioned
// hostile-input rejection, the typed round trip, RFC 3339 arithmetic, and the
// Time record/replay round trip (a real clock read reproduced byte-for-byte).

use prism::resolve::default_roots;
use prism::{interpret_io_on, record_on, replay_on, with_prelude, Config};
use std::io::Cursor;
use std::path::Path;

fn cfg() -> Config {
    Config::from_env()
}

fn roots() -> Vec<prism::resolve::Root> {
    default_roots(Path::new("."))
}

// Run a program (prelude prepended) on empty stdin, returning its stdout.
fn run(src: &str) -> String {
    let full = with_prelude(src);
    let mut out: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    interpret_io_on(&full, &roots(), &mut out, &mut input, &cfg())
        .unwrap_or_else(|e| panic!("run failed: {e:?}"));
    String::from_utf8(out).expect("utf8 output")
}

#[test]
fn json_canonical_encoding_is_deterministic() {
    // decode then encode yields the canonical form: keys sorted, whitespace gone,
    // arrays and nesting preserved, string escapes normalized.
    let src = include_str!("../fixtures/runtime/time_json_1.pr");
    assert_eq!(
        run(src),
        "42\n-7\n1.5\ntrue\nnull\n[1,2,3]\n{\"a\":2,\"b\":1,\"c\":[true,null]}\n\"tab\\tnewline\\n\"\n"
    );
}

#[test]
fn json_key_order_is_irrelevant_to_bytes() {
    // Two objects differing only in key order encode to identical bytes, so a JSON
    // value has a well-defined content hash.
    let src = r#"
import Json (..)

fn enc(s) =
  match decode(s) of
    Ok(j) => encode(j)
    Err(e) => "err"

fn main() =
  println(if str_eq(enc("\{\"z\":1,\"m\":2,\"a\":3}"), enc("\{\"a\":3,\"z\":1,\"m\":2}")) then "same" else "different")
"#;
    assert_eq!(run(src), "same\n");
}

#[test]
fn json_number_policy_is_exact_or_error() {
    // Exact by default: an in-range integer decodes to JInt; a non-canonical
    // spelling is a decode error. Lossy mode normalizes.
    let src = include_str!("../fixtures/runtime/time_json_2.pr");
    // A canonical decimal ("1.5") is exact; a non-canonical spelling ("1.0", "1e3")
    // errors in exact mode and normalizes in lossy mode. `Int` is arbitrary
    // precision, so a large integer literal is an exact `JInt`, not an overflow.
    assert_eq!(
        run(src),
        "ok 1\nok 1.5\nerr\nerr\nok 100000000000000000000000000000\nok 1\nok 1000\nok 100000000000000000000000000000\n"
    );
}

#[test]
fn json_parser_is_total_on_hostile_input() {
    // Every malformed input is one positioned error, never a panic or partial
    // value: unterminated containers, trailing input, bad numbers, unterminated
    // strings, and a nesting depth beyond the limit.
    let src = include_str!("../fixtures/runtime/time_json_3.pr");
    assert_eq!(
        run(src),
        "line 1 col 5: unterminated array\n\
         line 1 col 8: expected string key in object\n\
         line 1 col 4: trailing input after top-level value\n\
         line 1 col 8: trailing input after top-level value\n\
         line 1 col 14: unterminated string\n\
         line 1 col 1: unexpected character\n\
         line 1 col 1: unexpected end of input\n\
         line 1 col 513: maximum nesting depth exceeded\n"
    );
}

#[test]
fn json_typed_layer_round_trips() {
    // to_json/from_json compose to identity through a canonical string.
    let src = include_str!("../fixtures/runtime/time_json_4.pr");
    assert_eq!(run(src), "[1,2,3]\n[1,2,3]\n[true,\"hi\"]\n");
}

#[test]
fn time_rfc3339_formats_and_parses() {
    let src = include_str!("../fixtures/runtime/time_json_5.pr");
    assert_eq!(
        run(src),
        "1970-01-01T00:00:00Z\n\
         2025-07-04T11:54:56.123456789Z\n\
         2026-07-04T12:34:56Z\n\
         2026-07-04T12:34:56.123456789Z\n\
         2026-07-04T10:34:56Z\n\
         2026-07-04T18:04:56Z\n\
         none\n\
         none\n"
    );
}

#[test]
fn time_duration_arithmetic() {
    let src = r"
import Time (..)

fn main() =
  println(show_int(dur_nanos(dur_add(seconds(1), millis(500)))))
  println(show_int(dur_nanos(dur_sub(seconds(2), millis(250)))))
  println(show_int(dur_nanos(dur_scale(millis(3), 4))))
  println(show_int(dur_cmp(seconds(2), seconds(3))))
  println(show_int(dur_as_secs(dur_add(seconds(90), Duration(0)))))
";
    assert_eq!(run(src), "1500000000\n1750000000\n12000000\n-1\n90\n");
}

// The important Time property: a program that reads the real wall clock records
// each read, and replaying the trace reproduces the run byte-for-byte, times and
// all, with no real clock consulted.
const CLOCK_PROGRAM: &str = r"
import Time (..)

fn body() =
  let a = wall_clock()
  let b = mono_clock()
  println(format_rfc3339(a))
  println(show_int(instant_nanos(b)))

fn main() =
  run_clock_real(body)
";

#[test]
fn time_reads_replay_byte_for_byte() {
    let full = with_prelude(CLOCK_PROGRAM);

    let mut rec_out: Vec<u8> = Vec::new();
    let mut rec_in = Cursor::new(Vec::new());
    let (_exit, trace_str, n_obs) =
        record_on(&full, &roots(), &mut rec_out, &mut rec_in, &cfg()).expect("record");
    assert!(n_obs >= 2, "the run observed both clock reads, got {n_obs}");

    let mut replay_out: Vec<u8> = Vec::new();
    replay_on(&full, &roots(), &mut replay_out, &trace_str, &cfg()).expect("replay");

    assert_eq!(
        replay_out, rec_out,
        "replaying the trace reproduces the recorded clock reads byte-for-byte"
    );
    // The recorded run actually produced a timestamp, not an empty transcript.
    let text = String::from_utf8(rec_out).unwrap();
    assert!(
        text.starts_with('2') || text.starts_with('1'),
        "first line is an RFC 3339 timestamp, got {text:?}"
    );
}
