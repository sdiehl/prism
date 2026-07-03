//! The `.replay` frame codec: the durable form of an execution's observation
//! trace.
//!
//! A trace is a sequence of self-delimiting frames, one per observation, in the
//! exact format `lib/std/Replay.pr` writes (so a log produced by the `durable`
//! handler and a trace produced by `prism run --record` are the same bytes and
//! either tool reads the other). Each frame is a tag character, the *character*
//! length of its payload, a `:` delimiter, then the payload:
//!
//! ```text
//! I3:123    an Int observation (read_int, rand, args_count)
//! S5:hello  a String observation (read_line, read_file, getenv, arg)
//! B1:1      a Bool observation (file_exists)
//! O0:       an output boundary (print, println)
//! ```
//!
//! The length prefix makes any payload round-trip, newlines and `:` included, so
//! `decode(encode(t)) == t` for every trace. Lengths are counted in characters,
//! matching `Replay.pr`'s `str_len`, so a multi-byte payload agrees across the
//! language boundary.

use crate::eval::Obs;

const TAG_INT: char = 'I';
const TAG_STR: char = 'S';
const TAG_BOOL: char = 'B';
const TAG_OUT: char = 'O';
const DELIM: char = ':';

// The tag and payload of one observation, the raw form of a frame.
fn field(tag: char, payload: &str) -> String {
    // Character count, not byte count: `Replay.pr` measures payloads in chars.
    format!("{tag}{}{DELIM}{payload}", payload.chars().count())
}

fn encode_one(o: &Obs) -> String {
    match o {
        Obs::Int(n) => field(TAG_INT, &n.to_string()),
        Obs::Str(s) => field(TAG_STR, s),
        Obs::Bool(b) => field(TAG_BOOL, if *b { "1" } else { "0" }),
        Obs::Out => field(TAG_OUT, ""),
    }
}

/// Encode a trace to its self-delimiting `.replay` string form.
#[must_use]
pub fn encode(frames: &[Obs]) -> String {
    frames.iter().map(encode_one).collect()
}

/// Decode a `.replay` string back into its observation frames.
///
/// # Errors
/// Fails on a malformed frame: a truncated header, a missing delimiter, a
/// non-numeric length, or a payload that runs past the end of the input.
pub fn decode(s: &str) -> Result<Vec<Obs>, String> {
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let tag = chars[i];
        // The delimiter closes the decimal length that starts at i+1.
        let colon = chars[(i + 1)..]
            .iter()
            .position(|&c| c == DELIM)
            .map(|p| i + 1 + p)
            .ok_or_else(|| format!("replay trace: no '{DELIM}' after tag at {i}"))?;
        let len: usize = chars[(i + 1)..colon]
            .iter()
            .collect::<String>()
            .parse()
            .map_err(|_| format!("replay trace: bad length at {i}"))?;
        let start = colon + 1;
        let end = start + len;
        if end > chars.len() {
            return Err(format!("replay trace: payload at {start} runs past end"));
        }
        let payload: String = chars[start..end].iter().collect();
        out.push(decode_one(tag, &payload)?);
        i = end;
    }
    Ok(out)
}

fn decode_one(tag: char, payload: &str) -> Result<Obs, String> {
    match tag {
        TAG_INT => payload
            .parse()
            .map(Obs::Int)
            .map_err(|_| format!("replay trace: bad int payload {payload:?}")),
        TAG_BOOL => Ok(Obs::Bool(payload == "1")),
        TAG_OUT => Ok(Obs::Out),
        TAG_STR => Ok(Obs::Str(payload.to_string())),
        other => Err(format!("replay trace: unknown tag {other:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::{decode, encode};
    use crate::eval::Obs;

    #[test]
    fn round_trips_every_frame_kind() {
        let t = vec![
            Obs::Int(0),
            Obs::Int(-123),
            Obs::Str("hello".into()),
            // Delimiter and newline in the payload, the length-prefix's whole job.
            Obs::Str("a:b\nc".into()),
            Obs::Str(String::new()),
            Obs::Bool(true),
            Obs::Bool(false),
            Obs::Out,
        ];
        assert_eq!(decode(&encode(&t)).unwrap(), t);
    }

    #[test]
    fn matches_replay_pr_field_format() {
        // The exact bytes `Replay.pr`'s `enc_entry` would produce.
        assert_eq!(encode(&[Obs::Int(123)]), "I3:123");
        assert_eq!(encode(&[Obs::Str("hi".into())]), "S2:hi");
        assert_eq!(encode(&[Obs::Bool(true)]), "B1:1");
        assert_eq!(encode(&[Obs::Out]), "O0:");
    }

    #[test]
    fn rejects_malformed() {
        assert!(decode("I3").is_err());
        assert!(decode("X0:").is_err());
        assert!(decode("S9:hi").is_err());
    }
}
