//! The `prism-test-failure-v1` structured-failure test ABI.
//!
//! The compiler-owned wire payload a structured test failure carries from the
//! stdlib assertion layer to the harness, which converts it into a `test_failed`
//! event. The harness also recognizes the payload-free built-in `Fail`;
//! `Test.pr` expectations (`expect`, `expect_equal`, and context attachment) use
//! the versioned envelope so assertion wrappers need no second wire contract. It
//! is identified by its schema tag plus ABI version, not an arbitrary user-visible
//! name; a foreign tag or ABI is rejected rather than misread. The bytes follow
//! the same discipline as the manifest codec
//! (`crate::util::binary`: LEB128 lengths, bounded reads, a trailing-byte check).
//!
//! The `site` field is optional diagnostic metadata for a caller node/location.
//! It is not part of semantic identity and never enters a Core hash.

use crate::store::CodecError;
use crate::util::binary::{put_str, put_uvarint, Reader};

use super::TEST_FAILURE_SCHEMA;

/// The failure ABI version folded into the bytes. A format change bumps this so an
/// old reader rejects new bytes rather than misreading them.
const FAILURE_ABI: u64 = 1;

/// A structured test failure.
///
/// A message plus optional expected/actual/diff values, an ordered context stack,
/// and an optional diagnostic source site. The stdlib assertion layer builds one;
/// the harness renders it into a `test_failed` event.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Failure {
    /// The human-readable failure summary.
    pub message: String,
    /// The expected value, rendered, when the assertion had one.
    pub expected: Option<String>,
    /// The actual value, rendered, when the assertion had one.
    pub actual: Option<String>,
    /// A rendered difference between expected and actual, when computed.
    pub diff: Option<String>,
    /// Reserved diagnostic source site (never semantic identity).
    pub site: Option<String>,
    /// The context stack attached to the failure, outermost first.
    pub context: Vec<String>,
}

/// Encode a structured failure into canonical `prism-test-failure-v1` bytes.
#[must_use]
pub fn encode_failure(failure: &Failure) -> Vec<u8> {
    let mut out = Vec::new();
    put_str(&mut out, TEST_FAILURE_SCHEMA);
    put_uvarint(&mut out, FAILURE_ABI);
    put_str(&mut out, &failure.message);
    put_opt(&mut out, failure.expected.as_deref());
    put_opt(&mut out, failure.actual.as_deref());
    put_opt(&mut out, failure.diff.as_deref());
    put_opt(&mut out, failure.site.as_deref());
    put_uvarint(&mut out, failure.context.len() as u64);
    for entry in &failure.context {
        put_str(&mut out, entry);
    }
    out
}

/// Decode canonical failure bytes back into a [`Failure`].
///
/// Rejects a foreign scheme tag, a foreign ABI, a truncated frame, and trailing
/// bytes, so a stale or hostile payload lands on a [`CodecError`] rather than a
/// mangled failure.
///
/// # Errors
/// A [`CodecError`] on a foreign scheme, foreign ABI, truncation, an over-long
/// length, invalid UTF-8, or trailing bytes.
pub fn decode_failure(bytes: &[u8]) -> Result<Failure, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != TEST_FAILURE_SCHEMA {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != FAILURE_ABI {
        return Err(CodecError::Kind);
    }
    let message = r.string()?;
    let expected = get_opt(&mut r)?;
    let actual = get_opt(&mut r)?;
    let diff = get_opt(&mut r)?;
    let site = get_opt(&mut r)?;
    let count = r.bounded_len()?;
    let mut context = Vec::with_capacity(count);
    for _ in 0..count {
        context.push(r.string()?);
    }
    if !r.at_end() {
        return Err(CodecError::TrailingBytes);
    }
    Ok(Failure {
        message,
        expected,
        actual,
        diff,
        site,
        context,
    })
}

// An optional string: a presence byte, then the string when present. The byte is
// 1/0 and any other value is rejected by `Reader::bool`.
fn put_opt(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(s) => {
            out.push(1);
            put_str(out, s);
        }
        None => out.push(0),
    }
}

fn get_opt(r: &mut Reader<'_>) -> Result<Option<String>, CodecError> {
    if r.bool()? {
        Ok(Some(r.string()?))
    } else {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Failure {
        Failure {
            message: "values differ".to_string(),
            expected: Some("4".to_string()),
            actual: Some("5".to_string()),
            diff: Some("- 4\n+ 5".to_string()),
            site: Some("M.pr:12:3".to_string()),
            context: vec![
                "while checking addition".to_string(),
                "x = 2, y = 3".to_string(),
            ],
        }
    }

    #[test]
    fn round_trips_all_fields() {
        let failure = sample();
        let back = decode_failure(&encode_failure(&failure)).unwrap();
        assert_eq!(back, failure);
        // Re-encoding the decoded value is byte-identical.
        assert_eq!(encode_failure(&back), encode_failure(&failure));
    }

    #[test]
    fn round_trips_when_optionals_are_absent() {
        let failure = Failure {
            message: "bare".to_string(),
            ..Failure::default()
        };
        assert_eq!(decode_failure(&encode_failure(&failure)).unwrap(), failure);
    }

    #[test]
    fn rejects_foreign_abi_scheme_and_truncation() {
        let bytes = encode_failure(&sample());
        // A truncated frame is rejected, not misread.
        assert!(decode_failure(&bytes[..bytes.len() - 1]).is_err());
        // A flipped scheme byte is rejected.
        let mut foreign = bytes.clone();
        foreign[1] ^= 0xff;
        assert!(decode_failure(&foreign).is_err());
        // Trailing bytes are rejected.
        let mut trailing = bytes;
        trailing.push(0);
        assert_eq!(
            decode_failure(&trailing).unwrap_err(),
            CodecError::TrailingBytes
        );
    }
}
