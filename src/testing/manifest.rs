//! The `prism-test-manifest-v1` canonical byte codec.
//!
//! A manifest is the deterministic discovery artifact: sorted by logical ID,
//! carrying enough per-test identity to rebuild and execute a harness without
//! rediscovering declarations. It follows the byte discipline in
//! `crate::util::binary` (LEB128 lengths, bounded reads, a trailing-byte check),
//! the same substrate the Core codec rides. Diagnostic locations are side
//! metadata and never enter these bytes, so the manifest is byte-identical
//! across checkout roots.

use crate::store::CodecError;
use crate::util::binary::{put_str, put_uvarint, Reader};

use super::discovery::TestDescriptor;
use super::TEST_MANIFEST_SCHEMA;

/// The manifest ABI version folded into the bytes. A format change bumps this so
/// an old reader rejects new bytes rather than misreading them.
const MANIFEST_ABI: u64 = 1;

/// A decode error for the manifest wire format.
pub type ManifestError = CodecError;

/// Encode a sorted descriptor set into canonical `prism-test-manifest-v1` bytes.
///
/// The descriptors must already be sorted by logical ID (discovery guarantees
/// this); the encoding does not re-sort, so a caller passing an unsorted set
/// produces non-canonical bytes on purpose-detectable-by-the-round-trip.
#[must_use]
pub fn encode_manifest(descriptors: &[TestDescriptor]) -> Vec<u8> {
    let mut out = Vec::new();
    put_str(&mut out, TEST_MANIFEST_SCHEMA);
    put_uvarint(&mut out, MANIFEST_ABI);
    put_uvarint(&mut out, descriptors.len() as u64);
    for d in descriptors {
        // Semantic identity only: the diagnostic location is deliberately omitted.
        put_str(&mut out, &d.logical_id);
        put_str(&mut out, &d.defining_module_id);
        put_str(&mut out, &d.definition_id);
        put_str(&mut out, &d.test_core_digest);
        put_str(&mut out, &d.dependency_closure_digest);
    }
    out
}

/// Decode canonical manifest bytes back into descriptors.
///
/// Rejects a foreign scheme tag, a foreign ABI, a truncated frame, and trailing
/// bytes. The decoded descriptors carry an empty `diagnostic_location`, since
/// that field is not part of the canonical bytes.
///
/// # Errors
/// A [`CodecError`] on a foreign scheme, foreign ABI, truncation, an over-long
/// length, or trailing bytes.
pub fn decode_manifest(bytes: &[u8]) -> Result<Vec<TestDescriptor>, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != TEST_MANIFEST_SCHEMA {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != MANIFEST_ABI {
        return Err(CodecError::Kind);
    }
    let count = r.bounded_len()?;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        out.push(TestDescriptor {
            logical_id: r.string()?,
            defining_module_id: r.string()?,
            definition_id: r.string()?,
            test_core_digest: r.string()?,
            dependency_closure_digest: r.string()?,
            diagnostic_location: String::new(),
        });
    }
    if !r.at_end() {
        return Err(CodecError::TrailingBytes);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn descriptor(id: &str) -> TestDescriptor {
        TestDescriptor {
            logical_id: id.to_string(),
            defining_module_id: "M".to_string(),
            definition_id: format!("M@{id}"),
            test_core_digest: "aa".to_string(),
            dependency_closure_digest: "bb".to_string(),
            diagnostic_location: "/abs/path.pr".to_string(),
        }
    }

    #[test]
    fn round_trips_without_location() {
        let ds = vec![descriptor("a"), descriptor("b")];
        let bytes = encode_manifest(&ds);
        let back = decode_manifest(&bytes).unwrap();
        assert_eq!(back.len(), 2);
        assert_eq!(back[0].logical_id, "a");
        // The diagnostic location does not survive: it is not canonical.
        assert!(back[0].diagnostic_location.is_empty());
        // Re-encoding the decoded descriptors is byte-identical.
        assert_eq!(encode_manifest(&back), bytes);
    }

    #[test]
    fn location_does_not_move_bytes() {
        let mut a = descriptor("a");
        let mut b = descriptor("a");
        a.diagnostic_location = "/one.pr".to_string();
        b.diagnostic_location = "/two.pr".to_string();
        assert_eq!(encode_manifest(&[a]), encode_manifest(&[b]));
    }

    #[test]
    fn rejects_foreign_scheme_and_truncation() {
        let mut wrong = encode_manifest(&[descriptor("a")]);
        assert!(decode_manifest(&wrong[..wrong.len() - 1]).is_err());
        wrong[1] ^= 0xff;
        assert!(decode_manifest(&wrong).is_err());
    }
}
