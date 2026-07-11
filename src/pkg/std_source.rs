//! Source bundles for store-served package and standard-library roots.
//!
//! The existing store object layer can already hold immutable blobs keyed by a
//! root hash. This codec gives the package layer a compact blob shape for the
//! source-level artifact the resolver needs before Core import lands: a dotted
//! module table. The bundle header carries the compiler Core-hash scheme because
//! the artifact's digest is only meaningful under the identity discipline that
//! produced it. The records are length-prefixed rather than line-oriented after
//! the header, so module source may contain arbitrary newlines without escaping
//! or lossy round-trips.

use std::collections::BTreeMap;
use std::str;

use crate::core::HASH_SCHEME;
use crate::error::Error;

const MAGIC: &[u8] = b"prism-source-bundle\tv1\n";
const SCHEME_FIELD: &[u8] = b"scheme\t";
const FIELD_SEP: u8 = b'\t';
const RECORD_SEP: u8 = b'\n';

/// Encode a dotted-module source table as one deterministic store object.
#[must_use]
pub fn encode_source_bundle<I, N, S>(modules: I) -> Vec<u8>
where
    I: IntoIterator<Item = (N, S)>,
    N: AsRef<str>,
    S: AsRef<str>,
{
    let mut sorted = BTreeMap::new();
    for (name, src) in modules {
        sorted.insert(name.as_ref().to_string(), src.as_ref().to_string());
    }

    let mut out = MAGIC.to_vec();
    out.extend_from_slice(SCHEME_FIELD);
    out.extend_from_slice(HASH_SCHEME.as_bytes());
    out.push(RECORD_SEP);
    for (name, src) in sorted {
        let name = name.as_bytes();
        let src = src.as_bytes();
        out.extend_from_slice(name.len().to_string().as_bytes());
        out.push(FIELD_SEP);
        out.extend_from_slice(src.len().to_string().as_bytes());
        out.push(RECORD_SEP);
        out.extend_from_slice(name);
        out.extend_from_slice(src);
    }
    out
}

/// Decode a store-served source bundle into dotted module sources.
///
/// # Errors
/// Fails when the object has the wrong header, malformed lengths, invalid UTF-8,
/// duplicate module names, or is truncated.
pub fn decode_source_bundle(bytes: &[u8]) -> Result<BTreeMap<String, String>, Error> {
    if !bytes.starts_with(MAGIC) {
        return Err(bundle_error("missing source bundle header"));
    }
    let mut cursor = MAGIC.len();
    read_scheme(bytes, &mut cursor)?;
    let mut modules = BTreeMap::new();
    while cursor < bytes.len() {
        let name_len = read_len(bytes, &mut cursor, FIELD_SEP)?;
        let src_len = read_len(bytes, &mut cursor, RECORD_SEP)?;
        let name = read_utf8(bytes, &mut cursor, name_len)?;
        let src = read_utf8(bytes, &mut cursor, src_len)?;
        if modules.insert(name.clone(), src).is_some() {
            return Err(bundle_error(format!("duplicate module `{name}`")));
        }
    }
    Ok(modules)
}

fn read_scheme(bytes: &[u8], cursor: &mut usize) -> Result<(), Error> {
    let rest = bytes
        .get(*cursor..)
        .ok_or_else(|| bundle_error("truncated scheme field"))?;
    if !rest.starts_with(SCHEME_FIELD) {
        return Err(bundle_error("missing hash scheme"));
    }
    *cursor += SCHEME_FIELD.len();
    let start = *cursor;
    while *cursor < bytes.len() && bytes[*cursor] != RECORD_SEP {
        *cursor += 1;
    }
    if *cursor == bytes.len() {
        return Err(bundle_error("truncated hash scheme"));
    }
    let scheme =
        str::from_utf8(&bytes[start..*cursor]).map_err(|_| bundle_error("non-utf8 scheme"))?;
    if scheme != HASH_SCHEME {
        return Err(bundle_error(format!(
            "foreign hash scheme {scheme:?}; this build speaks {HASH_SCHEME:?}"
        )));
    }
    *cursor += 1;
    Ok(())
}

fn read_len(bytes: &[u8], cursor: &mut usize, sep: u8) -> Result<usize, Error> {
    let start = *cursor;
    while *cursor < bytes.len() && bytes[*cursor] != sep {
        *cursor += 1;
    }
    if *cursor == bytes.len() {
        return Err(bundle_error("truncated length field"));
    }
    if start == *cursor || !bytes[start..*cursor].iter().all(u8::is_ascii_digit) {
        return Err(bundle_error("malformed length field"));
    }
    let digits =
        str::from_utf8(&bytes[start..*cursor]).map_err(|_| bundle_error("non-utf8 length"))?;
    *cursor += 1;
    digits
        .parse()
        .map_err(|_| bundle_error("length field overflows usize"))
}

fn read_utf8(bytes: &[u8], cursor: &mut usize, len: usize) -> Result<String, Error> {
    let end = cursor
        .checked_add(len)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| bundle_error("truncated payload"))?;
    let text = str::from_utf8(&bytes[*cursor..end])
        .map_err(|_| bundle_error("payload is not valid utf-8"))?;
    *cursor = end;
    Ok(text.to_string())
}

fn bundle_error(msg: impl Into<String>) -> Error {
    Error::ResolvePackage(format!("invalid source bundle: {}", msg.into()))
}

#[cfg(test)]
mod tests {
    use super::{decode_source_bundle, encode_source_bundle};
    use crate::core::HASH_SCHEME;

    #[test]
    fn source_bundle_header_names_hash_scheme() {
        let bytes = encode_source_bundle([("A", "pub fn x() = 1\n")]);
        let text = String::from_utf8_lossy(&bytes);
        assert!(text.starts_with("prism-source-bundle\tv1\n"));
        assert!(text.contains(&format!("scheme\t{HASH_SCHEME}\n")));
    }

    #[test]
    fn source_bundle_rejects_foreign_hash_scheme() {
        let mut bytes = encode_source_bundle([("A", "pub fn x() = 1\n")]);
        let from = format!("scheme\t{HASH_SCHEME}\n");
        let to = "scheme\tforeign-scheme\n";
        let text = String::from_utf8(bytes).unwrap().replace(&from, to);
        bytes = text.into_bytes();
        let err = decode_source_bundle(&bytes).unwrap_err().to_string();
        assert!(err.contains("foreign hash scheme"), "{err}");
    }
}
