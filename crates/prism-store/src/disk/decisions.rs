use std::io;
use std::path::{Path, PathBuf};

use prism_common::format::FormatTag;

use super::DECISIONS_DIR;

const DECISION_FORMAT: FormatTag = FormatTag::new("prism-query-decision-v1");

fn path(root: &Path, kind: &str, locator: &str) -> io::Result<PathBuf> {
    if kind.is_empty()
        || !kind
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte == b'-')
        || locator.len() < 2
        || !locator.bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid query-decision locator",
        ));
    }
    Ok(root.join(DECISIONS_DIR).join(kind).join(locator))
}

pub(super) fn get(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    kind: &str,
    locator: &str,
) -> io::Result<Option<Vec<u8>>> {
    match super::read_visible(pending, &path(root, kind, locator)?)? {
        Some(bytes) => {
            let unknown = |detail: String| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("query decision has an unknown format{detail}"),
                )
            };
            let line = bytes
                .iter()
                .position(|b| *b == b'\n')
                .ok_or_else(|| unknown(String::new()))?;
            let tag = std::str::from_utf8(&bytes[..line]).unwrap_or_default();
            DECISION_FORMAT
                .expect(tag)
                .map_err(|e| unknown(format!(": {e}")))?;
            Ok(Some(bytes[line + 1..].to_vec()))
        }
        None => Ok(None),
    }
}

pub(super) fn put(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    kind: &str,
    locator: &str,
    bytes: &[u8],
) -> io::Result<()> {
    let mut encoded = format!("{DECISION_FORMAT}\n").into_bytes();
    encoded.extend_from_slice(bytes);
    super::atomic_write_in(pending, &path(root, kind, locator)?, &encoded)
}
