use std::io;
use std::path::{Path, PathBuf};

use super::DECISIONS_DIR;

const DECISION_FORMAT: &str = "prism-query-decision-v1";

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
            let prefix = format!("{DECISION_FORMAT}\n");
            if !bytes.starts_with(prefix.as_bytes()) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "query decision has an unknown format",
                ));
            }
            Ok(Some(bytes[prefix.len()..].to_vec()))
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
