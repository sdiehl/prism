use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use super::{atomic_write_if_absent, StoreHash};

#[cfg(test)]
use super::faults::{self, FaultPoint};

const QUERIES_DIR: &str = "queries";
const QUERY_FORMAT: &str = "prism-query-index-v1";

fn kind_ok(kind: &str) -> bool {
    !kind.is_empty()
        && kind
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b'-' | b'.'))
}

fn path(root: &Path, kind: &str, key: &StoreHash<'_>) -> io::Result<PathBuf> {
    if !kind_ok(kind) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "query kind must contain only lowercase ASCII, digits, '-' or '.'",
        ));
    }
    Ok(root.join(QUERIES_DIR).join(kind).join(key.as_str()))
}

pub(super) fn get(root: &Path, kind: &str, key: &StoreHash<'_>) -> io::Result<Option<String>> {
    let path = path(root, kind, key)?;
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let mut lines = text.lines();
    if lines.next() != Some(QUERY_FORMAT) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "query entry has an unknown format",
        ));
    }
    let output = lines.next().unwrap_or_default();
    StoreHash::new(output)?;
    if lines.next().is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "query entry has trailing rows",
        ));
    }
    Ok(Some(output.to_string()))
}

pub(super) fn put(
    root: &Path,
    kind: &str,
    key: &StoreHash<'_>,
    output: &StoreHash<'_>,
) -> io::Result<()> {
    let path = path(root, kind, key)?;
    if let Some(existing) = get(root, kind, key)? {
        if existing == output.as_str() {
            return Ok(());
        }
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "query {kind}/{} already maps to {existing}, not {output}",
                key.as_str()
            ),
        ));
    }
    #[cfg(test)]
    faults::hit(FaultPoint::BeforeQueryPublish)?;
    let bytes = format!("{QUERY_FORMAT}\n{}\n", output.as_str());
    if atomic_write_if_absent(&path, bytes.as_bytes())? {
        return Ok(());
    }
    match get(root, kind, key)? {
        Some(existing) if existing == output.as_str() => Ok(()),
        Some(existing) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "query {kind}/{} concurrently mapped to {existing}, not {output}",
                key.as_str()
            ),
        )),
        None => Err(io::Error::new(
            io::ErrorKind::NotFound,
            "query entry disappeared during concurrent commit",
        )),
    }
}
