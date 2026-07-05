//! `prism.lock`: the committed, human-readable pin of every dependency's resolved
//! root hash.
//!
//! The lock is flat and line-oriented, in the same shape as the store's own index
//! files: a versioned header line, then one TAB-separated row per dependency.
//! Nothing in it is fuzzy. Each row records a dependency name, the exact content
//! hash it resolved to, and the source that hash came from, so a build reads a
//! set of hashes it can verify by content and never re-solves a range (there are
//! none). A locked hash is terminal: on a warm cache it is never re-resolved,
//! re-fetched, or re-verified.
//!
//! ```text
//! prism-lock<TAB>v1
//! <name><TAB><root-hash><TAB><source>
//! ```
//!
//! The `<source>` field is space-tokenized, mirroring the store index's
//! within-field lists: `path <dir>`, `git <url> <tag>`, or `hash <hex>`. Names,
//! hashes, paths, urls, and tags contain neither a TAB nor a space, so both
//! separators are unambiguous; a token that would contain one is refused on write
//! rather than silently corrupting the file.

use std::fmt::Write as _;

use crate::error::Error;
use crate::project::DepSource;

// The lock is its own format family, versioned independently of the store index
// files it is modeled on; the separators match theirs (TAB between fields, space
// within a field's list) but are declared here because this is a distinct file.
const LOCK_HEADER: &str = "prism-lock\tv1";
const FIELD_SEP: char = '\t';
const TOKEN_SEP: char = ' ';

const SRC_PATH: &str = "path";
const SRC_GIT: &str = "git";
const SRC_HASH: &str = "hash";

// The reserved name of the standard-library pin. Unlike a dependency row, the
// Std pin has no `source` field: its bytes are the compiler's embedded stdlib, so
// the pin records only the root hash the lockfile was resolved against. Written
// as a distinguished two-field line (`std<TAB><root-hash>`) so it never collides
// with a three-field dependency row, even one a project happened to name `std`.
const STD_ROOT_NAME: &str = "std";

/// The resolved pin of one dependency: its name, the root hash it resolved to,
/// and the source that hash was resolved from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockEntry {
    pub name: String,
    pub hash: String,
    pub source: DepSource,
}

/// A parsed `prism.lock`: the pinned standard-library root and dependencies,
/// ordered by name so the file is stable across writes and diffs cleanly.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Lock {
    /// The standard-library root hash the lockfile is pinned against (the fold
    /// `driver::stdlib_hash` produces). `None` when the lock predates a Std pin,
    /// in which case the build runs against whatever stdlib the compiler embeds.
    pub std_root: Option<String>,
    pub entries: Vec<LockEntry>,
}

impl Lock {
    /// Pin the standard library to `root`, the fold over the embedded stdlib. A
    /// build can then detect that its compiler ships a different Std than the one
    /// the lock was resolved against ([`crate::pkg::std_pin_status`]).
    pub fn pin_std(&mut self, root: String) {
        self.std_root = Some(root);
    }

    /// The pinned standard-library root, if the lock records one.
    #[must_use]
    pub fn std_root(&self) -> Option<&str> {
        self.std_root.as_deref()
    }

    /// Insert or replace the pin for `entry.name`, keeping the entries sorted.
    pub fn set(&mut self, entry: LockEntry) {
        match self.entries.iter_mut().find(|e| e.name == entry.name) {
            Some(existing) => *existing = entry,
            None => self.entries.push(entry),
        }
        self.entries.sort_by(|a, b| a.name.cmp(&b.name));
    }

    /// The pinned hash for `name`, if any.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&LockEntry> {
        self.entries.iter().find(|e| e.name == name)
    }

    /// Parse a `prism.lock` document.
    ///
    /// # Errors
    /// Fails on a missing or wrong header, a malformed row, or an unrecognized
    /// source token.
    pub fn parse(text: &str) -> Result<Self, Error> {
        let mut lines = text.lines();
        if lines.next() != Some(LOCK_HEADER) {
            return Err(Error::Resolve(format!(
                "prism.lock: missing or unrecognized header (expected {LOCK_HEADER:?})"
            )));
        }
        let mut std_root = None;
        let mut entries = Vec::new();
        for line in lines.filter(|l| !l.trim().is_empty()) {
            // The Std pin is the two-field `std<TAB><hash>` line; everything else
            // is a three-field dependency row.
            let fields: Vec<&str> = line.splitn(3, FIELD_SEP).collect();
            if let [name, hash] = fields.as_slice() {
                if *name == STD_ROOT_NAME {
                    std_root = Some((*hash).to_string());
                    continue;
                }
            }
            entries.push(parse_row(line)?);
        }
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(Self { std_root, entries })
    }

    /// Render the lock to its committed text.
    ///
    /// # Errors
    /// Fails if any field contains a separator character (a TAB or a space inside
    /// a token), which would make the round-trip lossy.
    pub fn render(&self) -> Result<String, Error> {
        let mut out = String::from(LOCK_HEADER);
        out.push('\n');
        if let Some(root) = &self.std_root {
            reject_separators(root)?;
            let _ = writeln!(out, "{STD_ROOT_NAME}{FIELD_SEP}{root}");
        }
        for e in &self.entries {
            let source = source_field(&e.source)?;
            reject_separators(&e.name)?;
            reject_separators(&e.hash)?;
            let _ = writeln!(out, "{}{FIELD_SEP}{}{FIELD_SEP}{source}", e.name, e.hash);
        }
        Ok(out)
    }
}

// Serialize a dependency source to the lock's space-tokenized source field. Each
// token is separator-free (a space or tab inside one would make the round-trip
// lossy), so the field re-splits back to the same tokens on parse.
fn source_field(source: &DepSource) -> Result<String, Error> {
    match source {
        DepSource::Path(p) => token_field(&[SRC_PATH, &p.display().to_string()]),
        DepSource::Git { url, version } => token_field(&[SRC_GIT, url, version]),
        DepSource::Hash(hex) => token_field(&[SRC_HASH, hex]),
    }
}

fn token_field(tokens: &[&str]) -> Result<String, Error> {
    for t in tokens {
        reject_separators(t)?;
    }
    Ok(tokens.join(&TOKEN_SEP.to_string()))
}

fn parse_row(line: &str) -> Result<LockEntry, Error> {
    let mut fields = line.splitn(3, FIELD_SEP);
    let (Some(name), Some(hash), Some(source)) = (fields.next(), fields.next(), fields.next())
    else {
        return Err(Error::Resolve(format!(
            "prism.lock: malformed row (want name{FIELD_SEP:?}hash{FIELD_SEP:?}source): {line:?}"
        )));
    };
    Ok(LockEntry {
        name: name.to_string(),
        hash: hash.to_string(),
        source: parse_source_field(source)?,
    })
}

fn parse_source_field(field: &str) -> Result<DepSource, Error> {
    let mut toks = field.split(TOKEN_SEP);
    let kind = toks.next().unwrap_or_default();
    let rest: Vec<&str> = toks.collect();
    match (kind, rest.as_slice()) {
        (SRC_PATH, [p]) => Ok(DepSource::Path((*p).into())),
        (SRC_GIT, [url, version]) => Ok(DepSource::Git {
            url: (*url).to_string(),
            version: (*version).to_string(),
        }),
        (SRC_HASH, [hex]) => Ok(DepSource::Hash((*hex).to_string())),
        _ => Err(Error::Resolve(format!(
            "prism.lock: unrecognized source field {field:?}"
        ))),
    }
}

// A field is unusable if it holds a separator; the whole-token check below points
// at which token.
fn reject_separators(field: &str) -> Result<(), Error> {
    if field.contains(FIELD_SEP) || field.contains(TOKEN_SEP) {
        return Err(Error::Resolve(format!(
            "prism.lock: field {field:?} contains a separator character"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn sample() -> Lock {
        let mut lock = Lock::default();
        lock.set(LockEntry {
            name: "http".to_string(),
            hash: "a3f9".to_string(),
            source: DepSource::Git {
                url: "github.com/x/http".to_string(),
                version: "2.0".to_string(),
            },
        });
        lock.set(LockEntry {
            name: "geo".to_string(),
            hash: "7c21".to_string(),
            source: DepSource::Path(PathBuf::from("../geo")),
        });
        lock.set(LockEntry {
            name: "crypto".to_string(),
            hash: "9f86".to_string(),
            source: DepSource::Hash("9f86".to_string()),
        });
        lock
    }

    #[test]
    fn write_read_round_trip() {
        let lock = sample();
        let text = lock.render().unwrap();
        assert_eq!(Lock::parse(&text).unwrap(), lock);
    }

    #[test]
    fn entries_are_sorted_and_headed() {
        let text = sample().render().unwrap();
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some(LOCK_HEADER));
        let names: Vec<&str> = lines.map(|l| l.split(FIELD_SEP).next().unwrap()).collect();
        assert_eq!(names, ["crypto", "geo", "http"]);
    }

    #[test]
    fn set_replaces_an_existing_pin() {
        let mut lock = sample();
        lock.set(LockEntry {
            name: "geo".to_string(),
            hash: "beef".to_string(),
            source: DepSource::Path(PathBuf::from("../geo2")),
        });
        assert_eq!(lock.get("geo").unwrap().hash, "beef");
        assert_eq!(lock.entries.len(), 3);
    }

    #[test]
    fn std_pin_round_trips_above_the_deps() {
        let mut lock = sample();
        lock.pin_std("deadbeef".to_string());
        let text = lock.render().unwrap();
        // The Std pin is the first line under the header, before any dependency.
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some(LOCK_HEADER));
        assert_eq!(lines.next(), Some("std\tdeadbeef"));
        assert_eq!(Lock::parse(&text).unwrap(), lock);
        assert_eq!(Lock::parse(&text).unwrap().std_root(), Some("deadbeef"));
    }

    #[test]
    fn a_lock_without_a_std_pin_is_unpinned() {
        let text = sample().render().unwrap();
        assert!(!text.contains("std\t"));
        assert_eq!(Lock::parse(&text).unwrap().std_root(), None);
    }

    #[test]
    fn a_missing_header_is_rejected() {
        assert!(Lock::parse("geo\t7c21\tpath ../geo\n").is_err());
    }

    #[test]
    fn a_token_with_a_space_is_refused_on_write() {
        let mut lock = Lock::default();
        lock.set(LockEntry {
            name: "bad".to_string(),
            hash: "00".to_string(),
            source: DepSource::Path(PathBuf::from("../a b")),
        });
        assert!(lock.render().is_err());
    }
}
