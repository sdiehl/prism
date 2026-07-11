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
//! prism-lock<TAB>v2
//! std<TAB><scheme><TAB><root-hash>
//! <name><TAB><scheme><TAB><root-hash><TAB><source>
//! ```
//!
//! The `<source>` field is space-tokenized, mirroring the store index's
//! within-field lists: `path <dir>`, `git <url> <tag>`, or `hash <hex>`. Names,
//! hashes, paths, urls, and tags contain neither a TAB nor a space, so both
//! separators are unambiguous; a token that would contain one is refused on write
//! rather than silently corrupting the file.

use std::fmt::Write as _;

use crate::core::HASH_SCHEME;
use crate::error::Error;
use crate::project::DepSource;

// The lock is its own format family, versioned independently of the store index
// files it is modeled on; the separators match theirs (TAB between fields, space
// within a field's list) but are declared here because this is a distinct file.
const LOCK_HEADER_V1: &str = "prism-lock\tv1";
const LOCK_HEADER: &str = "prism-lock\tv2";
const FIELD_SEP: char = '\t';
const TOKEN_SEP: char = ' ';

const SRC_PATH: &str = "path";
const SRC_GIT: &str = "git";
const SRC_HASH: &str = "hash";

// The reserved name of the standard-library pin. Unlike a dependency row, the
// Std pin has no `source` field: its bytes are the compiler's embedded stdlib,
// so the pin records the hash scheme and root hash the lockfile was resolved
// against. Written as a distinguished line under the reserved name `std` so it
// never collides with a dependency row, even one a project happened to name `std`.
const STD_ROOT_NAME: &str = "std";

/// The resolved pin of one dependency: its name, the root hash it resolved to,
/// and the source that hash was resolved from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockEntry {
    pub name: String,
    pub scheme: String,
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
    /// The hash scheme that gives `std_root` its meaning.
    pub std_scheme: Option<String>,
    pub entries: Vec<LockEntry>,
}

impl Lock {
    /// Check the standard library to `root`, the fold over the embedded stdlib. A
    /// build can then detect that its compiler ships a different Std than the one
    /// the lock was resolved against ([`crate::pkg::std_pin_status`]).
    pub fn pin_std(&mut self, root: String) {
        self.std_root = Some(root);
        self.std_scheme = Some(HASH_SCHEME.to_string());
    }

    /// The pinned standard-library root, if the lock records one.
    #[must_use]
    pub fn std_root(&self) -> Option<&str> {
        self.std_root.as_deref()
    }

    /// The hash scheme of the pinned standard-library root, if present.
    #[must_use]
    pub fn std_scheme(&self) -> Option<&str> {
        self.std_scheme.as_deref()
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

    /// Ensure every lockfile hash is expressed under the hash scheme this
    /// compiler understands.
    ///
    /// # Errors
    /// Fails when the Std pin or any dependency row names a foreign hash scheme.
    pub fn validate_current_scheme(&self) -> Result<(), Error> {
        if let Some(pinned) = self.std_root() {
            match self.std_scheme() {
                Some(HASH_SCHEME) => {}
                Some(scheme) => {
                    return Err(Error::ResolvePackage(format!(
                        "prism.lock pins Std root {pinned} under foreign hash scheme {scheme}; \
                         this build speaks {HASH_SCHEME}"
                    )));
                }
                None => {
                    return Err(Error::ResolvePackage(format!(
                        "prism.lock pins Std root {pinned} without a hash scheme; this build \
                         speaks {HASH_SCHEME}"
                    )));
                }
            }
        }
        for entry in &self.entries {
            if entry.scheme != HASH_SCHEME {
                return Err(Error::ResolvePackage(format!(
                    "prism.lock pins dependency `{}` under foreign hash scheme {}; this build \
                     speaks {HASH_SCHEME}",
                    entry.name, entry.scheme
                )));
            }
        }
        Ok(())
    }

    /// Parse a `prism.lock` document.
    ///
    /// # Errors
    /// Fails on a missing or wrong header, a malformed row, or an unrecognized
    /// source token.
    pub fn parse(text: &str) -> Result<Self, Error> {
        let mut lines = text.lines();
        let header = lines.next();
        if header != Some(LOCK_HEADER_V1) && header != Some(LOCK_HEADER) {
            return Err(Error::ResolvePackage(format!(
                "prism.lock: missing or unrecognized header (expected {LOCK_HEADER:?})"
            )));
        }
        let mut std_root = None;
        let mut std_scheme = None;
        let mut entries = Vec::new();
        for line in lines.filter(|l| !l.trim().is_empty()) {
            let fields: Vec<&str> = line.split(FIELD_SEP).collect();
            match (header, fields.as_slice()) {
                (Some(LOCK_HEADER_V1), [name, hash]) if *name == STD_ROOT_NAME => {
                    std_scheme = Some(HASH_SCHEME.to_string());
                    std_root = Some((*hash).to_string());
                    continue;
                }
                (Some(LOCK_HEADER), [name, scheme, hash]) if *name == STD_ROOT_NAME => {
                    std_scheme = Some((*scheme).to_string());
                    std_root = Some((*hash).to_string());
                    continue;
                }
                _ => {}
            }
            entries.push(parse_row(header, line)?);
        }
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(Self {
            std_root,
            std_scheme,
            entries,
        })
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
            let scheme = self.std_scheme.as_deref().unwrap_or(HASH_SCHEME);
            reject_separators(scheme)?;
            reject_separators(root)?;
            let _ = writeln!(out, "{STD_ROOT_NAME}{FIELD_SEP}{scheme}{FIELD_SEP}{root}");
        }
        for e in &self.entries {
            let source = source_field(&e.source)?;
            reject_separators(&e.name)?;
            reject_separators(&e.scheme)?;
            reject_separators(&e.hash)?;
            let _ = writeln!(
                out,
                "{}{FIELD_SEP}{}{FIELD_SEP}{}{FIELD_SEP}{source}",
                e.name, e.scheme, e.hash
            );
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

fn parse_row(header: Option<&str>, line: &str) -> Result<LockEntry, Error> {
    let fields: Vec<&str> = line.splitn(4, FIELD_SEP).collect();
    match (header, fields.as_slice()) {
        (Some(LOCK_HEADER_V1), [name, hash, source]) => Ok(LockEntry {
            name: (*name).to_string(),
            scheme: HASH_SCHEME.to_string(),
            hash: (*hash).to_string(),
            source: parse_source_field(source)?,
        }),
        (Some(LOCK_HEADER), [name, scheme, hash, source]) => Ok(LockEntry {
            name: (*name).to_string(),
            scheme: (*scheme).to_string(),
            hash: (*hash).to_string(),
            source: parse_source_field(source)?,
        }),
        _ => Err(Error::ResolvePackage(format!(
            "prism.lock: malformed row (want name{FIELD_SEP:?}scheme{FIELD_SEP:?}hash{FIELD_SEP:?}source): {line:?}"
        ))),
    }
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
        _ => Err(Error::ResolvePackage(format!(
            "prism.lock: unrecognized source field {field:?}"
        ))),
    }
}

// A field is unusable if it holds a separator; the whole-token check below points
// at which token.
fn reject_separators(field: &str) -> Result<(), Error> {
    if field.contains(FIELD_SEP) || field.contains(TOKEN_SEP) {
        return Err(Error::ResolvePackage(format!(
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
            scheme: HASH_SCHEME.to_string(),
            hash: "a3f9".to_string(),
            source: DepSource::Git {
                url: "github.com/x/http".to_string(),
                version: "2.0".to_string(),
            },
        });
        lock.set(LockEntry {
            name: "geo".to_string(),
            scheme: HASH_SCHEME.to_string(),
            hash: "7c21".to_string(),
            source: DepSource::Path(PathBuf::from("../geo")),
        });
        lock.set(LockEntry {
            name: "crypto".to_string(),
            scheme: HASH_SCHEME.to_string(),
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
            scheme: HASH_SCHEME.to_string(),
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
        let expected_std = format!("std\t{HASH_SCHEME}\tdeadbeef");
        assert_eq!(lines.next(), Some(expected_std.as_str()));
        assert_eq!(Lock::parse(&text).unwrap(), lock);
        assert_eq!(Lock::parse(&text).unwrap().std_root(), Some("deadbeef"));
        assert_eq!(Lock::parse(&text).unwrap().std_scheme(), Some(HASH_SCHEME));
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
            scheme: HASH_SCHEME.to_string(),
            hash: "00".to_string(),
            source: DepSource::Path(PathBuf::from("../a b")),
        });
        assert!(lock.render().is_err());
    }

    #[test]
    fn legacy_v1_rows_parse_as_current_scheme() {
        let text = "prism-lock\tv1\nstd\tdeadbeef\ngeo\t7c21\tpath ../geo\n";
        let lock = Lock::parse(text).unwrap();
        assert_eq!(lock.std_root(), Some("deadbeef"));
        assert_eq!(lock.std_scheme(), Some(HASH_SCHEME));
        let geo = lock.get("geo").unwrap();
        assert_eq!(geo.scheme, HASH_SCHEME);
        assert_eq!(geo.hash, "7c21");
        lock.validate_current_scheme().unwrap();
    }

    #[test]
    fn current_scheme_validation_rejects_foreign_std() {
        let text = "prism-lock\tv2\nstd\tfuture-scheme\tdeadbeef\n";
        let lock = Lock::parse(text).unwrap();
        let err = lock.validate_current_scheme().unwrap_err().to_string();
        assert!(err.contains("Std root"));
        assert!(err.contains("future-scheme"));
    }

    #[test]
    fn current_scheme_validation_rejects_foreign_dependency() {
        let text = "prism-lock\tv2\ngeo\tfuture-scheme\t7c21\tpath ../geo\n";
        let lock = Lock::parse(text).unwrap();
        let err = lock.validate_current_scheme().unwrap_err().to_string();
        assert!(err.contains("dependency `geo`"));
        assert!(err.contains("future-scheme"));
    }
}
