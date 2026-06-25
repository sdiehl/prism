//! Project manifest (`prism.toml`) discovery and parsing.
//!
//! A project is a directory holding a `prism.toml` and a source tree under
//! `src/`. Module dotted paths resolve from the source root, not from the entry
//! file's own directory, so an entry nested anywhere under `src/` still sees the
//! same module namespace.

use std::path::{Path, PathBuf};

use crate::error::Error;

/// The manifest filename a project is keyed by.
const MANIFEST: &str = "prism.toml";

/// A parsed `prism.toml`:
///
/// ```toml
/// [package]
/// name = "myproj"
///
/// [bin]
/// entry = "src/main.pr"
/// ```
#[derive(Debug, Clone)]
pub struct Manifest {
    pub name: String,
    /// `[bin] entry`, relative to the project root.
    pub entry: PathBuf,
    /// Module root, relative to the project root (`[package] src`, default `src`).
    pub src_dir: PathBuf,
}

impl Manifest {
    /// Parse the text of a `prism.toml`.
    ///
    /// # Errors
    /// Fails on malformed TOML or a missing/ill-typed `name` or `[bin] entry`.
    pub fn parse(text: &str) -> Result<Self, Error> {
        let table: toml::Table =
            toml::from_str(text).map_err(|e| Error::Resolve(format!("prism.toml: {e}")))?;
        let pkg = table
            .get("package")
            .and_then(toml::Value::as_table)
            .ok_or_else(|| Error::Resolve("prism.toml: missing [package] table".into()))?;
        let name = pkg
            .get("name")
            .and_then(toml::Value::as_str)
            .ok_or_else(|| Error::Resolve("prism.toml: [package] name must be a string".into()))?
            .to_string();
        let entry = table
            .get("bin")
            .and_then(toml::Value::as_table)
            .and_then(|b| b.get("entry"))
            .and_then(toml::Value::as_str)
            .ok_or_else(|| Error::Resolve("prism.toml: [bin] entry must be a string".into()))?;
        let src_dir = pkg
            .get("src")
            .and_then(toml::Value::as_str)
            .unwrap_or("src");
        Ok(Self {
            name,
            entry: PathBuf::from(entry),
            src_dir: PathBuf::from(src_dir),
        })
    }
}

/// A located project: the manifest resolved against its root directory.
#[derive(Debug, Clone)]
pub struct Project {
    pub root: PathBuf,
    pub name: String,
    /// The base for module resolution (`root/src`).
    pub src_dir: PathBuf,
    /// The program to compile (`root/<entry>`).
    pub entry: PathBuf,
}

/// Walk up from `start` looking for the nearest enclosing `prism.toml`.
#[must_use]
pub fn find_manifest(start: &Path) -> Option<PathBuf> {
    let mut dir: &Path = if start.is_file() {
        start.parent()?
    } else {
        start
    };
    loop {
        let candidate = dir.join(MANIFEST);
        if candidate.is_file() {
            return Some(candidate);
        }
        dir = dir.parent()?;
    }
}

/// Load the project rooted at `arg`, which may be a project directory or a
/// `prism.toml` path.
///
/// # Errors
/// Fails when the manifest cannot be read or is malformed.
pub fn load_project(arg: &Path) -> Result<Project, Error> {
    let manifest_path = if arg.is_dir() {
        arg.join(MANIFEST)
    } else {
        arg.to_path_buf()
    };
    let text = std::fs::read_to_string(&manifest_path)?;
    let manifest = Manifest::parse(&text)?;
    let root = manifest_path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    Ok(Project {
        src_dir: root.join(&manifest.src_dir),
        entry: root.join(&manifest.entry),
        name: manifest.name,
        root,
    })
}

#[cfg(test)]
mod tests {
    use super::Manifest;

    #[test]
    fn parses_name_entry_and_default_src() {
        let m = Manifest::parse("[package]\nname = \"demo\"\n\n[bin]\nentry = \"src/main.pr\"\n")
            .unwrap();
        assert_eq!(m.name, "demo");
        assert_eq!(m.entry.to_str(), Some("src/main.pr"));
        assert_eq!(m.src_dir.to_str(), Some("src"));
    }

    #[test]
    fn missing_entry_is_an_error() {
        assert!(Manifest::parse("[package]\nname = \"demo\"\n").is_err());
    }
}
