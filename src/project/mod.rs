//! Project manifest (`prism.toml`) discovery and parsing.
//!
//! A project is a directory holding a `prism.toml` and a source tree under
//! `src/`. Module dotted paths resolve from the source root, not from the entry
//! file's own directory, so an entry nested anywhere under `src/` still sees the
//! same module namespace.

use std::path::{Path, PathBuf};

use crate::core::HASH_SCHEME;
use crate::error::Error;
use crate::flags::DynFlags;

/// The manifest filename a project is keyed by.
pub(crate) const MANIFEST: &str = "prism.toml";

/// Separator between the hash scheme and the hex digest in a bare hash-pin
/// dependency (`<scheme>:<hex>`). The scheme itself is never re-spelled here; it
/// is [`HASH_SCHEME`], so a pin string and every store key agree on one tag.
const HASH_PIN_SEP: char = ':';

/// Render a content hash as a bare hash-pin dependency string,
/// `<HASH_SCHEME>:<hex>`. The one place the pin surface syntax is spelled.
#[must_use]
pub fn hash_pin(hex: &str) -> String {
    format!("{HASH_SCHEME}{HASH_PIN_SEP}{hex}")
}

/// The hex digest of a bare hash-pin string `<HASH_SCHEME>:<hex>`.
///
/// `None` when the string is not a pin under the canonical scheme (a plain path
/// string, or a pin under some other scheme this build does not speak). The
/// inverse of [`hash_pin`].
#[must_use]
pub fn parse_hash_pin(s: &str) -> Option<&str> {
    let (scheme, hex) = s.split_once(HASH_PIN_SEP)?;
    let hex_ok = !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit());
    (scheme == HASH_SCHEME && hex_ok).then_some(hex)
}

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
    /// Optional `[package] prelude`, a path (relative to the root) whose contents
    /// replace the built-in prelude for this project. Absent uses the built-in.
    pub prelude: Option<PathBuf>,
    /// `[dependencies]` entries: each maps a dependency name to where its code
    /// comes from (a local path, a git release named by an opaque tag, or a bare
    /// content-hash pin).
    pub dependencies: Vec<Dependency>,
}

/// One `[dependencies]` entry: a name and the source its code resolves from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dependency {
    pub name: String,
    pub source: DepSource,
}

/// Where a dependency's code comes from.
///
/// Every form resolves to a single content hash before a build; the three differ
/// only in how that hash is named. A version is always an opaque label, never a
/// range: coexistence is by hash, so there is nothing to solve.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DepSource {
    /// A local path dependency: another Prism project whose modules resolve under
    /// its own source root. `path` is relative to the depending project's root.
    Path(PathBuf),
    /// A git-hosted release at `url`, pinned to the opaque tag `version`. The URL
    /// and tag are the package identity the signed index maps to a root hash; the
    /// tag carries no range or ordering semantics.
    Git { url: String, version: String },
    /// A fully explicit content-hash pin (the hex digest under [`HASH_SCHEME`]).
    /// Terminal: the hash is the identity, so nothing about it is re-resolved.
    Hash(String),
}

impl Manifest {
    /// Parse the text of a `prism.toml`.
    ///
    /// # Errors
    /// Fails on malformed TOML or a missing/ill-typed `name` or `[bin] entry`.
    pub fn parse(text: &str) -> Result<Self, Error> {
        let table: toml::Table =
            toml::from_str(text).map_err(|e| Error::ResolveProject(format!("prism.toml: {e}")))?;
        let pkg = table
            .get("package")
            .and_then(toml::Value::as_table)
            .ok_or_else(|| Error::ResolveProject("prism.toml: missing [package] table".into()))?;
        let name = pkg
            .get("name")
            .and_then(toml::Value::as_str)
            .ok_or_else(|| {
                Error::ResolveProject("prism.toml: [package] name must be a string".into())
            })?
            .to_string();
        let entry = table
            .get("bin")
            .and_then(toml::Value::as_table)
            .and_then(|b| b.get("entry"))
            .and_then(toml::Value::as_str)
            .ok_or_else(|| {
                Error::ResolveProject("prism.toml: [bin] entry must be a string".into())
            })?;
        let src_dir = pkg
            .get("src")
            .and_then(toml::Value::as_str)
            .unwrap_or("src");
        let prelude = pkg
            .get("prelude")
            .and_then(toml::Value::as_str)
            .map(PathBuf::from);
        let dependencies = Self::parse_deps(&table)?;
        Ok(Self {
            name,
            entry: PathBuf::from(entry),
            src_dir: PathBuf::from(src_dir),
            prelude,
            dependencies,
        })
    }

    // `[dependencies]` is a table of `name = <source>`. Three source forms:
    // `{ path = ".." }` (or a bare path string), `{ git = "..", version = ".." }`,
    // and a bare hash-pin string `<scheme>:<hex>`. Anything else is rejected so a
    // typo cannot silently drop a dependency.
    fn parse_deps(table: &toml::Table) -> Result<Vec<Dependency>, Error> {
        let Some(deps) = table.get("dependencies") else {
            return Ok(Vec::new());
        };
        let deps = deps.as_table().ok_or_else(|| {
            Error::ResolveProject("prism.toml: [dependencies] must be a table".into())
        })?;
        deps.iter()
            .map(|(name, val)| {
                Ok(Dependency {
                    name: name.clone(),
                    source: parse_dep_source(name, val)?,
                })
            })
            .collect()
    }
}

// The source of one `[dependencies]` entry. A bare string is a hash pin when it
// carries the canonical scheme prefix, otherwise the path shorthand; a table
// selects on its key (`git` before `path`, since a git dep also names a version).
fn parse_dep_source(name: &str, val: &toml::Value) -> Result<DepSource, Error> {
    match val {
        toml::Value::String(s) => Ok(parse_hash_pin(s).map_or_else(
            || DepSource::Path(PathBuf::from(s)),
            |hex| DepSource::Hash(hex.to_string()),
        )),
        toml::Value::Table(t) => {
            if let Some(url) = t.get("git").and_then(toml::Value::as_str) {
                let version = t
                    .get("version")
                    .and_then(toml::Value::as_str)
                    .ok_or_else(|| {
                        Error::ResolveProject(format!(
                            "prism.toml: git dependency `{name}` needs a `version` tag"
                        ))
                    })?;
                Ok(DepSource::Git {
                    url: url.to_string(),
                    version: version.to_string(),
                })
            } else if let Some(path) = t.get("path").and_then(toml::Value::as_str) {
                Ok(DepSource::Path(PathBuf::from(path)))
            } else {
                Err(Error::ResolveProject(format!(
                    "prism.toml: dependency `{name}` must set `path`, `git` (with `version`), \
                     or be a `{HASH_SCHEME}:<hex>` pin string"
                )))
            }
        }
        _ => Err(Error::ResolveProject(format!(
            "prism.toml: dependency `{name}` must be a path/pin string or an inline table"
        ))),
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
    /// A project-supplied prelude file (`root/<prelude>`) that replaces the
    /// built-in one, or `None` to use the built-in prelude.
    pub prelude: Option<PathBuf>,
    /// The source root of each path dependency, resolved against this project's
    /// root and that dependency's own manifest (its `src_dir`). These extend the
    /// module search path, so a dependency's modules resolve under its own root.
    pub dep_src_dirs: Vec<PathBuf>,
    /// The manifest dependencies in source order. Path dependencies are already
    /// expanded into `dep_src_dirs`; hash and git dependencies are resolved from
    /// the package store by the CLI build path.
    pub dependencies: Vec<Dependency>,
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

/// Overlay the enclosing project's `[flags]` table onto `base`.
///
/// Walks up from `start` for a `prism.toml` and applies only its `[flags]` table
/// (the toml precedence layer, below the environment and CLI). Reading the flags
/// is deliberately decoupled from full manifest validity: a bare `prism check
/// file.pr` in a directory whose `prism.toml` carries only `[flags]` (no
/// `[package]`/`[bin]`) still honors those flags. A manifest that cannot be found
/// or read, or whose TOML does not parse, or whose `[flags]` is not a table, leaves
/// `base` untouched (any real structural error is reported by the command's own
/// project load); only a bad value *inside* `[flags]` is surfaced here, so a flag
/// typo is never silently dropped.
#[must_use]
pub fn flag_overrides(start: &Path, base: DynFlags) -> DynFlags {
    let Some(manifest_path) = find_manifest(start) else {
        return base;
    };
    let Ok(text) = std::fs::read_to_string(&manifest_path) else {
        return base;
    };
    let Ok(table) = text.parse::<toml::Table>() else {
        return base;
    };
    let Some(flags_table) = table.get("flags").and_then(toml::Value::as_table) else {
        return base;
    };
    let mut flags = base;
    if let Err(msg) = flags.apply_toml(flags_table) {
        eprintln!("{msg}");
    }
    flags
}

/// Load the project rooted at `arg`, which may be a project directory or a
/// `prism.toml` path.
///
/// # Errors
/// Fails when the manifest cannot be read or is malformed.
pub fn load_project(arg: &Path) -> Result<Project, Error> {
    load_project_rec(arg, &mut Vec::new())
}

// `visiting` is the stack of manifests currently being resolved (by canonical
// path), so a dependency edge back into one already on the stack is reported as
// a cycle instead of recursing until the native stack overflows.
fn load_project_rec(arg: &Path, visiting: &mut Vec<PathBuf>) -> Result<Project, Error> {
    let manifest_path = if arg.is_dir() {
        arg.join(MANIFEST)
    } else {
        arg.to_path_buf()
    };
    // Canonicalize so `../geo` and `geo` name the same node; fall back to the raw
    // path if the file cannot be canonicalized (the read below reports it).
    let key = manifest_path
        .canonicalize()
        .unwrap_or_else(|_| manifest_path.clone());
    if visiting.contains(&key) {
        return Err(Error::ResolveProject(format!(
            "dependency cycle through `{}`",
            manifest_path.display()
        )));
    }
    let text = std::fs::read_to_string(&manifest_path)?;
    let manifest = Manifest::parse(&text)?;
    let root = manifest_path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    // Resolve each path dependency to its own project and collect its source
    // root, plus (transitively) the source roots of its own dependencies, so a
    // diamond of path deps still resolves. Each dep's `src_dir` honours that
    // dependency's own manifest.
    visiting.push(key);
    let mut dep_src_dirs = Vec::new();
    for dep in &manifest.dependencies {
        // Only path dependencies extend the module search path; git and hash
        // dependencies resolve through the store from their locked root hash (the
        // resolver seam), not from a source directory on disk.
        let DepSource::Path(rel) = &dep.source else {
            continue;
        };
        let dep_proj = load_project_rec(&root.join(rel), visiting)
            .map_err(|e| Error::ResolveProject(format!("dependency `{}`: {e}", dep.name)))?;
        dep_src_dirs.push(dep_proj.src_dir);
        for d in dep_proj.dep_src_dirs {
            if !dep_src_dirs.contains(&d) {
                dep_src_dirs.push(d);
            }
        }
    }
    visiting.pop();
    Ok(Project {
        src_dir: root.join(&manifest.src_dir),
        entry: root.join(&manifest.entry),
        prelude: manifest.prelude.map(|p| root.join(p)),
        name: manifest.name,
        dep_src_dirs,
        dependencies: manifest.dependencies,
        root,
    })
}

#[cfg(test)]
mod tests {
    use super::{hash_pin, parse_hash_pin, DepSource, Manifest};
    use std::path::PathBuf;

    #[test]
    fn parses_name_entry_and_default_src() {
        let m = Manifest::parse("[package]\nname = \"demo\"\n\n[bin]\nentry = \"src/main.pr\"\n")
            .unwrap();
        assert_eq!(m.name, "demo");
        assert_eq!(m.entry.to_str(), Some("src/main.pr"));
        assert_eq!(m.src_dir.to_str(), Some("src"));
        assert_eq!(m.prelude, None);
    }

    #[test]
    fn parses_prelude_override() {
        let m = Manifest::parse(
            "[package]\nname = \"demo\"\nprelude = \"src/Prelude.pr\"\n\n[bin]\nentry = \"src/main.pr\"\n",
        )
        .unwrap();
        assert_eq!(
            m.prelude.as_deref().and_then(|p| p.to_str()),
            Some("src/Prelude.pr")
        );
    }

    #[test]
    fn parses_path_dependencies_both_forms() {
        let m = Manifest::parse(
            "[package]\nname = \"app\"\n\n[bin]\nentry = \"src/main.pr\"\n\n\
             [dependencies]\ngeo = { path = \"../geo\" }\nutil = \"../util\"\n",
        )
        .unwrap();
        let mut deps: Vec<_> = m
            .dependencies
            .iter()
            .map(|d| (d.name.as_str(), d.source.clone()))
            .collect();
        deps.sort_by(|a, b| a.0.cmp(b.0));
        assert_eq!(
            deps,
            [
                ("geo", DepSource::Path(PathBuf::from("../geo"))),
                ("util", DepSource::Path(PathBuf::from("../util"))),
            ]
        );
    }

    #[test]
    fn parses_git_and_hash_dependency_forms() {
        let pin = hash_pin("9f86d081");
        let text = format!(
            "[package]\nname = \"app\"\n\n[bin]\nentry = \"src/main.pr\"\n\n\
             [dependencies]\n\
             http = {{ git = \"github.com/prism-lang/http\", version = \"2.0\" }}\n\
             crypto = \"{pin}\"\n"
        );
        let m = Manifest::parse(&text).unwrap();
        let mut deps: Vec<_> = m
            .dependencies
            .iter()
            .map(|d| (d.name.as_str(), d.source.clone()))
            .collect();
        deps.sort_by(|a, b| a.0.cmp(b.0));
        assert_eq!(
            deps,
            [
                ("crypto", DepSource::Hash("9f86d081".to_string())),
                (
                    "http",
                    DepSource::Git {
                        url: "github.com/prism-lang/http".to_string(),
                        version: "2.0".to_string(),
                    }
                ),
            ]
        );
    }

    #[test]
    fn hash_pin_round_trips_and_rejects_foreign_schemes() {
        assert_eq!(parse_hash_pin(&hash_pin("abc123")), Some("abc123"));
        // A path string is not a pin; a pin under another scheme is not ours.
        assert_eq!(parse_hash_pin("../util"), None);
        assert_eq!(parse_hash_pin("sha256:9f86"), None);
        // A pin with a non-hex digest is rejected rather than misread as a pin.
        assert_eq!(parse_hash_pin(&hash_pin("nothex!")), None);
    }

    #[test]
    fn git_dependency_without_version_is_an_error() {
        assert!(Manifest::parse(
            "[package]\nname = \"a\"\n\n[bin]\nentry = \"s.pr\"\n\n[dependencies]\nx = { git = \"g/h\" }\n",
        )
        .is_err());
    }

    #[test]
    fn dependency_with_no_recognised_key_is_an_error() {
        assert!(Manifest::parse(
            "[package]\nname = \"a\"\n\n[bin]\nentry = \"s.pr\"\n\n[dependencies]\nx = { version = \"1\" }\n",
        )
        .is_err());
    }

    #[test]
    fn missing_entry_is_an_error() {
        assert!(Manifest::parse("[package]\nname = \"demo\"\n").is_err());
    }
}
