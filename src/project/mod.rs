//! Project manifest (`prism.toml`) discovery and parsing.
//!
//! A project is a directory holding a `prism.toml` and a source tree under
//! `src/`. Module dotted paths resolve from the source root, not from the entry
//! file's own directory, so an entry nested anywhere under `src/` still sees the
//! same module namespace.

use std::collections::BTreeSet;
use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use crate::core::HASH_SCHEME;
use crate::error::Error;
use crate::flags::DynFlags;

/// The manifest filename a project is keyed by.
pub(crate) const MANIFEST: &str = "prism.toml";

/// The lockfile filename beside that manifest, pinning every dependency.
pub(crate) const LOCKFILE: &str = "prism.lock";

/// Separator between the hash scheme and the hex digest in a bare hash-pin
/// dependency (`<scheme>:<hex>`). The scheme itself is never re-spelled here; it
/// is [`HASH_SCHEME`], so a pin string and every store key agree on one tag.
const HASH_PIN_SEP: char = ':';

/// One supported SPDX license identifier.
///
/// Prism deliberately accepts a single identifier rather than a free-form SPDX
/// expression. That keeps dependency-license audits finite and typo-proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum License {
    /// `MIT`.
    Mit,
    /// `MIT-0`.
    Mit0,
    /// `Apache-2.0`.
    Apache2,
    /// `Apache-2.0 WITH LLVM-exception`.
    Apache2WithLlvmException,
    /// `BSD-2-Clause`.
    Bsd2Clause,
    /// `BSD-3-Clause`.
    Bsd3Clause,
    /// `GPL-2.0-only`.
    Gpl2Only,
    /// `GPL-2.0-or-later`.
    Gpl2OrLater,
    /// `GPL-3.0-only`.
    Gpl3Only,
    /// `GPL-3.0-or-later`.
    Gpl3OrLater,
    /// `LGPL-2.1-only`.
    Lgpl21Only,
    /// `LGPL-2.1-or-later`.
    Lgpl21OrLater,
    /// `LGPL-3.0-only`.
    Lgpl3Only,
    /// `LGPL-3.0-or-later`.
    Lgpl3OrLater,
    /// `AGPL-3.0-only`.
    Agpl3Only,
    /// `AGPL-3.0-or-later`.
    Agpl3OrLater,
    /// `MPL-2.0`.
    Mpl2,
    /// `EPL-2.0`.
    Epl2,
    /// `CDDL-1.0`.
    Cddl1,
    /// `ISC`.
    Isc,
    /// `Zlib`.
    Zlib,
    /// `BSL-1.0`.
    Bsl1,
    /// `CC0-1.0`.
    Cc0,
    /// `Unlicense`.
    Unlicense,
}

impl License {
    /// The canonical SPDX spelling written to manifests and audit reports.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Mit => "MIT",
            Self::Mit0 => "MIT-0",
            Self::Apache2 => "Apache-2.0",
            Self::Apache2WithLlvmException => "Apache-2.0 WITH LLVM-exception",
            Self::Bsd2Clause => "BSD-2-Clause",
            Self::Bsd3Clause => "BSD-3-Clause",
            Self::Gpl2Only => "GPL-2.0-only",
            Self::Gpl2OrLater => "GPL-2.0-or-later",
            Self::Gpl3Only => "GPL-3.0-only",
            Self::Gpl3OrLater => "GPL-3.0-or-later",
            Self::Lgpl21Only => "LGPL-2.1-only",
            Self::Lgpl21OrLater => "LGPL-2.1-or-later",
            Self::Lgpl3Only => "LGPL-3.0-only",
            Self::Lgpl3OrLater => "LGPL-3.0-or-later",
            Self::Agpl3Only => "AGPL-3.0-only",
            Self::Agpl3OrLater => "AGPL-3.0-or-later",
            Self::Mpl2 => "MPL-2.0",
            Self::Epl2 => "EPL-2.0",
            Self::Cddl1 => "CDDL-1.0",
            Self::Isc => "ISC",
            Self::Zlib => "Zlib",
            Self::Bsl1 => "BSL-1.0",
            Self::Cc0 => "CC0-1.0",
            Self::Unlicense => "Unlicense",
        }
    }
}

impl fmt::Display for License {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for License {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "MIT" => Ok(Self::Mit),
            "MIT-0" => Ok(Self::Mit0),
            "Apache-2.0" => Ok(Self::Apache2),
            "Apache-2.0 WITH LLVM-exception" => Ok(Self::Apache2WithLlvmException),
            "BSD-2-Clause" => Ok(Self::Bsd2Clause),
            "BSD-3-Clause" => Ok(Self::Bsd3Clause),
            "GPL-2.0-only" => Ok(Self::Gpl2Only),
            "GPL-2.0-or-later" => Ok(Self::Gpl2OrLater),
            "GPL-3.0-only" => Ok(Self::Gpl3Only),
            "GPL-3.0-or-later" => Ok(Self::Gpl3OrLater),
            "LGPL-2.1-only" => Ok(Self::Lgpl21Only),
            "LGPL-2.1-or-later" => Ok(Self::Lgpl21OrLater),
            "LGPL-3.0-only" => Ok(Self::Lgpl3Only),
            "LGPL-3.0-or-later" => Ok(Self::Lgpl3OrLater),
            "AGPL-3.0-only" => Ok(Self::Agpl3Only),
            "AGPL-3.0-or-later" => Ok(Self::Agpl3OrLater),
            "MPL-2.0" => Ok(Self::Mpl2),
            "EPL-2.0" => Ok(Self::Epl2),
            "CDDL-1.0" => Ok(Self::Cddl1),
            "ISC" => Ok(Self::Isc),
            "Zlib" => Ok(Self::Zlib),
            "BSL-1.0" => Ok(Self::Bsl1),
            "CC0-1.0" => Ok(Self::Cc0),
            "Unlicense" => Ok(Self::Unlicense),
            _ => Err(format!("unsupported SPDX license identifier `{value}`")),
        }
    }
}

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
/// version = "0.1.0"
/// authors = ["A. Developer <dev@example.com>"]
/// maintainers = ["dev@example.com"]
/// license = "MIT"
/// description = "What the package provides."
///
/// [bin]
/// entry = "src/main.pr"
/// ```
#[derive(Debug, Clone)]
pub struct Manifest {
    pub name: String,
    /// Required package release label. It is metadata, not dependency identity:
    /// builds and locks still resolve packages by content hash.
    pub version: String,
    /// Required package authors, in display form (`Name <email>` by convention).
    pub authors: Vec<String>,
    /// Required current maintainer contacts.
    pub maintainers: Vec<String>,
    /// Required license from Prism's supported SPDX identifier set.
    pub license: License,
    /// Optional package summary rendered at the top of generated API docs.
    pub description: Option<String>,
    /// Optional project and support URLs.
    pub homepage: Option<String>,
    /// Optional issue-tracker URL.
    pub issues: Option<String>,
    /// Optional published API-documentation URL.
    pub online_doc: Option<String>,
    /// Optional source repository, conventionally a `git+https` URL.
    pub repo: Option<String>,
    /// Optional package-relative documentation and legal files.
    pub changes_files: Vec<PathBuf>,
    /// Optional package-relative license files.
    pub license_files: Vec<PathBuf>,
    /// Optional package-relative readme files.
    pub readme_files: Vec<PathBuf>,
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
    /// Fails on malformed TOML, missing or ill-typed required package metadata,
    /// an ill-typed optional metadata field, or a missing `[bin] entry`.
    pub fn parse(text: &str) -> Result<Self, Error> {
        let table: toml::Table =
            toml::from_str(text).map_err(|e| Error::ResolveProject(format!("prism.toml: {e}")))?;
        let pkg = table
            .get("package")
            .and_then(toml::Value::as_table)
            .ok_or_else(|| Error::ResolveProject("prism.toml: missing [package] table".into()))?;
        let name = required_package_string(pkg, "name")?;
        let version = required_package_string(pkg, "version")?;
        let authors = required_package_strings(pkg, "authors")?;
        let maintainers = required_package_strings(pkg, "maintainers")?;
        let license_text = required_package_string(pkg, "license")?;
        let license = License::from_str(&license_text).map_err(|msg| {
            Error::ResolveProject(format!("prism.toml: [package] license: {msg}"))
        })?;
        let description = optional_package_string(pkg, "description")?;
        let homepage = optional_package_string(pkg, "homepage")?;
        let issues = optional_package_string(pkg, "issues")?;
        let online_doc = optional_package_string(pkg, "online-doc")?;
        let repo = optional_package_string(pkg, "repo")?;
        let changes_files = optional_package_paths(pkg, "changes-files")?;
        let license_files = optional_package_paths(pkg, "license-files")?;
        let readme_files = optional_package_paths(pkg, "readme-files")?;
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
            version,
            authors,
            maintainers,
            license,
            description,
            homepage,
            issues,
            online_doc,
            repo,
            changes_files,
            license_files,
            readme_files,
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

// One required scalar in `[package]`. Empty metadata is as absent as a missing
// key: it cannot identify a release, license, or person to a package consumer.
fn required_package_string(pkg: &toml::Table, key: &str) -> Result<String, Error> {
    match pkg.get(key).and_then(toml::Value::as_str) {
        Some(value) if !value.trim().is_empty() => Ok(value.to_string()),
        _ => Err(Error::ResolveProject(format!(
            "prism.toml: [package] {key} must be a non-empty string"
        ))),
    }
}

// One optional scalar in `[package]`; present values still have to be useful.
fn optional_package_string(pkg: &toml::Table, key: &str) -> Result<Option<String>, Error> {
    pkg.get(key)
        .map(|value| match value.as_str() {
            Some(value) if !value.trim().is_empty() => Ok(value.to_string()),
            _ => Err(Error::ResolveProject(format!(
                "prism.toml: [package] {key} must be a non-empty string"
            ))),
        })
        .transpose()
}

// Required people fields are non-empty arrays of non-empty strings. An array
// keeps multiple authors and maintainers structured instead of inventing a
// delimiter inside one scalar.
fn required_package_strings(pkg: &toml::Table, key: &str) -> Result<Vec<String>, Error> {
    let Some(values) = pkg.get(key).and_then(toml::Value::as_array) else {
        return Err(Error::ResolveProject(format!(
            "prism.toml: [package] {key} must be a non-empty array of strings"
        )));
    };
    let parsed: Option<Vec<String>> = values
        .iter()
        .map(|value| {
            value
                .as_str()
                .filter(|s| !s.trim().is_empty())
                .map(str::to_string)
        })
        .collect();
    match parsed {
        Some(parsed) if !parsed.is_empty() => Ok(parsed),
        _ => Err(Error::ResolveProject(format!(
            "prism.toml: [package] {key} must be a non-empty array of strings"
        ))),
    }
}

// Optional file lists use the same array discipline and remain relative paths;
// the package tool that consumes one decides when the file must exist.
fn optional_package_paths(pkg: &toml::Table, key: &str) -> Result<Vec<PathBuf>, Error> {
    let Some(value) = pkg.get(key) else {
        return Ok(Vec::new());
    };
    let Some(values) = value.as_array() else {
        return Err(Error::ResolveProject(format!(
            "prism.toml: [package] {key} must be an array of non-empty strings"
        )));
    };
    values
        .iter()
        .map(|value| match value.as_str() {
            Some(path) if !path.trim().is_empty() => Ok(PathBuf::from(path)),
            _ => Err(Error::ResolveProject(format!(
                "prism.toml: [package] {key} must be an array of non-empty strings"
            ))),
        })
        .collect()
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
    /// Package release and ownership metadata from `[package]`.
    pub version: String,
    /// Package authors from `[package]`.
    pub authors: Vec<String>,
    /// Current maintainer contacts from `[package]`.
    pub maintainers: Vec<String>,
    /// Validated SPDX license identifier from `[package]`.
    pub license: License,
    /// The optional `[package] description`, used by package-facing tools.
    pub description: Option<String>,
    /// Optional project homepage.
    pub homepage: Option<String>,
    /// Optional issue tracker.
    pub issues: Option<String>,
    /// Optional published documentation.
    pub online_doc: Option<String>,
    /// Optional source repository.
    pub repo: Option<String>,
    /// Located changelog files, resolved against the project root.
    pub changes_files: Vec<PathBuf>,
    /// Located license files, resolved against the project root.
    pub license_files: Vec<PathBuf>,
    /// Located readme files, resolved against the project root.
    pub readme_files: Vec<PathBuf>,
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

/// One package in the transitive dependency-license audit.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DependencyLicense {
    /// Dependency package name.
    pub name: String,
    /// Dependency package version.
    pub version: String,
    /// Validated SPDX license identifier.
    pub license: License,
}

/// Read every transitive path dependency's package license.
///
/// The root package is deliberately omitted: this is the dependency audit used
/// by `prism check --licenses`. Stored git and hash bundles do not yet carry a
/// package manifest, so the command fails closed rather than hiding one.
///
/// # Errors
/// Fails on an invalid manifest, a dependency cycle, or a stored dependency
/// whose license metadata is unavailable.
pub fn dependency_licenses(arg: &Path) -> Result<Vec<DependencyLicense>, Error> {
    let manifest_path = project_manifest(arg);
    let (manifest, root, key) = read_manifest(&manifest_path)?;
    let mut seen = BTreeSet::from([key.clone()]);
    let mut visiting = vec![key];
    let mut licenses = Vec::new();
    visit_dependency_licenses(&manifest, &root, &mut seen, &mut visiting, &mut licenses)?;
    licenses.sort();
    Ok(licenses)
}

fn visit_dependency_licenses(
    manifest: &Manifest,
    root: &Path,
    seen: &mut BTreeSet<PathBuf>,
    visiting: &mut Vec<PathBuf>,
    licenses: &mut Vec<DependencyLicense>,
) -> Result<(), Error> {
    for dependency in &manifest.dependencies {
        let DepSource::Path(relative) = &dependency.source else {
            return Err(Error::ResolveProject(format!(
                "dependency `{}` has no local manifest for license auditing",
                dependency.name
            )));
        };
        let manifest_path = project_manifest(&root.join(relative));
        let (dependency_manifest, dependency_root, key) = read_manifest(&manifest_path)
            .map_err(|e| Error::ResolveProject(format!("dependency `{}`: {e}", dependency.name)))?;
        if visiting.contains(&key) {
            return Err(Error::ResolveProject(format!(
                "dependency cycle through `{}`",
                manifest_path.display()
            )));
        }
        if !seen.insert(key.clone()) {
            continue;
        }
        licenses.push(DependencyLicense {
            name: dependency_manifest.name.clone(),
            version: dependency_manifest.version.clone(),
            license: dependency_manifest.license,
        });
        visiting.push(key);
        visit_dependency_licenses(
            &dependency_manifest,
            &dependency_root,
            seen,
            visiting,
            licenses,
        )?;
        visiting.pop();
    }
    Ok(())
}

fn project_manifest(arg: &Path) -> PathBuf {
    if arg.is_dir() {
        arg.join(MANIFEST)
    } else {
        arg.to_path_buf()
    }
}

fn read_manifest(path: &Path) -> Result<(Manifest, PathBuf, PathBuf), Error> {
    let text = std::fs::read_to_string(path)?;
    let manifest = Manifest::parse(&text)?;
    let root = path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    let key = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    Ok((manifest, root, key))
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
        version: manifest.version,
        authors: manifest.authors,
        maintainers: manifest.maintainers,
        license: manifest.license,
        description: manifest.description,
        homepage: manifest.homepage,
        issues: manifest.issues,
        online_doc: manifest.online_doc,
        repo: manifest.repo,
        changes_files: manifest
            .changes_files
            .into_iter()
            .map(|path| root.join(path))
            .collect(),
        license_files: manifest
            .license_files
            .into_iter()
            .map(|path| root.join(path))
            .collect(),
        readme_files: manifest
            .readme_files
            .into_iter()
            .map(|path| root.join(path))
            .collect(),
        dep_src_dirs,
        dependencies: manifest.dependencies,
        root,
    })
}

#[cfg(test)]
mod tests {
    use super::{hash_pin, parse_hash_pin, DepSource, License, Manifest};
    use std::path::PathBuf;

    const VERSION: &str = "0.1.0";
    const AUTHOR: &str = "A. Developer <dev@example.com>";
    const MAINTAINER: &str = "dev@example.com";

    fn manifest(name: &str, package_extra: &str, tail: &str) -> String {
        format!(
            r#"[package]
name = {name:?}
version = {VERSION:?}
authors = [{AUTHOR:?}]
maintainers = [{MAINTAINER:?}]
license = "MIT"
{package_extra}
{tail}"#
        )
    }

    fn minimal(name: &str) -> String {
        manifest(name, "", "[bin]\nentry = \"src/main.pr\"\n")
    }

    #[test]
    fn parses_required_metadata_entry_and_default_src() {
        let m = Manifest::parse(&minimal("demo")).unwrap();
        assert_eq!(m.name, "demo");
        assert_eq!(m.version, VERSION);
        assert_eq!(m.authors, [AUTHOR]);
        assert_eq!(m.maintainers, [MAINTAINER]);
        assert_eq!(m.license, License::Mit);
        assert_eq!(m.description, None);
        assert_eq!(m.entry.to_str(), Some("src/main.pr"));
        assert_eq!(m.src_dir.to_str(), Some("src"));
        assert_eq!(m.prelude, None);
    }

    #[test]
    fn parses_optional_package_metadata() {
        let m = Manifest::parse(&manifest(
            "demo",
            "description = \"A small demo.\"\n\
             homepage = \"https://example.com/demo\"\n\
             issues = \"https://example.com/demo/issues\"\n\
             online-doc = \"https://docs.example.com/demo\"\n\
             repo = \"git+https://example.com/demo.git\"\n\
             changes-files = [\"CHANGES.md\"]\n\
             license-files = [\"LICENSE\"]\n\
             readme-files = [\"README.md\", \"GUIDE.md\"]",
            "[bin]\nentry = \"src/main.pr\"\n",
        ))
        .unwrap();
        assert_eq!(m.description.as_deref(), Some("A small demo."));
        assert_eq!(m.homepage.as_deref(), Some("https://example.com/demo"));
        assert_eq!(m.issues.as_deref(), Some("https://example.com/demo/issues"));
        assert_eq!(
            m.online_doc.as_deref(),
            Some("https://docs.example.com/demo")
        );
        assert_eq!(m.repo.as_deref(), Some("git+https://example.com/demo.git"));
        assert_eq!(m.changes_files, [PathBuf::from("CHANGES.md")]);
        assert_eq!(m.license_files, [PathBuf::from("LICENSE")]);
        assert_eq!(
            m.readme_files,
            [PathBuf::from("README.md"), PathBuf::from("GUIDE.md")]
        );
    }

    #[test]
    fn required_metadata_is_non_empty_and_well_typed() {
        let missing_version = r#"[package]
name = "demo"
authors = ["a"]
maintainers = ["m"]
license = "MIT"

[bin]
entry = "src/main.pr"
"#;
        assert!(Manifest::parse(missing_version).is_err());
        let base = minimal("demo");
        assert!(
            Manifest::parse(&base.replace(&format!("authors = [{AUTHOR:?}]"), "authors = []"))
                .is_err()
        );
        assert!(Manifest::parse(&base.replace(
            &format!("maintainers = [{MAINTAINER:?}]"),
            "maintainers = [42]"
        ))
        .is_err());
        assert!(Manifest::parse(&base.replace("license = \"MIT\"", "license = \"\"")).is_err());
        assert!(
            Manifest::parse(&base.replace("license = \"MIT\"", "license = \"Beerware\"")).is_err()
        );
    }

    #[test]
    fn optional_metadata_rejects_wrong_types() {
        assert!(Manifest::parse(&manifest(
            "demo",
            "description = 42",
            "[bin]\nentry = \"src/main.pr\"\n"
        ))
        .is_err());
        assert!(Manifest::parse(&manifest(
            "demo",
            "readme-files = \"README.md\"",
            "[bin]\nentry = \"src/main.pr\"\n"
        ))
        .is_err());
    }

    #[test]
    fn parses_prelude_override() {
        let m = Manifest::parse(&manifest(
            "demo",
            "prelude = \"src/Prelude.pr\"",
            "[bin]\nentry = \"src/main.pr\"\n",
        ))
        .unwrap();
        assert_eq!(
            m.prelude.as_deref().and_then(|p| p.to_str()),
            Some("src/Prelude.pr")
        );
    }

    #[test]
    fn parses_path_dependencies_both_forms() {
        let m = Manifest::parse(&manifest(
            "app",
            "",
            "[bin]\nentry = \"src/main.pr\"\n\n\
             [dependencies]\ngeo = { path = \"../geo\" }\nutil = \"../util\"\n",
        ))
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
        let text = manifest(
            "app",
            "",
            &format!(
                "[bin]\nentry = \"src/main.pr\"\n\n\
                 [dependencies]\n\
                 http = {{ git = \"github.com/prism-lang/http\", version = \"2.0\" }}\n\
                 crypto = \"{pin}\"\n"
            ),
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
        assert!(Manifest::parse(&manifest(
            "a",
            "",
            "[bin]\nentry = \"s.pr\"\n\n[dependencies]\nx = { git = \"g/h\" }\n",
        ))
        .is_err());
    }

    #[test]
    fn dependency_with_no_recognised_key_is_an_error() {
        assert!(Manifest::parse(&manifest(
            "a",
            "",
            "[bin]\nentry = \"s.pr\"\n\n[dependencies]\nx = { version = \"1\" }\n",
        ))
        .is_err());
    }

    #[test]
    fn missing_entry_is_an_error() {
        assert!(Manifest::parse(&manifest("demo", "", "")).is_err());
    }
}
