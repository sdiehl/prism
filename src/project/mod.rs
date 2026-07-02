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
    /// Optional `[package] prelude`, a path (relative to the root) whose contents
    /// replace the built-in prelude for this project. Absent uses the built-in.
    pub prelude: Option<PathBuf>,
    /// `[dependencies]` path dependencies: each `name = { path = "..." }` maps a
    /// dependency name to its project root, relative to this manifest's root.
    pub dependencies: Vec<Dependency>,
}

/// A local path dependency: another Prism project whose modules resolve under
/// its own source root. No versions or registry yet (that is a later phase);
/// `path` is relative to the depending project's root.
#[derive(Debug, Clone)]
pub struct Dependency {
    pub name: String,
    pub path: PathBuf,
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

    // `[dependencies]` is a table of `name = { path = "..." }`. A bare-string
    // form (`name = "..."`) is accepted as shorthand for the path. Anything else
    // is rejected so a typo cannot silently drop a dependency.
    fn parse_deps(table: &toml::Table) -> Result<Vec<Dependency>, Error> {
        let Some(deps) = table.get("dependencies") else {
            return Ok(Vec::new());
        };
        let deps = deps
            .as_table()
            .ok_or_else(|| Error::Resolve("prism.toml: [dependencies] must be a table".into()))?;
        deps.iter()
            .map(|(name, val)| {
                let path = match val {
                    toml::Value::String(s) => s.as_str(),
                    toml::Value::Table(t) => t.get("path").and_then(toml::Value::as_str).ok_or_else(
                        || Error::Resolve(format!("prism.toml: dependency `{name}` needs a `path`")),
                    )?,
                    _ => {
                        return Err(Error::Resolve(format!(
                            "prism.toml: dependency `{name}` must be a path string or `{{ path = .. }}`"
                        )))
                    }
                };
                Ok(Dependency {
                    name: name.clone(),
                    path: PathBuf::from(path),
                })
            })
            .collect()
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
        return Err(Error::Resolve(format!(
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
        let dep_proj = load_project_rec(&root.join(&dep.path), visiting)
            .map_err(|e| Error::Resolve(format!("dependency `{}`: {e}", dep.name)))?;
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
            .map(|d| (d.name.as_str(), d.path.to_str().unwrap()))
            .collect();
        deps.sort_unstable();
        assert_eq!(deps, [("geo", "../geo"), ("util", "../util")]);
    }

    #[test]
    fn dependency_without_path_is_an_error() {
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
