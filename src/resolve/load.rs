//! Module loader: turns a root program's imports into the set of module files
//! it transitively depends on.
//!
//! A module is one `.pr` file; directories are namespace prefixes
//! (`Data.Map` -> `<root>/Data/Map.pr`). Modules resolve against a search path
//! of [`Root`]s tried in order: the project source, any path dependencies, and
//! the embedded standard library. The first root that has a module wins, so a
//! project may shadow a stdlib module by defining its own. Loading dedupes by
//! module path and keeps a visited set, so import cycles load each file once
//! rather than looping.

use std::collections::{BTreeSet, VecDeque};
use std::fs;
use std::path::PathBuf;

use crate::error::Error;
use crate::parse::parse;
use crate::syntax::ast::Program;

#[derive(Debug)]
pub struct Module {
    pub path: Vec<String>,
    pub prog: Program,
}

/// One entry in the module search path: a source directory on disk, or the
/// in-binary standard library (a table of dotted module path to source text).
#[derive(Debug, Clone)]
pub enum Root {
    Dir(PathBuf),
    Embedded(&'static [(&'static str, &'static str)]),
}

impl Root {
    /// Fetch the source of module `path` from this root, or `None` if absent
    /// here (so the next root is tried). A "not found" miss falls through, as
    /// does an "unsupported" miss: a `Dir` root on a platform with no filesystem
    /// (wasm) cannot supply the file, so resolution proceeds to the embedded
    /// stdlib rather than failing. Any other read error is a hard error.
    fn fetch(&self, path: &[String]) -> Result<Option<String>, Error> {
        match self {
            Self::Dir(base) => {
                let mut p = base.clone();
                for c in path {
                    p.push(c);
                }
                p.set_extension(crate::driver::SOURCE_EXT);
                match fs::read_to_string(&p) {
                    Ok(src) => Ok(Some(src)),
                    Err(e)
                        if matches!(
                            e.kind(),
                            std::io::ErrorKind::NotFound | std::io::ErrorKind::Unsupported
                        ) =>
                    {
                        Ok(None)
                    }
                    Err(e) => Err(Error::Resolve(format!(
                        "cannot load module `{}`: {} ({})",
                        path.join("."),
                        e,
                        p.display()
                    ))),
                }
            }
            Self::Embedded(table) => {
                let key = path.join(".");
                Ok(table
                    .iter()
                    .find(|(name, _)| *name == key)
                    .map(|(_, src)| (*src).to_string()))
            }
        }
    }
}

// Where the search looked, for a not-found diagnostic.
fn searched(roots: &[Root]) -> String {
    roots
        .iter()
        .map(|r| match r {
            Root::Dir(p) => p.display().to_string(),
            Root::Embedded(_) => "<stdlib>".to_string(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Load every module reachable from `root`'s imports, searching `roots` in order.
///
/// # Errors
/// Fails when an imported module is found in no root, is unreadable, or does not
/// parse.
pub fn load(root: &Program, roots: &[Root]) -> Result<Vec<Module>, Error> {
    let mut out = Vec::new();
    let mut visited = BTreeSet::new();
    let mut queue: VecDeque<Vec<String>> = root.imports.iter().map(|i| i.path.clone()).collect();
    while let Some(path) = queue.pop_front() {
        if !visited.insert(path.join(".")) {
            continue;
        }
        let mut src = None;
        for r in roots {
            if let Some(found) = r.fetch(&path)? {
                src = Some(found);
                break;
            }
        }
        let src = src.ok_or_else(|| {
            Error::Resolve(format!(
                "cannot resolve module `{}` (searched: {})",
                path.join("."),
                searched(roots)
            ))
        })?;
        let program = parse(&src)
            .map_err(|e| Error::Resolve(format!("in module `{}`: {e}", path.join("."))))?
            .program;
        for imp in &program.imports {
            queue.push_back(imp.path.clone());
        }
        out.push(Module {
            path,
            prog: program,
        });
    }
    Ok(out)
}
