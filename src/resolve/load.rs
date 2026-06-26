//! Module loader: turns a root program's imports into the set of module files
//! it transitively depends on.
//!
//! A module is one `.pr` file; directories are namespace prefixes
//! (`Data.Map` -> `<root>/Data/Map.pr`). Loading dedupes by module path and
//! keeps a visited set, so import cycles load each file once rather than
//! looping.

use std::collections::{BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};

use crate::error::Error;
use crate::parse::parse;
use crate::syntax::ast::Program;

#[derive(Debug)]
pub struct Module {
    pub path: Vec<String>,
    pub prog: Program,
}

fn module_file(base: &Path, path: &[String]) -> PathBuf {
    let mut p = base.to_path_buf();
    for c in path {
        p.push(c);
    }
    p.set_extension(crate::driver::SOURCE_EXT);
    p
}

/// Load every module reachable from `root`'s imports, searching under `base`.
///
/// # Errors
/// Fails when an imported file is missing, unreadable, or does not parse.
pub fn load(root: &Program, base: &Path) -> Result<Vec<Module>, Error> {
    let mut out = Vec::new();
    let mut visited = BTreeSet::new();
    let mut queue: VecDeque<Vec<String>> = root.imports.iter().map(|i| i.path.clone()).collect();
    while let Some(path) = queue.pop_front() {
        if !visited.insert(path.join(".")) {
            continue;
        }
        let file = module_file(base, &path);
        let src = fs::read_to_string(&file).map_err(|e| {
            Error::Resolve(format!(
                "cannot load module `{}`: {} (searched `{}` under root `{}`)",
                path.join("."),
                e,
                file.display(),
                base.display()
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
