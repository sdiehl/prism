//! `prism fmt`: format source files in place, or filter stdin for an editor.

use std::io::Read as _;
use std::path::{Path, PathBuf};

use crate::cli::{file_name, glob_pr, read, CmdResult};
use crate::error::Error;

// One path per line, `#` starting a comment, resolved against the directory
// holding the file, which is searched for upward from each walk root the way
// git finds its own configuration. A path matches the file itself or anything
// beneath it.
const IGNORE_FILE: &str = ".prismfmtignore";

// `prism fmt [paths..] [--check]`. With no path, the current directory is
// walked, as is any directory path. Explicitly named files must parse. Files
// reached by walking are skipped with a notice if they do not, so one
// unparseable fixture cannot fail a whole-tree run.
pub fn fmt_cmd(paths: &[PathBuf], check: bool) -> CmdResult {
    if paths.len() == 1 && paths[0].as_os_str() == "-" {
        return fmt_stdin();
    }
    let mut targets: Vec<(PathBuf, bool)> = Vec::new();
    if paths.is_empty() {
        targets.extend(walk(Path::new(".")));
    } else {
        for p in paths {
            if p.is_dir() {
                targets.extend(walk(p));
            } else {
                targets.push((p.clone(), true));
            }
        }
    }
    targets.sort();
    targets.dedup();

    let mut needs_fmt = false;
    for (path, strict) in targets {
        let src = read(&path).map_err(|e| (e, String::new(), file_name(&path)))?;
        let formatted = match crate::format(&src) {
            Ok(f) => f,
            Err(e) if strict => return Err((e, src, file_name(&path))),
            Err(_) => {
                eprintln!("{}: skipped (does not parse)", path.display());
                continue;
            }
        };
        if formatted == src {
            continue;
        }
        if check {
            eprintln!("{}: not formatted", path.display());
            needs_fmt = true;
        } else {
            std::fs::write(&path, &formatted)
                .map_err(|e| (Error::Io(e), String::new(), file_name(&path)))?;
        }
    }
    if needs_fmt {
        Err((
            Error::CodegenFormat("some files need formatting".into()),
            String::new(),
            String::new(),
        ))
    } else {
        Ok(())
    }
}

// Walk a directory for `.pr` files, dropping the ones an `IGNORE_FILE` claims.
// Ignoring applies to walking only: naming a file on the command line still
// formats it, so the exemption never becomes a way to lose an edit silently.
fn walk(root: &Path) -> Vec<(PathBuf, bool)> {
    let ignored = ignored_paths(root);
    glob_pr(root)
        .into_iter()
        .filter(|p| {
            let full = absolute(p);
            !ignored.iter().any(|i| full.starts_with(i))
        })
        .map(|p| (p, false))
        .collect()
}

// The absolute form of every path an `IGNORE_FILE` at or above `root` lists.
// Test data pinned by digest cannot also be formatter-owned: its exact bytes
// are the contract, so a formatter release that changes layout would otherwise
// rewrite the very inputs a frozen corpus exists to hold still.
fn ignored_paths(root: &Path) -> Vec<PathBuf> {
    let mut dir = absolute(root);
    loop {
        let candidate = dir.join(IGNORE_FILE);
        if let Ok(text) = std::fs::read_to_string(&candidate) {
            return text
                .lines()
                .map(|line| line.split('#').next().unwrap_or_default().trim())
                .filter(|line| !line.is_empty())
                .map(|line| dir.join(line))
                .collect();
        }
        if !dir.pop() {
            return Vec::new();
        }
    }
}

fn absolute(path: &Path) -> PathBuf {
    if path.is_absolute() {
        return path.to_path_buf();
    }
    std::env::current_dir().map_or_else(|_| path.to_path_buf(), |cwd| cwd.join(path))
}

// Editor format-on-save filter: read source on stdin, write the canonical form
// to stdout. Any parse error is fatal so an editor never overwrites a buffer
// with a half-formatted result.
fn fmt_stdin() -> CmdResult {
    let mut src = String::new();
    std::io::stdin()
        .read_to_string(&mut src)
        .map_err(|e| (Error::Io(e), String::new(), "<stdin>".into()))?;
    let formatted = crate::format(&src).map_err(|e| (e, src.clone(), "<stdin>".into()))?;
    print!("{formatted}");
    Ok(())
}
