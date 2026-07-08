//! Content-addressed store command bodies: attest, query, reseat wire goldens.

use std::path::Path;

use crate::cli::{file_name, read, resolve_input, CmdResult};
use crate::error::Error;

// Attest two backends emit identical output.
pub fn attest(file: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let out = crate::attest_on(&full, &roots, cfg).map_err(|e| (e, full, name))?;
    print!("{out}");
    Ok(())
}

// Query the definition dependency graph.
pub fn query(kind: &str, name: &str, file: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, disp, _) = resolve_input(file, cfg)?;
    let out = crate::query_on(kind, name, &full, &roots, cfg).map_err(|e| (e, full, disp))?;
    print!("{out}");
    Ok(())
}

// Reseat the wire goldens of a single file's `stable` blocks. Without `--accept`
// it is a deliberate no-op, so an accidental `prism store wire foo.pr` never rewrites.
pub fn wire(accept: bool, file: &Path) -> CmdResult {
    let name = file_name(file);
    let src = read(file).map_err(|e| (e, String::new(), name.clone()))?;
    if !accept {
        eprintln!(
            "wire: pass --accept to reseat the goldens in {}",
            file.display()
        );
        return Ok(());
    }
    let reseated = crate::format_wire_accept(&src).map_err(|e| (e, src.clone(), name.clone()))?;
    if reseated == src {
        eprintln!("{}: goldens already current", file.display());
        return Ok(());
    }
    std::fs::write(file, &reseated).map_err(|e| (Error::Io(e), String::new(), name))?;
    eprintln!("{}: goldens reseated", file.display());
    Ok(())
}
