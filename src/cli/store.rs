//! Content-addressed store command bodies: attest, query, reseat wire goldens.

use std::path::Path;

use crate::cli::{file_name, read, resolve_input, CmdResult};
use crate::driver::stable_lock;
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

// Lock or verify a file's stable-migration behavior. Without `--accept` it derives
// the manifest and verifies it against the committed sibling file (or previews it
// when the family is not yet locked); with `--accept` it previews and rewrites the
// committed manifest in place. A second `--accept` on an unchanged tree is a
// no-op, so the lock is byte-idempotent.
pub fn lock(accept: bool, file: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let derived =
        stable_lock::derive(&full, &roots).map_err(|e| (e, full.clone(), name.clone()))?;
    if derived.is_empty() {
        eprintln!(
            "{}: no `stable` family declares a `migrations` table to lock",
            file.display()
        );
        return Ok(());
    }
    let path = stable_lock::manifest_path(file);
    if !accept {
        if let Some(committed) =
            stable_lock::read_committed(file).map_err(|e| (e, full.clone(), name.clone()))?
        {
            stable_lock::verify(&full, &roots, &committed)
                .map_err(|e| (e, full.clone(), name.clone()))?;
            eprintln!("{}: locked families verified", file.display());
        } else {
            print!("{}", derived.render());
            eprintln!(
                "{}: pass --accept to write {}",
                file.display(),
                path.display()
            );
        }
        return Ok(());
    }
    let text = derived.to_text().map_err(|e| {
        (
            Error::ResolveCommand(e.to_string()),
            full.clone(),
            name.clone(),
        )
    })?;
    if std::fs::read_to_string(&path).is_ok_and(|existing| existing == text) {
        eprintln!("{}: lock manifest already current", path.display());
        return Ok(());
    }
    print!("{}", derived.render());
    std::fs::write(&path, &text).map_err(|e| (Error::Io(e), String::new(), name))?;
    eprintln!("{}: lock manifest written", path.display());
    Ok(())
}
