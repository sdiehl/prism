//! Content-addressed store command bodies: attest, query, reseat wire goldens.

use std::fmt::Write as _;
use std::io::IsTerminal;
use std::path::Path;
use std::sync::{Mutex, PoisonError};
use std::time::Duration;

use crate::cli::{file_name, read, resolve_input, CmdResult};
use crate::driver::stable_lock;
use crate::error::Error;
use crate::store::disk::{resolve_store_path, GcProgress, Store};

const SECS_PER_DAY: u64 = 24 * 60 * 60;

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

// Garbage-collect store cache entries the query and index layers no longer
// reference, sparing anything younger than `days` (the safety margin for
// content whose liveness the store cannot see, and for a write racing this
// sweep). See `prism_store::disk::gc` for the reachability rules.
pub fn gc(days: u64, dry_run: bool, cfg: &crate::Config) -> CmdResult {
    let store_root = resolve_store_path(cfg.flags().store_path.as_deref());
    let store = Store::open_or_create(&store_root).map_err(|e| io_err(e, &store_root, "open"))?;
    let census = store
        .census()
        .map_err(|e| io_err(e, &store_root, "census"))?;
    eprintln!(
        "store gc ({}): {} files",
        store_root.display(),
        group_thousands(census.total())
    );
    let width = census
        .layers
        .iter()
        .map(|layer| layer.name.len())
        .max()
        .unwrap_or(0);
    for layer in &census.layers {
        if layer.files > 0 {
            eprintln!(
                "  {:<width$}  {:>11}",
                layer.name,
                group_thousands(layer.files)
            );
        }
    }
    let min_age = Duration::from_secs(days.saturating_mul(SECS_PER_DAY));
    let render = ProgressRender::new();
    let swept = store.gc_with_progress(min_age, dry_run, &|beat| render.beat(beat));
    render.finish();
    let stats = swept.map_err(|e| io_err(e, &store_root, "gc"))?;
    let verb = if dry_run { "would remove" } else { "removed" };
    let mut summary = format!(
        "store gc ({}): {verb} {} query bindings, {} objects, {} metadata blobs, {} reclaimed",
        store_root.display(),
        group_thousands(stats.queries_removed),
        group_thousands(stats.objects_removed),
        group_thousands(stats.meta_removed),
        human_bytes(stats.bytes_removed),
    );
    if stats.salvaged > 0 {
        let _ = write!(summary, ", {} salvaged", group_thousands(stats.salvaged));
    }
    eprintln!("{summary}");
    if !dry_run {
        let after = store
            .census()
            .map_err(|e| io_err(e, &store_root, "census"))?;
        eprintln!("store now holds {} files", group_thousands(after.total()));
    }
    Ok(())
}

const BAR_WIDTH: u64 = 24;

// Renders sweep progress: on a terminal, one live line redrawn in place per
// beat; otherwise a single line per phase transition so piped output stays
// short. Beats arrive from the sweep's worker threads, hence the mutex.
struct ProgressRender {
    tty: bool,
    last: Mutex<Option<GcProgress>>,
}

impl ProgressRender {
    fn new() -> Self {
        Self {
            tty: std::io::stderr().is_terminal(),
            last: Mutex::new(None),
        }
    }

    fn beat(&self, beat: &GcProgress) {
        let mut last = self.last.lock().unwrap_or_else(PoisonError::into_inner);
        let new_phase = last.as_ref().is_none_or(|prev| prev.phase != beat.phase);
        if self.tty {
            if new_phase && last.is_some() {
                eprintln!();
            }
            eprint!("\r\x1b[2K{}", progress_line(beat));
        } else if new_phase {
            eprintln!("store gc: {} ...", beat.phase);
        }
        *last = Some(beat.clone());
    }

    // Terminate the live line so the summary starts on its own row.
    fn finish(&self) {
        let last = self.last.lock().unwrap_or_else(PoisonError::into_inner);
        if self.tty && last.is_some() {
            eprintln!();
        }
    }
}

fn progress_line(beat: &GcProgress) -> String {
    let mut line = format!("store gc: {}", beat.phase);
    // A zero total means the phase's extent is unknown, so no bar is drawn;
    // `checked_div` folds that case and the fill arithmetic together.
    let fill = beat
        .done
        .min(beat.total)
        .saturating_mul(BAR_WIDTH)
        .checked_div(beat.total);
    if let Some(filled) = fill {
        let bar: String = (0..BAR_WIDTH)
            .map(|i| if i < filled { '#' } else { '-' })
            .collect();
        let _ = write!(line, " [{bar}] {}/{}", beat.done, beat.total);
    }
    if beat.removed > 0 {
        let _ = write!(line, ", {} removed", group_thousands(beat.removed));
    }
    if beat.bytes > 0 {
        let _ = write!(line, " ({})", human_bytes(beat.bytes));
    }
    if beat.salvaged > 0 {
        let _ = write!(line, ", {} salvaged", group_thousands(beat.salvaged));
    }
    line
}

fn group_thousands(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::with_capacity(digits.len() + digits.len() / 3);
    for (i, ch) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(ch);
    }
    out
}

fn io_err(e: std::io::Error, store_root: &Path, verb: &str) -> (Error, String, String) {
    (
        Error::Io(e),
        String::new(),
        format!("store {verb} at {}", store_root.display()),
    )
}

// Display-only rounding: precision loss above 2^52 bytes is invisible in a
// one-decimal human-readable size.
#[allow(clippy::cast_precision_loss)]
fn human_bytes(bytes: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut value = bytes as f64;
    let mut unit = UNITS[0];
    for candidate in &UNITS[1..] {
        if value < 1024.0 {
            break;
        }
        value /= 1024.0;
        unit = candidate;
    }
    if unit == UNITS[0] {
        format!("{bytes} {unit}")
    } else {
        format!("{value:.1} {unit}")
    }
}
