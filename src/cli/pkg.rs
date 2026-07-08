//! Package manager and store-publishing command bodies.

use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

use crate::cli::check_world::{PACKAGE_USAGE_SUMMARY, USAGE_SUMMARY_PHASE};
use crate::cli::{out_stem, pkg_report, resolve_input, user_source, CmdResult};
use crate::error::Error;

pub fn init() -> CmdResult {
    let mut stdout = io::stdout();
    write!(stdout, "package name: ")
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;
    stdout
        .flush()
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;
    let mut name = String::new();
    io::stdin()
        .read_line(&mut name)
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;

    write!(stdout, "directory name: ")
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;
    stdout
        .flush()
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;
    let mut dir = String::new();
    io::stdin()
        .read_line(&mut dir)
        .map_err(|e| (Error::Io(e), String::new(), "pkg init".into()))?;

    let dir = PathBuf::from(dir.trim());
    pkg_report(crate::pkg::cmd::init(&name, &dir), "pkg init")
}

pub fn add(target: &str, cfg: &crate::Config) -> CmdResult {
    pkg_report(crate::pkg::cmd::add(target, cfg), target)
}

pub fn why(target: &str, cfg: &crate::Config) -> CmdResult {
    pkg_report(crate::pkg::cmd::why(target, cfg), target)
}

pub fn export(file: &Path, out: Option<PathBuf>, cfg: &crate::Config) -> CmdResult {
    let (full, roots, _name, default_out) = resolve_input(file, cfg)?;
    let user_src = user_source(file)?;
    let stem = out_stem(&default_out);
    let out_dir = out.unwrap_or_else(|| PathBuf::from("target").join("export"));
    pkg_report(
        crate::pkg::export::export_cmd(&user_src, &full, &roots, &out_dir, &stem),
        &file.display().to_string(),
    )
}

pub fn publish(
    file: &Path,
    tag: &str,
    name: Option<String>,
    origin: Option<String>,
    cfg: &crate::Config,
) -> CmdResult {
    let (full, roots, _disp, default_out) = resolve_input(file, cfg)?;
    let user_src = user_source(file)?;
    let pkg_name = name.unwrap_or_else(|| out_stem(&default_out));
    let pkg_origin = origin.unwrap_or_else(|| pkg_name.clone());
    pkg_report(
        crate::pkg::trust::publish_source_cmd(
            &user_src,
            &full,
            &roots,
            &pkg_origin,
            &pkg_name,
            tag,
            cfg,
        ),
        &file.display().to_string(),
    )
}

// `prism audit`: render the report and set the exit code from its verdict.
pub fn audit(cfg: &crate::Config, allow_unsigned: bool) -> CmdResult {
    let report = crate::pkg::trust::audit_cmd(cfg, allow_unsigned)
        .map_err(|e| (e, String::new(), "audit".to_string()))?;
    print!("{}", report.render());
    if report.ok() {
        Ok(())
    } else {
        Err((
            Error::Resolve("audit failed".into()),
            String::new(),
            "audit".to_string(),
        ))
    }
}

// The package root a committed artifact lives in: the directory itself when given a
// directory, otherwise the parent of the `prism.toml` or `.pr` file.
fn package_root(path: &Path) -> PathBuf {
    if path.is_dir() {
        path.to_path_buf()
    } else {
        path.parent()
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
    }
}

// `pkg accept-usage <pkg>`: regenerate the usage summary through the same phase the
// check-world usage gate compares against and write it to the package root as
// `usage-summary.md`. Creating the file for the first time and refreshing a drifted
// one are the same operation; the output is byte-stable, so a second accept over an
// unchanged package rewrites identical bytes.
pub fn accept_usage(path: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(path, cfg)?;
    let summary = crate::dump_on(USAGE_SUMMARY_PHASE, &full, &roots, cfg)
        .map_err(|e| (e, full, name.clone()))?;
    let golden = package_root(path).join(PACKAGE_USAGE_SUMMARY);
    std::fs::write(&golden, &summary).map_err(|e| (Error::Io(e), String::new(), name))?;
    println!("wrote {}", golden.display());
    Ok(())
}
