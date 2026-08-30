//! Package manager and store-publishing command bodies.

use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use crate::cli::check_world::{PACKAGE_USAGE_SUMMARY, USAGE_SUMMARY_PHASE};
use crate::cli::{out_stem, pkg_report, resolve_input, user_source, CmdError, CmdResult};
use crate::error::Error;
use crate::pkg::cmd::{add as pkg_add, init as pkg_init, why as pkg_why};
use crate::pkg::export::export_cmd;
use crate::pkg::trust::{audit_cmd, publish_source_cmd};
use crate::{dump_on, Config};

const AUDIT_COMMAND: &str = "audit";
const AUDIT_FAILED: &str = "audit failed";
const PKG_INIT_COMMAND: &str = "pkg init";

pub fn init() -> CmdResult {
    let mut stdout = io::stdout();
    let name = prompt(&mut stdout, "package name")?;
    let dir = prompt(&mut stdout, "directory name")?;
    let version = prompt(&mut stdout, "version")?;
    let author = prompt(&mut stdout, "author")?;
    let maintainer = prompt(&mut stdout, "maintainer")?;
    let license = prompt(&mut stdout, "license")?;

    let dir = PathBuf::from(dir.trim());
    pkg_report(
        pkg_init(&name, &dir, &version, &author, &maintainer, &license),
        PKG_INIT_COMMAND,
    )
}

fn prompt(stdout: &mut impl Write, field: &str) -> Result<String, CmdError> {
    write!(stdout, "{field}: ")
        .map_err(|e| (Error::Io(e), String::new(), PKG_INIT_COMMAND.into()))?;
    stdout
        .flush()
        .map_err(|e| (Error::Io(e), String::new(), PKG_INIT_COMMAND.into()))?;
    let mut value = String::new();
    io::stdin()
        .read_line(&mut value)
        .map_err(|e| (Error::Io(e), String::new(), PKG_INIT_COMMAND.into()))?;
    Ok(value.trim().to_string())
}

pub fn add(target: &str, cfg: &Config) -> CmdResult {
    pkg_report(pkg_add(target, cfg), target)
}

pub fn why(target: &str, cfg: &Config) -> CmdResult {
    pkg_report(pkg_why(target, cfg), target)
}

pub fn export(file: &Path, out: Option<PathBuf>, cfg: &Config) -> CmdResult {
    let (full, roots, _name, default_out) = resolve_input(file, cfg)?;
    let user_src = user_source(file)?;
    let stem = out_stem(&default_out);
    let out_dir = out.unwrap_or_else(|| PathBuf::from("target").join("export"));
    pkg_report(
        export_cmd(&user_src, &full, &roots, &out_dir, &stem),
        &file.display().to_string(),
    )
}

pub fn publish(
    file: &Path,
    tag: &str,
    name: Option<String>,
    origin: Option<String>,
    cfg: &Config,
) -> CmdResult {
    let (full, roots, _disp, default_out) = resolve_input(file, cfg)?;
    let user_src = user_source(file)?;
    let pkg_name = name.unwrap_or_else(|| out_stem(&default_out));
    let pkg_origin = origin.unwrap_or_else(|| pkg_name.clone());
    pkg_report(
        publish_source_cmd(&user_src, &full, &roots, &pkg_origin, &pkg_name, tag, cfg),
        &file.display().to_string(),
    )
}

// `prism audit`: render the report and set the exit code from its verdict.
pub fn audit(cfg: &Config, allow_unsigned: bool) -> CmdResult {
    let report = audit_cmd(cfg, allow_unsigned)
        .map_err(|e| (e, String::new(), AUDIT_COMMAND.to_string()))?;
    print!("{}", report.render());
    if report.ok() {
        Ok(())
    } else {
        Err((
            Error::ResolvePackage(AUDIT_FAILED.into()),
            String::new(),
            AUDIT_COMMAND.to_string(),
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
pub fn accept_usage(path: &Path, cfg: &Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(path, cfg)?;
    let summary =
        dump_on(USAGE_SUMMARY_PHASE, &full, &roots, cfg).map_err(|e| (e, full, name.clone()))?;
    let golden = package_root(path).join(PACKAGE_USAGE_SUMMARY);
    fs::write(&golden, &summary).map_err(|e| (Error::Io(e), String::new(), name))?;
    println!("wrote {}", golden.display());
    Ok(())
}
