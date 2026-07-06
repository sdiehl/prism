use std::env;
use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::codegen::rt::{write_libm_archive, write_runtime};
use crate::error::Error;

use super::{Config, NATIVE_KONT_FRAME_FLAGS};

pub(super) fn run_native(bin: &Path) -> Result<Vec<u8>, Error> {
    let out = Command::new(bin)
        .stdin(Stdio::null())
        .output()
        .map_err(Error::Io)?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(Error::Codegen(format!(
            "attest: {} exited with {}",
            bin.display(),
            out.status
        )))
    }
}

pub(super) fn cc_link(ir: &Path, out: &Path, cfg: &Config) -> Result<(), Error> {
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
    let rt_dir = out.with_extension("prism_rt.d");
    let sources = write_runtime(&rt_dir)?;
    let libm_archive = write_libm_archive(&rt_dir)?;
    let extra = env::var("PRISM_CC_FLAGS").unwrap_or_default();
    let olevel = format!("-O{}", cfg.backend_opt);
    let rt_checks: &[&str] = if cfg.flags.rt_checks {
        &["-DPRISM_RT_DEBUG"]
    } else {
        &[]
    };
    let native_kont_frame_flags: &[&str] = if cfg.flags.native_kont_frames {
        &NATIVE_KONT_FRAME_FLAGS
    } else {
        &[]
    };
    let res = Command::new(&cc)
        .args([
            olevel.as_str(),
            "-flto=thin",
            "-ffp-contract=off",
            "-Wno-override-module",
        ])
        .args(rt_checks)
        .args(native_kont_frame_flags)
        .args(extra.split_whitespace())
        .arg(ir)
        .args(&sources)
        .arg(&libm_archive)
        .arg("-o")
        .arg(out)
        .output()
        .map_err(|e| Error::Codegen(format!("running {cc}: {e} (is clang installed?)")));
    let _ = fs::remove_dir_all(&rt_dir);
    let cc_out = res?;
    if cc_out.status.success() {
        if !cc_out.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&cc_out.stderr));
        }
        Ok(())
    } else {
        Err(ir_failure(&cc, ir, &cc_out.stderr))
    }
}

pub(super) fn ir_failure(tool: &str, ir: &Path, stderr: &[u8]) -> Error {
    let ext = ir.extension().and_then(|e| e.to_str()).unwrap_or("ll");
    let kept = env::temp_dir().join(format!("prism_failed.{ext}"));
    let _ = fs::copy(ir, &kept);
    let text = String::from_utf8_lossy(stderr);
    let head: Vec<&str> = text.lines().take(8).collect();
    Error::Codegen(format!(
        "{tool} rejected generated IR, kept at {}:\n{}",
        kept.display(),
        head.join("\n")
    ))
}
