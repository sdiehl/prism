use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::codegen::rt::{write_libm_archive, write_runtime_for, RuntimeProfile};
use crate::error::Error;
use crate::lineage::FactOutcome;

use super::cache::NativeArtifactCache;
use super::{Config, NATIVE_KONT_FRAME_FLAGS};

const THIN_LTO_FLAG: &str = "-flto=thin";
const NO_FP_CONTRACT_FLAG: &str = "-ffp-contract=off";
const NO_OVERRIDE_MODULE_WARNING_FLAG: &str = "-Wno-override-module";
const COMPILE_ONLY_FLAG: &str = "-c";
const OUTPUT_FLAG: &str = "-o";

pub(super) fn run_native(bin: &Path) -> Result<Vec<u8>, Error> {
    let out = Command::new(bin)
        .stdin(Stdio::null())
        .output()
        .map_err(Error::Io)?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(Error::CodegenBackend(format!(
            "attest: {} exited with {}",
            bin.display(),
            out.status
        )))
    }
}

fn cc_args(cfg: &Config) -> Vec<String> {
    let mut args = vec![
        format!("-O{}", cfg.backend_opt.as_str()),
        THIN_LTO_FLAG.to_string(),
        NO_FP_CONTRACT_FLAG.to_string(),
        NO_OVERRIDE_MODULE_WARNING_FLAG.to_string(),
    ];
    let macos_min = env!("PRISM_MACOSX_DEPLOYMENT_TARGET");
    if !macos_min.is_empty() {
        args.push(format!("-mmacosx-version-min={macos_min}"));
    }
    if cfg.flags.rt_checks {
        args.push("-DPRISM_RT_DEBUG".to_string());
    }
    if cfg.flags.native_kont_frames {
        args.extend(NATIVE_KONT_FRAME_FLAGS.iter().map(ToString::to_string));
    }
    args.extend(
        env::var("PRISM_CC_FLAGS")
            .unwrap_or_default()
            .split_whitespace()
            .map(ToString::to_string),
    );
    args
}

fn compile_object(
    cc: &str,
    args: &[String],
    source: &Path,
    object: &Path,
    cache: Option<&NativeArtifactCache>,
    cfg: &Config,
) -> Result<(), Error> {
    if let Some(cache) = cache {
        if let Some(output) = cache.materialize_file(object, false)? {
            cache.record_decision(cfg, FactOutcome::Hit, Some(output), "");
            return Ok(());
        }
    }
    let source_dir = source.parent().unwrap_or_else(|| Path::new("."));
    let source_name = source.file_name().unwrap_or(source.as_os_str());
    let object_path = if object.is_absolute() {
        object.to_path_buf()
    } else {
        env::current_dir().map_err(Error::Io)?.join(object)
    };
    let output = Command::new(cc)
        .current_dir(source_dir)
        .args(args)
        .arg(COMPILE_ONLY_FLAG)
        .arg(source_name)
        .arg(OUTPUT_FLAG)
        .arg(object_path)
        .output()
        .map_err(|error| {
            Error::CodegenBackend(format!("running {cc}: {error} (is clang installed?)"))
        })?;
    if !output.status.success() {
        return Err(ir_failure(cc, source, &output.stderr));
    }
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }
    if let Some(cache) = cache {
        let output = cache.store_result(object)?;
        cache.record_decision(
            cfg,
            FactOutcome::Write,
            Some(output),
            "object input or compiler configuration changed",
        );
    }
    Ok(())
}

pub(super) fn cc_link(
    ir: &Path,
    out: &Path,
    cfg: &Config,
    runtime_profile: RuntimeProfile,
) -> Result<(), Error> {
    cc_link_many(
        std::slice::from_ref(&ir.to_path_buf()),
        out,
        cfg,
        runtime_profile,
    )
}

pub(super) fn cc_link_many(
    ir: &[PathBuf],
    out: &Path,
    cfg: &Config,
    runtime_profile: RuntimeProfile,
) -> Result<(), Error> {
    let first_ir = ir.first().ok_or_else(|| {
        Error::CodegenBackend("cannot link an empty backend artifact set".to_string())
    })?;
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
    let args = cc_args(cfg);
    let rt_dir = out.with_extension("prism_rt.d");
    let sources = write_runtime_for(&rt_dir, runtime_profile)?;
    let libm_archive = write_libm_archive(&rt_dir)?;

    let mut program_objects = Vec::with_capacity(ir.len());
    for (index, input) in ir.iter().enumerate() {
        let name = format!("program-{index}");
        let object = rt_dir.join(format!("{name}.o"));
        let ir_bytes = fs::read(input)?;
        let cache = NativeArtifactCache::for_native_object(&name, &ir_bytes, cfg)?;
        compile_object(&cc, &args, input, &object, cache.as_ref(), cfg)?;
        program_objects.push(object);
    }

    let mut runtime_objects = Vec::with_capacity(sources.len());
    for (index, source) in sources.iter().enumerate() {
        let object = rt_dir.join(format!("runtime-{index}.o"));
        let bytes = fs::read(source)?;
        let name = source
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("runtime");
        let cache = NativeArtifactCache::for_runtime_object(name, &bytes, runtime_profile, cfg)?;
        compile_object(&cc, &args, source, &object, cache.as_ref(), cfg)?;
        runtime_objects.push(object);
    }

    let result = Command::new(&cc)
        .args(&args)
        .args(&program_objects)
        .args(&runtime_objects)
        .arg(&libm_archive)
        .arg(OUTPUT_FLAG)
        .arg(out)
        .output()
        .map_err(|error| {
            Error::CodegenBackend(format!("running {cc}: {error} (is clang installed?)"))
        });
    let cc_out = result?;
    let _ = fs::remove_dir_all(&rt_dir);
    if cc_out.status.success() {
        if !cc_out.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&cc_out.stderr));
        }
        Ok(())
    } else {
        Err(ir_failure(&cc, first_ir, &cc_out.stderr))
    }
}

pub(super) fn ir_failure(tool: &str, ir: &Path, stderr: &[u8]) -> Error {
    let ext = ir.extension().and_then(|e| e.to_str()).unwrap_or("ll");
    let kept = env::temp_dir().join(format!("prism_failed.{ext}"));
    let _ = fs::copy(ir, &kept);
    let text = String::from_utf8_lossy(stderr);
    let head: Vec<&str> = text.lines().take(8).collect();
    Error::CodegenBackend(format!(
        "{tool} rejected generated IR, kept at {}:\n{}",
        kept.display(),
        head.join("\n")
    ))
}
