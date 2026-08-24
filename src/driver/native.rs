use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::error::Error;
use crate::lineage::FactOutcome;
use prism_native::rt::{cc, cc_flags, write_libm_archive, write_runtime_for, RuntimeProfile};

use super::cache::NativeArtifactCache;
use super::scheduler::QueryScheduler;
use super::{Config, NATIVE_KONT_FRAME_FLAGS};

const THIN_LTO_FLAG: &str = "-flto=thin";
const NO_FP_CONTRACT_FLAG: &str = "-ffp-contract=off";
const NO_OVERRIDE_MODULE_WARNING_FLAG: &str = "-Wno-override-module";
const COMPILE_ONLY_FLAG: &str = "-c";
const OUTPUT_FLAG: &str = "-o";
const LLD_FLAG: &str = "-fuse-ld=lld";
const VERSION_FLAG: &str = "--version";
/// Asks the driver where it would find a program, without building any job.
const PRINT_PROG_NAME_FLAG: &str = "-print-prog-name=";
const LLD_PROGRAM: &str = "ld.lld";
const DEFAULT_LINKER_PROGRAM: &str = "ld";
/// Stands in for a toolchain component whose own banner could not be read.
const UNKNOWN_COMPONENT: &str = "unavailable";
/// Names the linker when the driver would not say which one it launches.
const PLATFORM_LINKER: &str = "platform";

/// Direct C-toolchain work performed by one native link.
///
/// The phase timer reports the wall clock around the whole link. These counters
/// expose the multiplicative work inside it: subprocess time is summed over the
/// direct compiler commands (including a configured wrapper), while cache hits
/// name runtime objects materialized without launching that command at all.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct CcLinkStats {
    pub probe_invocations: usize,
    pub probe_time: Duration,
    pub compile_invocations: usize,
    pub compile_time: Duration,
    pub link_invocations: usize,
    pub link_time: Duration,
    pub runtime_object_hits: usize,
    pub runtime_object_misses: usize,
}

impl CcLinkStats {
    pub(super) const fn invocations(self) -> usize {
        self.probe_invocations + self.compile_invocations + self.link_invocations
    }

    fn record_object(&mut self, object: ObjectCompileStats, runtime: bool) {
        match object {
            ObjectCompileStats::Hit => {
                if runtime {
                    self.runtime_object_hits += 1;
                }
            }
            ObjectCompileStats::Invoked(elapsed) => {
                self.compile_invocations += 1;
                self.compile_time += elapsed;
                if runtime {
                    self.runtime_object_misses += 1;
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
enum ObjectCompileStats {
    Hit,
    Invoked(Duration),
}

fn compile_runtime_object(
    cc: &str,
    args: &[String],
    source: &Path,
    object: &Path,
    cache: Option<&NativeArtifactCache>,
    cfg: &Config,
) -> Result<ObjectCompileStats, Error> {
    // Parallel corpus workers commonly reach the same cold runtime key at once.
    // Serialize only that first materialize/compile/store critical section so
    // one worker prebuilds each invariant object and every sibling gets a hit.
    // Program objects and final links remain fully parallel.
    static RUNTIME_COMPILE_LOCK: Mutex<()> = Mutex::new(());
    let _guard = RUNTIME_COMPILE_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    compile_object(cc, args, source, object, cache, cfg)
}

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
        format!("-O{}", cfg.backend_opt().as_str()),
        THIN_LTO_FLAG.to_string(),
        NO_FP_CONTRACT_FLAG.to_string(),
        NO_OVERRIDE_MODULE_WARNING_FLAG.to_string(),
    ];
    let macos_min = prism_native::rt::macos_deployment_target();
    if !macos_min.is_empty() {
        args.push(format!("-mmacosx-version-min={macos_min}"));
    }
    if cfg.flags.rt_checks {
        args.push("-DPRISM_RT_DEBUG".to_string());
    }
    if cfg.flags.native_kont_frames {
        args.extend(NATIVE_KONT_FRAME_FLAGS.iter().map(ToString::to_string));
    }
    args.extend(cc_flags().split_whitespace().map(ToString::to_string));
    args
}

fn compile_object(
    cc: &str,
    args: &[String],
    source: &Path,
    object: &Path,
    cache: Option<&NativeArtifactCache>,
    cfg: &Config,
) -> Result<ObjectCompileStats, Error> {
    if let Some(cache) = cache {
        if let Some(output) = cache.materialize_file(object, false)? {
            cache.record_decision(cfg, FactOutcome::Hit, Some(output), "");
            return Ok(ObjectCompileStats::Hit);
        }
    }
    let source_dir = source.parent().unwrap_or_else(|| Path::new("."));
    let source_name = source.file_name().unwrap_or(source.as_os_str());
    let object_path = if object.is_absolute() {
        object.to_path_buf()
    } else {
        env::current_dir().map_err(Error::Io)?.join(object)
    };
    let started = Instant::now();
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
    let elapsed = started.elapsed();
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
    Ok(ObjectCompileStats::Invoked(elapsed))
}

/// The first line a toolchain probe prints, memoized for the process.
///
/// Every probe is a subprocess launch on the critical path of a link and its
/// answer cannot change while the compiler runs, so each distinct command is
/// asked once. `None` reports that the command failed or said nothing; what
/// that absence means is the caller's to decide.
fn probe_line(cmd: &str, args: &[&str]) -> (Option<String>, Option<Duration>) {
    static LINES: OnceLock<Mutex<BTreeMap<String, Option<String>>>> = OnceLock::new();
    let mut key = cmd.to_string();
    for arg in args {
        key.push('\0');
        key.push_str(arg);
    }
    let lines = LINES.get_or_init(|| Mutex::new(BTreeMap::new()));
    let mut lines = lines
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(line) = lines.get(&key) {
        return (line.clone(), None);
    }
    let started = Instant::now();
    let line = Command::new(cmd)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .and_then(|output| output.lines().next().map(str::trim).map(str::to_string))
        .filter(|line| !line.is_empty());
    let elapsed = started.elapsed();
    lines.insert(key, line.clone());
    drop(lines);
    (line, Some(elapsed))
}

/// The cost of the toolchain probes one link makes.
#[derive(Default)]
struct ProbeCost {
    count: usize,
    time: Duration,
}

impl ProbeCost {
    /// Runs a probe and folds what it cost into the running total. A memoized
    /// answer costs nothing and is not counted.
    fn line(&mut self, cmd: &str, args: &[&str]) -> Option<String> {
        let (line, elapsed) = probe_line(cmd, args);
        if let Some(elapsed) = elapsed {
            self.count += 1;
            self.time += elapsed;
        }
        line
    }
}

/// The absolute path the driver would launch for a linker program.
///
/// This is a pure driver query: it builds no link job, needs no input file, and
/// a toolchain that does not have the program simply echoes the bare name back,
/// which is not a path and so reads as absent.
fn linker_path(cc: &str, program: &str, cost: &mut ProbeCost) -> Option<String> {
    let query = format!("{PRINT_PROG_NAME_FLAG}{program}");
    let path = cost.line(cc, &[&query])?;
    let found = Path::new(&path).is_absolute() && Path::new(&path).is_file();
    found.then_some(path)
}

/// Picks the linker for the final link, and names it for the fingerprint.
///
/// `ThinLTO` defers code generation and final layout to the linker, so a build's
/// bytes are a function of its inputs only when the linker is one too. `ld.lld`
/// ships with the same LLVM the rest of the pipeline is pinned to and lays its
/// inputs out in a fixed order; the Linux default is whichever linker owns `ld`
/// on the host, which may be a parallel linker whose output permutes between
/// otherwise identical runs. So pin lld wherever the toolchain has it, and fall
/// back rather than fail where it does not: an installed release must keep
/// linking on a host that never shipped lld, and naming the fallback here keeps
/// any artifact from crossing between the two. Apple platforms keep `ld64`,
/// which orders its output deterministically already and is the linker their
/// SDK is built against.
fn resolve_linker(cc: &str, cost: &mut ProbeCost) -> (Option<&'static str>, String) {
    if cfg!(target_os = "macos") {
        return (None, PLATFORM_LINKER.to_string());
    }
    let lld = linker_path(cc, LLD_PROGRAM, cost);
    let flag = lld.is_some().then_some(LLD_FLAG);
    let Some(path) = lld.or_else(|| linker_path(cc, DEFAULT_LINKER_PROGRAM, cost)) else {
        return (flag, PLATFORM_LINKER.to_string());
    };
    // The banner moves when the linker is upgraded in place; the path does not,
    // so prefer it and keep the path only as the coarser fallback.
    let name = cost.line(&path, &[VERSION_FLAG]).unwrap_or(path);
    (flag, name)
}

/// The external C toolchain one native link runs through.
///
/// Resolved once per link so the fingerprint that keys cached objects and the
/// command line that produces them can never disagree about which tools ran.
struct Toolchain {
    cc: String,
    cc_version: String,
    /// Selects the linker, absent when the platform default is taken.
    linker_flag: Option<&'static str>,
    linker: String,
    probes: usize,
    probe_time: Duration,
}

impl Toolchain {
    /// Probes the compiler, and the linker the final link will hand its work to.
    fn resolve() -> Self {
        let cc = cc();
        let mut cost = ProbeCost::default();
        let cc_version = cost
            .line(&cc, &[VERSION_FLAG])
            .unwrap_or_else(|| UNKNOWN_COMPONENT.to_string());
        let (linker_flag, linker) = resolve_linker(&cc, &mut cost);
        Self {
            cc,
            cc_version,
            linker_flag,
            linker,
            probes: cost.count,
            probe_time: cost.time,
        }
    }

    /// The compile flags plus whatever selects the linker.
    fn link_args(&self, args: &[String]) -> Vec<String> {
        let mut link = args.to_vec();
        link.extend(self.linker_flag.map(ToString::to_string));
        link
    }

    /// Fingerprint of the toolchain behind a compiled object.
    ///
    /// Under `ThinLTO` an object holds bitcode and the linker is what turns it
    /// into machine code, so the linker is named here alongside the compiler.
    /// It does not itself change an object's bytes; naming it anyway is the
    /// conservative reading, and it costs only a rebuild of a handful of small
    /// runtime objects on the rare occasion a linker moves. What it buys is
    /// that a cached object cannot quietly outlive the toolchain it was made
    /// for, without anyone having to keep proving that bitcode is linker-blind.
    fn object_context(&self, args: &[String]) -> String {
        let Self {
            cc,
            cc_version,
            linker,
            ..
        } = self;
        let mut context = format!(
            "target={}\0cc={cc}\0cc-version={cc_version}\0linker={linker}\0",
            env!("PRISM_TARGET"),
        );
        for arg in args {
            context.push_str(arg);
            context.push('\0');
        }
        context
    }
}

pub(super) fn cc_link(
    ir: &Path,
    out: &Path,
    cfg: &Config,
    runtime_profile: RuntimeProfile,
) -> Result<CcLinkStats, Error> {
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
) -> Result<CcLinkStats, Error> {
    let first_ir = ir.first().ok_or_else(|| {
        Error::CodegenBackend("cannot link an empty backend artifact set".to_string())
    })?;
    let toolchain = Toolchain::resolve();
    let cc = &toolchain.cc;
    let args = cc_args(cfg);
    let runtime_toolchain = toolchain.object_context(&args);
    let rt_dir = out.with_extension("prism_rt.d");
    let sources = write_runtime_for(&rt_dir, runtime_profile)?;
    let libm_archive = write_libm_archive(&rt_dir)?;
    let mut stats = CcLinkStats::default();
    stats.probe_invocations += toolchain.probes;
    stats.probe_time += toolchain.probe_time;

    // Program shards are independent compiler subprocesses writing distinct
    // objects, so they run under the bounded scheduler; results fold back in
    // input order, keeping stats and error selection deterministic.
    let shard_jobs: Vec<(usize, &PathBuf)> = ir.iter().enumerate().collect();
    let shard_results = QueryScheduler::new(cfg.flags.query_threads).map_ordered(
        &shard_jobs,
        |(index, input)| -> Result<(PathBuf, ObjectCompileStats), Error> {
            let name = format!("program-{index}");
            let object = rt_dir.join(format!("{name}.o"));
            let ir_bytes = fs::read(input)?;
            let cache = NativeArtifactCache::for_native_object(&name, &ir_bytes, cfg)?;
            let object_stats = compile_object(cc, &args, input, &object, cache.as_ref(), cfg)?;
            Ok((object, object_stats))
        },
    );
    let mut program_objects = Vec::with_capacity(ir.len());
    for result in shard_results {
        let (object, object_stats) = result?;
        stats.record_object(object_stats, false);
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
        let cache = NativeArtifactCache::for_runtime_object(
            name,
            &bytes,
            runtime_profile,
            &runtime_toolchain,
            cfg,
        )?;
        let object_stats = compile_runtime_object(cc, &args, source, &object, cache.as_ref(), cfg)?;
        stats.record_object(object_stats, true);
        runtime_objects.push(object);
    }

    let link_started = Instant::now();
    let result = Command::new(cc)
        .args(toolchain.link_args(&args))
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
    stats.link_invocations += 1;
    stats.link_time += link_started.elapsed();
    let _ = fs::remove_dir_all(&rt_dir);
    if cc_out.status.success() {
        if !cc_out.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&cc_out.stderr));
        }
        Ok(stats)
    } else {
        Err(ir_failure(cc, first_ir, &cc_out.stderr))
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
