//! Corpus discovery and interpreter-reference helpers shared by the parity
//! oracles (`tests/parity.rs`, `tests/tier_parity.rs`). One definition of "the
//! runnable corpus" keeps the two gates diffing the same programs.

// Each test target compiles this module independently and not every target
// uses every helper, so per-target dead-code analysis would otherwise warn. A
// test binary is its own crate root, so `pub` here is crate-visible only;
// rustc's unreachable_pub and clippy's redundant_pub_crate disagree about the
// spelling, and we side with plain `pub`.
#![allow(dead_code, unreachable_pub)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs, thread};

use prism::error::Error;
use prism::eval::{Run, Rv};

/// Type-directed generator of small well-typed programs for the differential
/// determinism gate; shared so every fuzz harness diffs the same fragment.
pub mod fuzzgen;

/// A clean run under `PRISM_CHECK_LEAKS` writes exactly this to stderr.
const LEAK_OK: &str = "prism: 0 cells leaked";
/// The env var that turns on the runtime's live-cell balance report.
const CHECK_LEAKS: &str = "PRISM_CHECK_LEAKS";
/// Opt-in memoization of verified native cases: set it to skip programs whose
/// complete toolchain fingerprint is unchanged since a previous green run.
const GATE_CACHE: &str = "PRISM_GATE_CACHE";
/// Selects how the compiler half of the cache key is fingerprinted. Unset (the
/// default) hashes the test executable itself, maximally conservative and stable
/// between local runs where cargo does not rebuild. Set to `source` to hash the
/// compiler's source inputs instead (`src/`, `runtime/`, `lib/`, the manifests),
/// a fingerprint that is reproducible across machines, so a persisted cache hits
/// across CI runners where the executable is not byte-reproducible.
const GATE_FINGERPRINT: &str = "PRISM_GATE_FINGERPRINT";
/// The value of `PRISM_GATE_FINGERPRINT` that selects the source-tree hash.
const FINGERPRINT_SOURCE: &str = "source";
/// The compiler-source roots hashed in `source` fingerprint mode: everything that
/// compiles into the test binary and can therefore move native output. A change
/// under any of these re-runs the whole gate; a change elsewhere (docs, plans)
/// leaves the cache warm.
const COMPILER_SOURCE_ROOTS: &[&str] = &[
    "src",
    "runtime",
    "lib",
    "build.rs",
    "Cargo.lock",
    "Cargo.toml",
    "rust-toolchain.toml",
];
/// The backend-opt level the native build compiles at, part of the cache key so
/// a different `-O` invalidates. Mirrors the driver default.
const DEFAULT_BACKEND_OPT: &str = "2";
/// Environment knobs that can change generated code, runtime behavior, or the
/// diagnostics a gate treats as build-affecting. These are identity inputs for
/// cached native oracle artifacts, not hidden ambient state.
const BEHAVIOR_ENV: &[&str] = &[
    "PRISM_NATIVE_EFFECTS",
    "PRISM_TRAMPOLINE",
    "PRISM_CORE_LINT",
    "PRISM_RT_CHECKS",
    "PRISM_NATIVE_KONT_FRAMES",
    "PRISM_OPT_LEVEL",
    "PRISM_BACKEND_OPT",
    "PRISM_NO_SPECIALIZE",
    "PRISM_FUSE",
    "PRISM_SCHEDULER",
    "PRISM_EFFECT_TIER",
    "PRISM_CC_FLAGS",
];

#[derive(Debug)]
pub struct TempDir {
    path: PathBuf,
}

impl TempDir {
    pub fn new(scope: &str, tag: &str) -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path = env::temp_dir().join(format!(
            "prism-{scope}-{tag}-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn join(&self, path: impl AsRef<Path>) -> PathBuf {
        self.path.join(path)
    }

    pub fn store_root(&self) -> PathBuf {
        self.path.join("store")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

pub fn cc() -> String {
    env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

pub fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Assert a C compiler is reachable, panicking with an actionable message if
/// not. The native oracles are meaningless without one, so its absence fails
/// the test loudly rather than passing vacuously.
pub fn require_cc() {
    assert!(
        have(&cc()),
        r"C compiler `{}` not found (set PRISM_CC). The native parity oracle requires it; install clang or LLVM so the native backend is exercised.",
        cc()
    );
}

pub fn source(path: &Path) -> String {
    prism::with_prelude(&fs::read_to_string(path).unwrap())
}

/// The interpreter's real terminal output, byte-for-byte what a native binary's
/// stdout must equal. `term` (not a join over `out`) preserves the
/// print/println distinction: a bare `print` adds no newline.
pub fn interpreted(full: &str) -> String {
    prism::interpret(full).unwrap().term
}

/// The bit width of the runtime's signed tagged immediate: a value is stored as
/// `(n << 1) | 1`, so magnitudes below `2^62` are immediates and anything wider
/// is a heap bignum.
const TAGGED_IMMEDIATE_BITS: u32 = 62;

/// A signed value that native's `main` shim returns as a tagged immediate (an odd
/// word it shifts back into an exit code), as opposed to a heap bignum, which it
/// treats as non-immediate and exits 0 for.
fn fits_tagged_immediate(n: i64) -> bool {
    let lo = -(1i64 << TAGGED_IMMEDIATE_BITS);
    let hi = (1i64 << TAGGED_IMMEDIATE_BITS) - 1;
    (lo..=hi).contains(&n)
}

/// The process exit code the interpreter's result implies, derived exactly as the
/// native `main` shim derives it from `prismfn_main`'s return word so the two are
/// directly comparable. An explicit `exit(n)` wins; otherwise a tagged-immediate
/// integer or boolean return becomes the code and every other value (Unit, a heap
/// cell, a bignum too wide to tag) exits 0. The OS reports only the low 8 bits, so
/// the result is masked to a `u8`, matching what a native process reports back.
// The truncations are the point: native narrows the immediate to `int` at exit
// and the kernel then reports only the low byte, so mirroring both is what makes
// the two exit codes comparable.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
pub fn canonical_exit(run: &Run) -> u8 {
    let code = run.exit.unwrap_or_else(|| match run.value {
        Rv::Int(n) | Rv::I64(n) if fits_tagged_immediate(n) => n as i32,
        Rv::Bool(b) => i32::from(b),
        _ => 0,
    });
    code as u8
}

/// The corpus directories, relative to the crate root.
const CORPUS_DIRS: [&str; 2] = ["examples", "tests/cases/run"];

/// Committed `.pr` programs intentionally outside the runnable corpus, each with
/// why. `corpus_skip_list_is_exact` (tests/parity.rs) asserts the set of programs
/// that actually drop out of `corpus()` equals these keys, so a regression that
/// silently stops a program interpreting (which would quietly shrink every oracle
/// built on the corpus) fails CI by name, and a program that becomes runnable
/// again is flagged here as a stale entry. Labels are `dir/name.pr`.
pub const CORPUS_SKIPS: &[(&str, &str)] = &[
    ("examples/capabilities.pr", "off-platform: getenv"),
    ("examples/durable.pr", "off-platform: file IO + eprint"),
    (
        "examples/incr_trace.pr",
        "off-platform: file IO (durable trace-replay Incr snapshot)",
    ),
    (
        "examples/incr_warm.pr",
        "off-platform: file IO (durable Incr snapshot)",
    ),
    (
        "examples/game.pr",
        "interactive: blocks on read_int over empty stdin",
    ),
    (
        "examples/greet.pr",
        "off-platform: file_exists/read_file (the lineage chapter's input-file demo)",
    ),
    ("examples/os.pr", "off-platform: file IO + getenv"),
    (
        "examples/sandbox.pr",
        "off-platform: read_file/file_exists (a handler stubs them, but detection is syntactic)",
    ),
    ("tests/cases/run/fs.pr", "off-platform: file IO"),
    (
        "tests/cases/run/fs_bytes.pr",
        "off-platform: byte-level file IO",
    ),
];

/// Every committed `.pr` under the corpus directories, as `(dir/name.pr, path)`,
/// sorted. The single discovery pass behind `corpus()` and `corpus_drops()`.
fn candidates() -> Vec<(String, PathBuf)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for dir in CORPUS_DIRS {
        for entry in fs::read_dir(root.join(dir)).unwrap().flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("pr") {
                continue;
            }
            let label = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            out.push((label, path));
        }
    }
    out.sort();
    out
}

/// The corpus membership predicate: the interpreter runs `full` cleanly on empty
/// stdin and it stays on this platform (no file/env IO). The interpret-Ok arm
/// excludes error cases, no-`main` library files, and the interactive examples
/// that block on input; the off-platform arm excludes IO whose native and
/// interpreted runs are not a pure function of the source.
fn runnable(full: &str, root: &Path) -> bool {
    let on_platform = prism::off_platform_builtins(full, root).is_ok_and(|ops| ops.is_empty());
    on_platform && prism::interpret(full).is_ok()
}

/// The runnable corpus: every candidate satisfying `runnable`.
pub fn corpus() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    candidates()
        .into_iter()
        .filter(|(_, p)| runnable(&source(p), root))
        .map(|(_, p)| p)
        .collect()
}

/// Env var naming how many CI shards the corpus is split across; unset or `<= 1`
/// runs the whole corpus. Paired with [`SHARD_INDEX_ENV`].
const SHARD_TOTAL_ENV: &str = "PRISM_SHARD_TOTAL";
/// Env var naming this shard's 0-based index (`0 <= index < total`).
const SHARD_INDEX_ENV: &str = "PRISM_SHARD_INDEX";

/// Partition a sorted corpus for CI sharding: with `PRISM_SHARD_TOTAL=n` (n > 1)
/// set, keep only the cases whose position mod n equals `PRISM_SHARD_INDEX`, so n
/// parallel CI jobs cover the corpus between them. Unset or `n <= 1` returns the
/// list unchanged, so local runs and the tier oracle are unaffected. The corpus is
/// already sorted, so the partition is identical on every machine.
pub fn shard(cases: Vec<PathBuf>) -> Vec<PathBuf> {
    let total = env::var(SHARD_TOTAL_ENV)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(1);
    if total <= 1 {
        return cases;
    }
    let index = env::var(SHARD_INDEX_ENV)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0);
    shard_by(cases, total, index)
}

/// The pure index-mod-total split behind [`shard`]: keep the cases at positions
/// `p` with `p % total == index % total`. Over `index in 0..total` the results are
/// disjoint and cover every case exactly once.
pub fn shard_by(cases: Vec<PathBuf>, total: usize, index: usize) -> Vec<PathBuf> {
    let index = index % total;
    cases
        .into_iter()
        .enumerate()
        .filter(move |(i, _)| i % total == index)
        .map(|(_, p)| p)
        .collect()
}

/// The committed programs that drop out of `corpus()`, as their `dir/name.pr`
/// labels. Compared against `CORPUS_SKIPS` to catch silent corpus shrinkage.
pub fn corpus_drops() -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    candidates()
        .into_iter()
        .filter(|(_, p)| !runnable(&source(p), root))
        .map(|(label, _)| label)
        .collect()
}

/// Remove a case's native binary and its intermediate `.bc`/`.ll` artifacts.
pub fn cleanup_bin(bin: &Path) {
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(bin);
}

/// A per-case, per-process temp path for a native binary. The process id keeps
/// concurrent test binaries (parity vs tier) from colliding.
pub fn temp_bin(tag: &str, stem: &str) -> PathBuf {
    env::temp_dir().join(format!("prism_parity_{tag}_{}_{stem}", std::process::id()))
}

/// The single leak predicate for every native oracle. The parity harness sets
/// only `PRISM_CHECK_LEAKS` (the reuse/effop/drive counters are behind their own
/// env vars), so a correct run's stderr is exactly the leak line and stdout is
/// untouched. Whole-stderr equality is therefore the right check: it also fails
/// on a stray `fatal:`/`prism_rt:` abort line or a nonzero balance, which a
/// substring search for the leak line would let slip through.
pub fn leak_free(stderr: &str) -> bool {
    stderr.trim_end() == LEAK_OK
}

/// A content fingerprint of everything outside the program source that can move
/// its native output or leak result: the test executable itself (any change to
/// the frontend, codegen, or the `runtime.c` embedded via `include_str!` rebuilds
/// it, so its hash stands in for the whole compiler), the C compiler in use and
/// its version string, the backend-opt level, and the extra `PRISM_CC_FLAGS`
/// handed to the linker. The last matters for CI: the ASan/UBSan and
/// `-DPRISM_RT_DEBUG` re-runs of the parity corpus differ from the plain run only
/// in those flags, so without them in the key those hardening passes would share
/// a key with the plain build and be wrongly skipped. Computed once. Because any
/// of these moving changes the key, a stale pass can never be served after a
/// toolchain or flag change; the cache only skips work when the exact same
/// toolchain last passed.
fn compiler_fingerprint() -> &'static GateCacheIdentity {
    static FP: OnceLock<GateCacheIdentity> = OnceLock::new();
    FP.get_or_init(|| {
        let compiler = if env::var(GATE_FINGERPRINT).as_deref() == Ok(FINGERPRINT_SOURCE) {
            source_tree_hash()
        } else {
            env::current_exe()
                .ok()
                .and_then(|p| fs::read(p).ok())
                .map_or_else(String::new, |b| blake3::hash(&b).to_hex().to_string())
        };
        let clang = Command::new(cc())
            .arg("--version")
            .output()
            .ok()
            .map_or_else(String::new, |o| {
                String::from_utf8_lossy(&o.stdout).into_owned()
            });
        GateCacheIdentity::new(format!(
            "{}\0{compiler}\0{clang}\0{}",
            cc(),
            artifact_identity_context()
        ))
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateCacheIdentity {
    fingerprint: String,
}

impl GateCacheIdentity {
    const fn new(fingerprint: String) -> Self {
        Self { fingerprint }
    }

    #[cfg(test)]
    pub fn for_test(fingerprint: &str) -> Self {
        Self::new(fingerprint.to_string())
    }

    fn as_str(&self) -> &str {
        &self.fingerprint
    }
}

pub fn artifact_identity_context() -> String {
    let mut out = String::new();
    out.push_str("compiler-version=");
    out.push_str(env!("CARGO_PKG_VERSION"));
    out.push('\0');
    out.push_str("hash-scheme=");
    out.push_str(prism::core::HASH_SCHEME);
    out.push('\0');
    out.push_str("target=");
    out.push_str(env!("PRISM_TARGET"));
    out.push('\0');
    out.push_str("features=");
    out.push_str(compiled_features());
    out.push('\0');
    for name in BEHAVIOR_ENV {
        out.push_str(name);
        out.push('=');
        let value = match *name {
            "PRISM_BACKEND_OPT" => {
                env::var(name).unwrap_or_else(|_| DEFAULT_BACKEND_OPT.to_string())
            }
            _ => env::var(name).unwrap_or_default(),
        };
        out.push_str(&value);
        out.push('\0');
    }
    out
}

const fn compiled_features() -> &'static str {
    match (
        cfg!(feature = "native"),
        cfg!(feature = "mlir"),
        cfg!(feature = "wasm"),
        cfg!(feature = "mimalloc"),
    ) {
        (true, true, _, true) => "native,mlir,mimalloc",
        (true, true, _, false) => "native,mlir",
        (true, false, _, true) => "native,mimalloc",
        (true, false, _, false) => "native",
        (false, _, true, true) => "wasm,mimalloc",
        (false, _, true, false) => "wasm",
        (false, _, false, true) => "mimalloc",
        (false, _, false, false) => "",
    }
}

/// A reproducible hash of the compiler's source inputs (`COMPILER_SOURCE_ROOTS`):
/// every file under those roots, path and contents, in sorted order. Content-only
/// and order-stable, so two checkouts of the same commit on different machines
/// hash identically, which is what lets a persisted cache hit across CI runners.
/// The `source` fingerprint mode uses this in place of the executable's bytes.
fn source_tree_hash() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for rel in COMPILER_SOURCE_ROOTS {
        let p = root.join(rel);
        if p.is_dir() {
            collect_files(&p, &mut files);
        } else if p.is_file() {
            files.push(p);
        }
    }
    files.sort();
    let mut h = blake3::Hasher::new();
    for f in &files {
        if let Ok(rel) = f.strip_prefix(root) {
            h.update(rel.to_string_lossy().as_bytes());
            h.update(b"\0");
        }
        if let Ok(bytes) = fs::read(f) {
            h.update(&(bytes.len() as u64).to_le_bytes());
            h.update(&bytes);
        }
    }
    h.finalize().to_hex().to_string()
}

/// Collect every regular file under `dir`, recursively, into `out`.
fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect_files(&p, out);
            } else if p.is_file() {
                out.push(p);
            }
        }
    }
}

/// The cache directory when memoization is enabled, else `None`. Lives under
/// `target/` so `cargo clean` clears it and it never enters version control.
fn gate_cache_dir() -> Option<PathBuf> {
    env::var_os(GATE_CACHE)?;
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("gate-cache");
    fs::create_dir_all(&dir).ok()?;
    Some(dir)
}

/// The cache key for a verified case: a hash over the compiler fingerprint, the
/// oracle tag (a program passes `llvm` and `mlir` independently), and the full
/// prelude-prepended source. Any input change moves the key.
fn cache_key(full: &str, tag: &str) -> String {
    cache_key_with_identity(full, tag, compiler_fingerprint())
}

pub fn cache_key_with_identity(full: &str, tag: &str, identity: &GateCacheIdentity) -> String {
    let mut h = blake3::Hasher::new();
    h.update(identity.as_str().as_bytes());
    h.update(b"\0");
    h.update(tag.as_bytes());
    h.update(b"\0");
    h.update(full.as_bytes());
    h.finalize().to_hex().to_string()
}

/// Build `case` with `build`, run it under leak checking on empty stdin, and
/// diff stdout (byte-for-byte) and the leak report against the interpreter. The
/// one native build/run/diff/leak path behind both parity oracles; `tag` names
/// the backend (`llvm`/`mlir`) or the forced tier for messages and temp paths.
///
/// When `PRISM_GATE_CACHE` is set, a case whose toolchain fingerprint matches a
/// prior green run is skipped: its result is a pure function of the key, so a
/// recorded pass is as good as a fresh one. Only passes are recorded, so a
/// failing case is always re-run, and the full cold gate is one `cargo clean`
/// (or an unset env) away.
pub fn check_native_parity(
    case: &Path,
    tag: &str,
    build: impl Fn(&str, &Path) -> Result<(), Error>,
) -> Result<(), String> {
    let full = source(case);
    let cache = gate_cache_dir();
    let key = cache.as_ref().map(|_| cache_key(&full, tag));
    if let (Some(dir), Some(k)) = (&cache, &key) {
        if dir.join(k).exists() {
            return Ok(());
        }
    }
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = temp_bin(tag, &stem);
    if let Err(e) = build(&full, &bin) {
        cleanup_bin(&bin);
        return Err(format!("{}: {tag} build failed: {e}", case.display()));
    }
    let run = Command::new(&bin).env(CHECK_LEAKS, "1").output();
    cleanup_bin(&bin);
    let out = match run {
        Ok(o) => o,
        Err(e) => return Err(format!("{}: spawn failed: {e}", case.display())),
    };
    // The interpreter reference: its streamed stdout and the exit code its result
    // implies (`canonical_exit`), both compared against the native process.
    let reference = prism::interpret(&full).unwrap();
    let want = &reference.term;
    // A program whose `main` returns a tagged-immediate value exits with that
    // value as its code; `canonical_exit` reconstructs it the way the native
    // `main` shim does, so exit-code divergence (the class the `error`/`exit`
    // seam exposed) is now inside the oracle, not just the empty-stdin instances.
    // A crash by signal reports no code and diverges here as well as truncating
    // stdout above.
    let want_exit = canonical_exit(&reference);
    let Some(got_exit) = out.status.code() else {
        return Err(format!(
            "{tag} process faulted for {} without an exit code",
            case.display()
        ));
    };
    let leak = String::from_utf8_lossy(&out.stderr);
    let native_stderr = leak
        .lines()
        .filter(|line| !line.starts_with("prism: ") || !line.ends_with(" cells leaked"))
        .collect::<Vec<_>>()
        .join("\n");
    let native_trace = prism::ObservationTrace::from_process(
        &out.stdout,
        native_stderr.as_bytes(),
        got_exit & 0xFF,
    );
    let interpreter_trace =
        prism::ObservationTrace::from_process(want.as_bytes(), &[], i32::from(want_exit));
    if native_trace != interpreter_trace {
        return Err(format!(
            "{tag} observation trace diverges for {}:\n  native: {:?}\n  interp: {:?}",
            case.display(),
            native_trace.observations,
            interpreter_trace.observations
        ));
    }
    if !leak_free(&leak) {
        return Err(format!(
            "{}: {tag} did not free all cells: {}",
            case.display(),
            leak.trim()
        ));
    }
    // Record the pass: an empty marker named by the key. Only reached on a full
    // verification, so a failing case never leaves a marker to skip it later.
    if let (Some(dir), Some(k)) = (&cache, &key) {
        let _ = fs::write(dir.join(k), b"");
    }
    Ok(())
}

/// Worker stack size for corpus fan-out. The in-process interpreter's recursion
/// depth is corpus-dependent (deep non-tail folds recurse per element), and its
/// real budget has always been the CLI main thread's 8MB, not the 2MB default of
/// a spawned test thread. Reserve generously: the reservation is virtual and
/// pages commit only on use, so the cost of headroom is nothing and the cost of
/// too little is a corpus-wide abort that names no culprit.
const CORPUS_WORKER_STACK: usize = 256 * 1024 * 1024;

/// Run `check` over `cases` across cores, collecting every failure so one run
/// reports all divergences rather than aborting at the first. Returns the
/// failure messages; callers assert emptiness with their own summary.
pub fn parallel_check(
    cases: &[PathBuf],
    check: impl Fn(&Path) -> Result<(), String> + Sync,
) -> Vec<String> {
    let next = AtomicUsize::new(0);
    let fails: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let threads = thread::available_parallelism()
        .map_or(4, std::num::NonZeroUsize::get)
        .min(cases.len().max(1));
    thread::scope(|s| {
        for _ in 0..threads {
            let worker = || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let Some(case) = cases.get(i) else { break };
                if let Err(e) = check(case) {
                    fails.lock().unwrap().push(e);
                }
            };
            thread::Builder::new()
                .stack_size(CORPUS_WORKER_STACK)
                .spawn_scoped(s, worker)
                .expect("spawning corpus worker");
        }
    });
    fails.into_inner().unwrap()
}
