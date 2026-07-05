use std::env;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::Command;

// The one canonical list of C runtime translation units and their headers. It is
// defined here, in exactly one place, and every consumer derives from it: this
// build script compiles each source and reruns on any change, and it also emits
// a generated manifest (below) that the embedded-runtime path in src/codegen/rt.rs
// reads, so the in-binary copy and the natively linked copy can never drift.
// Header order matters only for readers; each source pulls in what it needs by
// #include. Keep prism_internal.h first (the shared foundation).
const RUNTIME_HEADERS: &[&str] = &[
    "prism_internal.h",
    "prism_mem.h",
    "prism_string.h",
    "prism_int.h",
    "prism_float.h",
    "prism_libm.h",
    "prism_effect.h",
    "prism_array.h",
    "prism_buffer.h",
    "prism_sort.h",
    "prism_io.h",
];
const RUNTIME_SOURCES: &[&str] = &[
    "prism_mem.c",
    "prism_string.c",
    "prism_int.c",
    "prism_float.c",
    "prism_libm.c",
    "prism_effect.c",
    "prism_sort.c",
    "prism_array.c",
    "prism_buffer.c",
    "prism_io.c",
];
const RUNTIME_DIR: &str = "runtime";
// The vendored double-precision libm lives in one subdirectory (many small
// translation units that must stay separate, since musl keeps per-file static
// helpers that would collide if amalgamated). It is enumerated from disk rather
// than hand-listed, but folded into the same canonical runtime file set so the
// embedded copy, the build-script compile, and the native link step all agree.
const LIBM_SUBDIR: &str = "libm";

// Vendored libm units excluded from the compile and every native link.
// `nearbyint.c` is the only vendored file that calls libm's floating-point
// environment (`fetestexcept`/`feclearexcept`), which on glibc live in the system
// libm. No Prism operation reaches `nearbyint` (`round` lowers to `round.c`), so
// compiling it would force `-lm` onto every native link and the runtime oracle
// purely to satisfy a never-executed reference, breaking the self-contained "no
// system libm" invariant that keeps float results identical across platforms. The
// source stays vendored; re-admit it here once a Prism op needs it, and provide
// its fenv calls in-runtime rather than from the platform.
const LIBM_EXCLUDE: &[&str] = &["nearbyint.c"];

// `(relative-name, is_header)` for every vendored libm file, sorted for a stable
// manifest. Names are `libm/<file>` so they materialize into a subdirectory and
// each `#include "libm.h"` resolves from the including file's own directory.
fn libm_files(manifest_dir: &str) -> Vec<(String, bool)> {
    let dir = format!("{manifest_dir}/{RUNTIME_DIR}/{LIBM_SUBDIR}");
    let mut out: Vec<(String, bool)> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("reading {dir}: {e}"))
        .filter_map(Result::ok)
        .filter_map(|e| e.file_name().into_string().ok())
        .filter(|f| !LIBM_EXCLUDE.contains(&f.as_str()))
        .filter_map(
            |f| match Path::new(&f).extension().and_then(OsStr::to_str) {
                Some("h") => Some((format!("{LIBM_SUBDIR}/{f}"), true)),
                Some("c") => Some((format!("{LIBM_SUBDIR}/{f}"), false)),
                _ => None, // COPYRIGHT, README.md
            },
        )
        .collect();
    out.sort();
    out
}

fn main() {
    println!("cargo:rerun-if-changed=src/syntax/grammar.lalrpop");
    lalrpop::process_root().unwrap();
    // The target triple for the banner; TARGET is set by cargo for build scripts.
    println!(
        "cargo:rustc-env=PRISM_TARGET={}",
        env::var("TARGET").unwrap_or_default()
    );

    // The C compiler that builds the runtime and the vendored libm. It MUST be the
    // same compiler the native backend links generated programs with (`cc_link` in
    // src/driver/mod.rs), because musl's transcendentals (sin/atan/exp/...) are not
    // IEEE-correctly-rounded: their last bit is a function of the toolchain, so a
    // gcc-built interpreter libm and a clang-built native libm disagree by ~1 ULP
    // and break float parity. We resolve it exactly as `cc_link` does (`PRISM_CC`,
    // else clang) and bake the choice plus its version in, so the native backend
    // and the runtime oracle default to this identical compiler rather than each
    // guessing a system default. Optimization level is a second toolchain input to
    // those same functions (clang -O0 and -O2 disagree by a ULP on atan even with
    // FP contraction off): the interpreter libm here is fixed at -O2, and the
    // native link uses -O2 by default, so they agree on the default path. Making
    // the libm opt level independent of the program's -O is the remaining step to
    // close the contract fully (see cc_link).
    println!("cargo:rerun-if-env-changed=PRISM_CC");
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| "clang".into());
    println!("cargo:rustc-env=PRISM_BUILD_CC={cc}");
    let cc_version = Command::new(&cc)
        .arg("--version")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(str::trim).map(str::to_string))
        .unwrap_or_default();
    println!("cargo:rustc-env=PRISM_BUILD_CC_VERSION={cc_version}");

    // Emit the embedded-runtime manifest for src/codegen/rt.rs. Generated for every
    // target (including wasm, which compiles rt.rs but not the C) so the include!
    // always resolves; the include_str! paths are absolute so they resolve from
    // OUT_DIR. Headers are flagged so the native-compile path can write them beside
    // the sources without handing them to the compiler as translation units.
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut manifest = String::from("pub static RUNTIME_FILES: &[(&str, &str, bool)] = &[\n");
    let libm = libm_files(&manifest_dir);
    // The vendored libm is deliberately NOT in this manifest: the native backend
    // links the single pre-built archive `libprism_libm.a` (embedded via
    // include_bytes! in codegen::rt) instead of recompiling the sources, so the
    // interpreter and every native binary share one byte-identical libm.
    // Recompiling it a second, different way (the cc-rs invocation below vs the raw
    // clang link in cc_link) is what made the non-correctly-rounded transcendentals
    // diverge by a ULP. `prism_libm.c` (a RUNTIME_SOURCE) still declares and calls
    // the standard names; they resolve from the linked archive.
    let entries = RUNTIME_HEADERS
        .iter()
        .map(|name| ((*name).to_string(), true))
        .chain(
            RUNTIME_SOURCES
                .iter()
                .map(|name| ((*name).to_string(), false)),
        );
    for (name, is_header) in entries {
        let abs = format!("{manifest_dir}/{RUNTIME_DIR}/{name}");
        writeln!(
            manifest,
            "    ({name:?}, include_str!({abs:?}), {is_header}),"
        )
        .unwrap();
        println!("cargo:rerun-if-changed={RUNTIME_DIR}/{name}");
    }
    manifest.push_str("];\n");
    let out_dir = env::var("OUT_DIR").unwrap();
    fs::write(Path::new(&out_dir).join("runtime_manifest.rs"), manifest).unwrap();

    // The C runtime is linked only into natively compiled programs; a wasm build
    // runs the interpreter alone, so skip it (and the bogus -lm).
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("wasm32") {
        let mut rt = cc::Build::new();
        rt.compiler(&cc).include(RUNTIME_DIR).opt_level(2);
        // FP contraction stays off everywhere the runtime is compiled, matching
        // the native link step: an FMA fused on one platform and not another
        // breaks byte-for-byte float parity with the interpreter.
        rt.flag("-ffp-contract=off");
        for src in RUNTIME_SOURCES {
            rt.file(format!("{RUNTIME_DIR}/{src}"));
        }
        // Opt-in mimalloc: the `libmimalloc-sys` crate (pulled in by the feature)
        // provides the `mi_*` symbols; the runtime shim declares and routes to
        // them, so we only flip the define here, no in-tree allocator source.
        if env::var_os("CARGO_FEATURE_MIMALLOC").is_some() {
            rt.define("PRISM_MIMALLOC", None);
        }
        rt.compile("prism_rt");

        // The vendored libm is compiled as a separate archive with warnings off:
        // it is verbatim third-party code whose FORCE_EVAL idiom trips
        // -Wunused-but-set-variable, and it is not ours to lint. Same
        // -ffp-contract=off pin. Each unit resolves its `#include "libm.h"` from
        // its own directory, so no extra include path is needed.
        let mut libm_rt = cc::Build::new();
        libm_rt
            .compiler(&cc)
            .opt_level(2)
            .warnings(false)
            .flag("-ffp-contract=off");
        for (name, is_header) in &libm {
            if !is_header {
                libm_rt.file(format!("{RUNTIME_DIR}/{name}"));
            }
        }
        libm_rt.compile("prism_libm");
        // Export the exact archive path so codegen::rt can embed it (include_bytes!)
        // and the native backend links THESE bytes, never a recompile. One libm,
        // shared by the interpreter and every native binary.
        println!("cargo:rustc-env=PRISM_LIBM_ARCHIVE={out_dir}/libprism_libm.a");
        // No `-lm`: the vendored libm above provides every math symbol. Linking
        // the system libm is the actual source of cross-platform float
        // divergence, so it is deliberately absent from every native link.
    }
}
