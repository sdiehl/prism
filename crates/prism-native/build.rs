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
    "prism_arena.h",
    "prism_mem.h",
    "prism_string.h",
    "prism_int.h",
    "prism_float.h",
    "prism_libm.h",
    "prism_libm_rename.h",
    "prism_effect.h",
    "prism_array.h",
    "prism_buffer.h",
    "prism_tbuf.h",
    "prism_simd.h",
    "prism_sort.h",
    "prism_kont.h",
    "prism_io.h",
];
const RUNTIME_SOURCES: &[&str] = &[
    "prism_arena.c",
    "prism_mem.c",
    "prism_string.c",
    "prism_int.c",
    "prism_float.c",
    "prism_libm.c",
    "prism_effect.c",
    "prism_sort.c",
    "prism_array.c",
    "prism_buffer.c",
    "prism_tbuf.c",
    "prism_simd.c",
    "prism_kont.c",
    "prism_io.c",
];
const RUNTIME_DIR: &str = "../../runtime";
// The vendored double-precision libm lives in one subdirectory (many small
// translation units that must stay separate, since musl keeps per-file static
// helpers that would collide if amalgamated). It is enumerated from disk rather
// than hand-listed, but folded into the same canonical runtime file set so the
// embedded copy, the build-script compile, and the native link step all agree.
const LIBM_SUBDIR: &str = "libm";

// The C warning set, held in one file the lint gates read too, so the ordinary
// cargo build reports what they report instead of only surfacing a warning in a
// hook that not every path runs. See the file for why `-Werror` is not in it.
const RUNTIME_WARNINGS: &str = "warnings.txt";

// The warning flags, comments and blank lines dropped.
fn warning_flags(manifest_dir: &str) -> Vec<String> {
    let path = format!("{manifest_dir}/{RUNTIME_DIR}/{RUNTIME_WARNINGS}");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {path}: {e}"));
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_string)
        .collect()
}

// The header carrying the runtime's cell ABI: the reserved heap-tag family and
// the header-word layout. The generated mirror below is parsed out of it, so
// admitting a new runtime cell kind is one line in C and zero here.
const ABI_HEADER: &str = "prism_internal.h";

// The layout defines mirrored into Rust alongside the tag family. Each is a
// plain numeric define; a missing one is a build error, not a silent zero.
const ABI_RC_WORD: &str = "PRISM_RC_W";
const ABI_TAG_WORD: &str = "PRISM_TAG_W";
const ABI_ARITY_WORD: &str = "PRISM_ARITY_W";
const ABI_HEADER_WORDS: &str = "PRISM_HDR_WORDS";
const ABI_WORD_BYTES: &str = "PRISM_WORD_BYTES";
const ABI_STATIC_CELL: &str = "PRISM_STATIC_CELL";

// The reserved-tag family must at least contain the four cell kinds the runtime
// has always claimed; fewer means the parser regressed, not that C shrank.
const ABI_MIN_HEAP_TAGS: usize = 4;
const EXPECTED_RC_WORD_INDEX: i64 = 0;
const ARITY_TRAILING_WORDS: i64 = 1;
const C_HEX_PREFIX: &str = "0x";
const C_LONG_SUFFIX: char = 'L';
const HEX_RADIX: u32 = 16;
const HEX_GROUP_DIGITS: usize = 4;

// A `#define NAME value` numeric define: decimal or 0x hex with an optional L
// suffix, or the parenthesized single-shift form `(1L << n)` the rc-word
// marker bits use. General expressions are still not parsed; nothing else in
// the mirrored ABI needs them.
fn c_define(header: &str, name: &str) -> Option<i64> {
    let prefix = format!("#define {name} ");
    let raw = header.lines().find_map(|l| l.strip_prefix(&prefix))?.trim();
    if let Some(inner) = raw.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        let (base, shift) = inner.split_once("<<")?;
        let base = base.trim();
        let base = base.strip_suffix(C_LONG_SUFFIX).unwrap_or(base);
        return base
            .parse::<i64>()
            .ok()?
            .checked_shl(shift.trim().parse().ok()?);
    }
    let raw = raw.strip_suffix(C_LONG_SUFFIX).unwrap_or(raw);
    raw.strip_prefix(C_HEX_PREFIX).map_or_else(
        || raw.parse().ok(),
        |hex| i64::from_str_radix(hex, HEX_RADIX).ok(),
    )
}

fn required_c_define(header: &str, name: &str) -> i64 {
    c_define(header, name).unwrap_or_else(|| panic!("{ABI_HEADER} no longer defines {name}"))
}

// Every `#define PRISM_*_TAG <number>` in the ABI header, in definition order:
// the heap tags the runtime claims for its own cell kinds.
fn heap_tags(header: &str) -> Vec<(String, i64)> {
    header
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("#define ")?;
            let (name, _) = rest.split_once(' ')?;
            if !(name.starts_with("PRISM_") && name.ends_with("_TAG")) {
                return None;
            }
            Some((name.to_string(), c_define(header, name)?))
        })
        .collect()
}

// Rust-readable hex with a separator every four digits from the right. The ABI
// tags are bit patterns, so retaining hex in the generated mirror is useful;
// grouping keeps the generated source under the workspace's literal lint.
fn rust_hex(value: i64) -> String {
    assert!(value >= 0, "runtime ABI tags must be non-negative");
    let digits = format!("{value:x}");
    let mut out = String::from(C_HEX_PREFIX);
    for (index, digit) in digits.chars().enumerate() {
        if index > 0 && (digits.len() - index).is_multiple_of(HEX_GROUP_DIGITS) {
            out.push('_');
        }
        out.push(digit);
    }
    out
}

// The generated ABI mirror (`runtime_abi.rs`, included by src/codegen/abi.rs):
// one Rust constant per reserved heap tag, the tag family as a named array the
// tag-collision guards iterate, and the header layout as compile-time facts.
fn runtime_abi(manifest_dir: &str) -> String {
    let path = format!("{manifest_dir}/{RUNTIME_DIR}/{ABI_HEADER}");
    let header = fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {path}: {e}"));
    let tags = heap_tags(&header);
    assert!(
        tags.len() >= ABI_MIN_HEAP_TAGS,
        "parsed only {} PRISM_*_TAG defines from {ABI_HEADER}; the tag parser regressed",
        tags.len()
    );
    let rc_word = required_c_define(&header, ABI_RC_WORD);
    let tag_word = required_c_define(&header, ABI_TAG_WORD);
    let arity_word = required_c_define(&header, ABI_ARITY_WORD);
    let header_words = required_c_define(&header, ABI_HEADER_WORDS);
    let word_bytes = required_c_define(&header, ABI_WORD_BYTES);
    let static_cell = required_c_define(&header, ABI_STATIC_CELL);
    let tag_offset = tag_word * word_bytes;
    let header_bytes = header_words * word_bytes;
    assert_eq!(
        rc_word, EXPECTED_RC_WORD_INDEX,
        "runtime rc word moved off offset 0"
    );
    assert_eq!(
        (arity_word + ARITY_TRAILING_WORDS) * word_bytes,
        header_bytes,
        "arity is no longer the last header word"
    );
    let mut out = String::from(
        "// Generated from runtime/prism_internal.h by build.rs: the runtime's\n\
         // reserved heap-tag family and cell layout, mirrored so Rust codegen\n\
         // cannot drift from the C. Do not edit; edit the header.\n",
    );
    for (name, value) in &tags {
        let short = name.strip_prefix("PRISM_").unwrap();
        writeln!(out, "pub(crate) const {short}: i64 = {};", rust_hex(*value)).unwrap();
    }
    writeln!(
        out,
        "/// Every heap tag the runtime claims for its own cell kinds. Codegen\n\
         /// must never mint a closure or constructor tag equal to one of these,\n\
         /// or refcounting misclassifies the cell and walks (or skips) the wrong\n\
         /// payload. Paired with the C define name so the layout test can check\n\
         /// each entry against the embedded header text independently.\n\
         pub(crate) const RESERVED_HEAP_TAGS: [(&str, i64); {}] = [",
        tags.len()
    )
    .unwrap();
    for (name, _) in &tags {
        writeln!(
            out,
            "    (\"{name}\", {}),",
            name.strip_prefix("PRISM_").unwrap()
        )
        .unwrap();
    }
    out.push_str("];\n");
    writeln!(out, "pub(crate) const WORD_BYTES: i64 = {word_bytes};").unwrap();
    writeln!(out, "pub(crate) const TAG_OFF: i64 = {tag_offset};").unwrap();
    writeln!(out, "pub(crate) const HDR_BYTES: i64 = {header_bytes};").unwrap();
    writeln!(
        out,
        "/// The rc-word marker for a cell baked into the executable image:\n\
         /// codegen writes it into a static cell's refcount word so the runtime\n\
         /// treats the cell as count-inert and never writes the (read-only) word.\n\
         pub(crate) const STATIC_CELL: i64 = {};",
        rust_hex(static_cell)
    )
    .unwrap();
    out
}

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

fn macos_deployment_target(cc: &str) -> Option<String> {
    if let Ok(target) = env::var("MACOSX_DEPLOYMENT_TARGET") {
        if !target.trim().is_empty() {
            return Some(target);
        }
    }
    let output = Command::new(cc)
        .args(["-###", "-x", "c", "/dev/null", "-o", "/tmp/prism-cc-probe"])
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&output.stderr);
    let marker = "apple-macosx";
    let start = text.find(marker)? + marker.len();
    let version: String = text[start..]
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '.')
        .collect();
    let mut parts = version.split('.').filter(|s| !s.is_empty());
    let major = parts.next()?;
    let minor = parts.next().unwrap_or("0");
    Some(format!("{major}.{minor}"))
}

fn main() {
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
    // FP contraction off). The vendored libm archive is built once here at -O2 and
    // embedded for every native link, so program `--backend-opt` never recompiles
    // libm differently from the interpreter.
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
    println!("cargo:rerun-if-env-changed=MACOSX_DEPLOYMENT_TARGET");
    let macos_min = if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        macos_deployment_target(&cc)
    } else {
        None
    };
    println!(
        "cargo:rustc-env=PRISM_MACOSX_DEPLOYMENT_TARGET={}",
        macos_min.as_deref().unwrap_or("")
    );

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

    // The ABI mirror for src/codegen/abi.rs, regenerated whenever the header
    // changes (its rerun-if-changed is declared with the manifest above).
    fs::write(
        Path::new(&out_dir).join("runtime_abi.rs"),
        runtime_abi(&manifest_dir),
    )
    .unwrap();

    // The C runtime is linked only into natively compiled programs; a wasm build
    // runs the interpreter alone, so skip it (and the bogus -lm).
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("wasm32") {
        let mut rt = cc::Build::new();
        rt.compiler(&cc).include(RUNTIME_DIR).opt_level(2);
        // FP contraction stays off everywhere the runtime is compiled, matching
        // the native link step: an FMA fused on one platform and not another
        // breaks byte-for-byte float parity with the interpreter.
        rt.flag("-ffp-contract=off");
        // The lint gates' warning set, applied here too so a warning is not
        // reachable only through a hook. Each flag is probed first: a compiler
        // that rejects one keeps building, it just reports less. Not fatal here
        // (no -Werror); making it fatal is the gates' job, on a pinned compiler.
        for flag in warning_flags(&manifest_dir) {
            rt.flag_if_supported(&flag);
        }
        println!("cargo:rerun-if-changed={RUNTIME_DIR}/{RUNTIME_WARNINGS}");
        if let Some(min) = &macos_min {
            rt.flag(format!("-mmacosx-version-min={min}"));
        }
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
        // Force-include the prism_v_* rename header at the top of every libm unit
        // (before its own <math.h>), so even the units that pull <math.h> directly
        // instead of libm.h get their public entry points namespaced. This is what
        // stops the vendored transcendentals from being shadowed by the platform
        // libm at link time (the source of a ULP of cross-binary float drift).
        let rename_hdr = format!("{manifest_dir}/{RUNTIME_DIR}/prism_libm_rename.h");
        libm_rt
            .compiler(&cc)
            .opt_level(2)
            .warnings(false)
            .flag("-ffp-contract=off")
            .flag("-include")
            .flag(&rename_hdr);
        if let Some(min) = &macos_min {
            libm_rt.flag(format!("-mmacosx-version-min={min}"));
        }
        for (name, is_header) in &libm {
            if !is_header {
                libm_rt.file(format!("{RUNTIME_DIR}/{name}"));
            }
        }
        libm_rt.compile("prism_libm");
        // Rerun (rebuild the archive, which reruns the include_bytes! embed) when any
        // vendored unit, a libm header, or the rename header changes. cc-rs tracks the
        // .c it compiles, but not the headers they include, and these are no longer in
        // the manifest loop that emitted rerun-if-changed, so declare them here.
        for (name, _) in &libm {
            println!("cargo:rerun-if-changed={RUNTIME_DIR}/{name}");
        }
        println!("cargo:rerun-if-changed={RUNTIME_DIR}/prism_libm_rename.h");
        // Export the exact archive path so codegen::rt can embed it (include_bytes!)
        // and the native backend links THESE bytes, never a recompile. One libm,
        // shared by the interpreter and every native binary.
        println!("cargo:rustc-env=PRISM_LIBM_ARCHIVE={out_dir}/libprism_libm.a");
        // No `-lm`: the vendored libm above provides every math symbol. Linking
        // the system libm is the actual source of cross-platform float
        // divergence, so it is deliberately absent from every native link.
    }
}
