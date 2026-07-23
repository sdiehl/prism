//! Env-knob audit: every `PRISM_*` environment knob has exactly one documented
//! home, and nothing reads one anywhere else.
//!
//! The knobs fall into three families, and this test is the guard that keeps the
//! boundary between them honest. A knob read from a new, unclassified site fails
//! here, forcing the author to say which family it belongs to (and, for a compile
//! knob, to route it through `DynFlags` rather than sampling the environment deep
//! in a pass).
//!
//! 1. **Compile-time behavior knobs** live in `src/flags.rs` and are read exactly
//!    once, in `DynFlags::from_env`, then threaded down. This is the determinism
//!    contract's requirement: a compile's behavior is a function of its inputs, so
//!    no pass may sample the process environment on its own. Any `PRISM_*` read in
//!    `flags.rs` is accepted here; a read from any other compiler module is not.
//!
//! 2. **Runtime knobs** are observed by the *running program* (the native C
//!    runtime), and the interpreter mirrors them so both tiers agree. They gate
//!    telemetry and self-checks, never compilation, so they deliberately do not go
//!    through `DynFlags`.
//!
//! 3. **Toolchain and test knobs** select the C compiler Prism links with, or
//!    steer a test's golden-file blessing / external solver. The toolchain seam is
//!    centralized in `codegen::rt`; the test knobs live only in test modules.
//!
//! `env!("PRISM_...")` reads (baked at build time by `build.rs`) are a fourth,
//! separate thing and are intentionally not scanned: they are compile-time
//! constants, not runtime environment reads.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

// The single home for compile-time behavior knobs. Any `PRISM_*` read here is a
// `DynFlags` field and is accepted without a per-var entry below.
const DYNFLAGS_HOME: &str = "src/flags.rs";

// Every `PRISM_*` knob read outside `flags.rs`, mapped to the file(s) allowed to
// read it. Keep this table in sync with the three families above; a new read from
// an unlisted (var, file) pair fails the audit, and a listed pair that no longer
// appears in the source fails it too, so the catalogue can neither grow silently
// nor rot.
const ALLOWED: &[(&str, &[&str])] = &[
    // Family 2: runtime knobs (native runtime + interpreter mirror).
    (
        "PRISM_PROBES",
        &["runtime/prism_io.c", "src/eval/builtin.rs"],
    ),
    ("PRISM_CHECK_LEAKS", &["runtime/prism_mem.c"]),
    ("PRISM_ALLOC_STATS", &["runtime/prism_mem.c"]),
    ("PRISM_REUSE_STATS", &["runtime/prism_mem.c"]),
    ("PRISM_EFFOP_STATS", &["runtime/prism_mem.c"]),
    ("PRISM_DRIVE_STATS", &["runtime/prism_mem.c"]),
    // Family 3a: the C-toolchain seam, centralized in one module.
    ("PRISM_CC", &["src/codegen/rt.rs"]),
    ("PRISM_CC_FLAGS", &["src/codegen/rt.rs"]),
    // Family 3b: test-only knobs (golden-file blessing, external solvers).
    ("PRISM_BLESS_REPLAY", &["src/debug/durable/tests.rs"]),
    ("PRISM_BLESS_SMT", &["src/verify/tests.rs"]),
    ("PRISM_BLESS_WORLD_FIXTURE", &["src/lineage/tests.rs"]),
    ("PRISM_Z3", &["src/verify/tests.rs"]),
    ("PRISM_CVC5", &["src/verify/tests.rs"]),
];

// An environment *read* is one of these call forms with a string-literal argument.
// A bare `"PRISM_..."` in a diagnostic message or a doc comment is not a read and
// is ignored; a read via a dynamic (non-literal) name is out of scope by design
// (the `getenv` builtin reads an arbitrary program-supplied name).
const READ_MARKERS: &[&str] = &["env::var(\"", "env::var_os(\"", "getenv(\""];

/// Every `(var, relative-file)` env read of a `PRISM_*` knob found by scanning the
/// literal call sites under `src/` (`.rs`) and `runtime/` (`.c`/`.h`).
fn scan_reads() -> BTreeSet<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut found = BTreeSet::new();
    for (dir, exts) in [("src", &["rs"][..]), ("runtime", &["c", "h"][..])] {
        collect(&root.join(dir), &root, exts, &mut found);
    }
    found
}

fn collect(dir: &Path, root: &Path, exts: &[&str], out: &mut BTreeSet<(String, String)>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, root, exts, out);
        } else if path
            .extension()
            .is_some_and(|e| exts.iter().any(|x| e == *x))
        {
            let rel = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            let text = fs::read_to_string(&path).unwrap_or_default();
            for line in text.lines() {
                for var in reads_on_line(line) {
                    out.insert((var, rel.clone()));
                }
            }
        }
    }
}

/// The `PRISM_*` var names read on one line via any [`READ_MARKERS`] call form.
fn reads_on_line(line: &str) -> Vec<String> {
    let mut vars = Vec::new();
    for marker in READ_MARKERS {
        let mut rest = line;
        while let Some(i) = rest.find(marker) {
            let after = &rest[i + marker.len()..];
            if let Some(end) = after.find('"') {
                let name = &after[..end];
                if name.starts_with("PRISM_") {
                    vars.push(name.to_string());
                }
            }
            rest = &rest[i + marker.len()..];
        }
    }
    vars
}

#[test]
fn every_prism_env_read_has_a_documented_home() {
    let allowed: BTreeMap<&str, BTreeSet<&str>> = ALLOWED
        .iter()
        .map(|(v, fs)| (*v, fs.iter().copied().collect()))
        .collect();
    let reads = scan_reads();

    // No read lives anywhere but its documented home.
    let mut stray = Vec::new();
    for (var, file) in &reads {
        if file == DYNFLAGS_HOME {
            continue; // a DynFlags knob, read at the one sanctioned site
        }
        let ok = allowed
            .get(var.as_str())
            .is_some_and(|files| files.contains(file.as_str()));
        if !ok {
            stray.push(format!("  {var} read at {file}"));
        }
    }
    assert!(
        stray.is_empty(),
        "PRISM_* env knob read from an undocumented site.\n{}\n\nClassify it: a compile knob \
         belongs in DynFlags (src/flags.rs), a runtime or toolchain/test knob in the ALLOWED \
         table in tests/env_knobs.rs (with its family).",
        stray.join("\n")
    );

    // No allowlisted read has silently disappeared (renamed knob, moved reader).
    let mut missing = Vec::new();
    for (var, files) in &allowed {
        for file in files {
            if !reads.contains(&((*var).to_string(), (*file).to_string())) {
                missing.push(format!("  {var} expected at {file}"));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "an allowlisted PRISM_* read is gone; update the ALLOWED table in tests/env_knobs.rs.\n{}",
        missing.join("\n")
    );
}
