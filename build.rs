use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

// Homebrew's LLVM is built with the Z3 solver and zstd compression enabled, so
// `llvm-config --system-libs` hands the linker `-lz3 -lzstd` and the resulting
// binary carries a hard LC_LOAD_DYLIB on both, under the build machine's
// Homebrew prefix. Every user without that exact prefix (no brew, or Intel's
// /usr/local instead of Apple Silicon's /opt/homebrew) then gets a dyld abort
// before main, on `prism --version` as much as on a compile. Nothing in prism
// calls Z3 (the `verify` path spawns a solver as a subprocess and speaks
// SMT-LIB over a pipe; it never links one), and the zstd use is LLVM's own
// compression helper, so both dependencies can be discharged at link time:
// force-load the static zstd archive so those symbols resolve locally, then let
// the linker drop every dylib no symbol is bound to. Z3 goes because it was
// always dead weight, zstd because the archive now satisfies it, and the macOS
// artifact stops depending on the runner's Homebrew tree.
const ZSTD_ARCHIVE_CANDIDATES: &[&str] = &[
    "/opt/homebrew/opt/zstd/lib/libzstd.a",
    "/usr/local/opt/zstd/lib/libzstd.a",
];
const ZSTD_ARCHIVE: &str = "libzstd.a";

/// The static zstd archive to bind against, taken from the well-known Homebrew
/// prefixes and otherwise from whatever prefix `brew` reports.
fn zstd_archive() -> Option<PathBuf> {
    if let Some(hit) = ZSTD_ARCHIVE_CANDIDATES
        .iter()
        .map(Path::new)
        .find(|p| p.exists())
    {
        return Some(hit.to_path_buf());
    }
    let out = Command::new("brew")
        .args(["--prefix", "zstd"])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let prefix = String::from_utf8(out.stdout).ok()?;
    let path = Path::new(prefix.trim()).join("lib").join(ZSTD_ARCHIVE);
    path.exists().then_some(path)
}

fn main() {
    // The target triple for the banner and artifact identity; TARGET is set by
    // cargo for build scripts. The C-toolchain identity lives with the native
    // backend's build script (`crates/prism-native/build.rs`).
    println!(
        "cargo:rustc-env=PRISM_TARGET={}",
        env::var("TARGET").unwrap_or_default()
    );

    // See ZSTD_ARCHIVE_CANDIDATES above. ld64 only; ELF linkers already default
    // to --as-needed and the Linux packages declare their LLVM dependency.
    if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        if let Some(archive) = zstd_archive() {
            println!(
                "cargo:rustc-link-arg-bins=-Wl,-force_load,{}",
                archive.display()
            );
        }
        println!("cargo:rustc-link-arg-bins=-Wl,-dead_strip_dylibs");
    }
}
