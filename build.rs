use std::env;

fn main() {
    // The target triple for the banner and artifact identity; TARGET is set by
    // cargo for build scripts. The C-toolchain identity lives with the native
    // backend's build script (`crates/prism-native/build.rs`).
    println!(
        "cargo:rustc-env=PRISM_TARGET={}",
        env::var("TARGET").unwrap_or_default()
    );
}
