fn main() {
    println!("cargo:rerun-if-changed=src/syntax/grammar.lalrpop");
    lalrpop::process_root().unwrap();
    // The target triple for the banner; TARGET is set by cargo for build scripts.
    println!(
        "cargo:rustc-env=PRISM_TARGET={}",
        std::env::var("TARGET").unwrap_or_default()
    );
    // The C runtime is linked only into natively compiled programs; a wasm
    // build runs the interpreter alone, so skip it (and the bogus -lm).
    if std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("wasm32") {
        let mut rt = cc::Build::new();
        rt.file("runtime/prism_rt.c").opt_level(2);
        // Opt-in mimalloc: the `libmimalloc-sys` crate (pulled in by the feature)
        // provides the `mi_*` symbols; the runtime shim declares and routes to
        // them, so we only flip the define here, no in-tree allocator source.
        if std::env::var_os("CARGO_FEATURE_MIMALLOC").is_some() {
            rt.define("PRISM_MIMALLOC", None);
        }
        rt.compile("prism_rt");
        println!("cargo:rustc-link-lib=m");
        println!("cargo:rerun-if-changed=runtime/prism_rt.c");
    }
}
