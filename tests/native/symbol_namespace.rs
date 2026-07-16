// A user function may be named anything the source allows, including the name of
// a C runtime intrinsic. The native backend mints Core functions into `prismfn_`,
// its own lambdas, apply dispatchers, and TRMC helpers into
// `prismlam_`/`prismap_`/`prismtrmc_`, and the C runtime owns `prism_`; the five
// disagree on the byte at index 5, so no user name can spell a symbol another
// definer already emitted.
//
// Before that split every Core function was `prism_{name}`, and the collision was
// reachable three ways, each a different symptom:
//
//   - `bump`/`alloc`/`box` emitted a second definition of a runtime function, and
//     the link died with `duplicate symbol '_prism_bump'`.
//   - `rc_inc` shadowed a runtime symbol the emitter itself calls, so the call
//     resolved to the user's function and codegen ICEd on the arity/return
//     mismatch, before the linker ever ran.
//   - `apply_1` shadowed codegen's own arity-1 dispatcher, and the LLVM verifier
//     rejected the module: the dispatcher takes a closure plus one argument, the
//     user's function takes one.
//
// Only a function that SURVIVES INLINING emits a symbol at all, which is why this
// stayed latent: a one-line `fn bump(n) = n + 1` is inlined away and links fine.
// Each case is therefore recursive AND applied through an unknown closure, and
// the IR is checked for a real definition of both the user's mangled name and a
// codegen dispatcher before the binary is built. Those two guards are what keep
// the gate from passing vacuously if inlining later swallows the case.
//
// Note that `prismlam_{tag}` needs no case here: tags are content hashes of the
// owning function, never small integers, so no plausible source identifier spells
// one. The prefix split makes it impossible rather than merely improbable, but
// there is no program to regress against.

use std::path::Path;
use std::process::Command;

use prism::codegen::native_symbol;

use crate::support::{cleanup_bin, require_cc, temp_bin};

// `prism_{name}` is defined by `runtime/prism_mem.c` for the first four (`rc_inc`
// is additionally one the emitter calls), and by codegen itself for `apply_1`.
// `prismfn_bump` is the complementary prefix-forgery case: a legal source binder
// that begins with the Core-function prefix must become
// `prismfn_prismfn_bump`, not escape or replace the namespace.
const ADVERSARIAL_NAMES: &[&str] = &["bump", "alloc", "box", "rc_inc", "apply_1", "prismfn_bump"];

// The dispatcher every case must force into existence for the `apply_1` case to
// be testing anything.
const DISPATCHER: &str = "prismap_1";

// Recursion keeps the definition alive through the inliner; routing it through a
// closure that `twice` applies at an unknown arity forces codegen to emit its own
// dispatcher alongside. `twice(g, 19)` is `g(g(19))`, and `g` adds one, so every
// case prints 21.
fn program(name: &str) -> String {
    prism::with_prelude(&format!(
        "fn {name}(n : Int) : Int =\n  if n <= 0 then 0 else 1 + {name}(n - 1)\n\n\
         fn twice(f : Int -> Int, x : Int) : Int = f(f(x))\n\n\
         fn main() =\n  let g = \\(k : Int) -> {name}(k) + 1\n  println(twice(g, 19))\n"
    ))
}

#[test]
fn user_functions_may_shadow_runtime_symbol_names() {
    require_cc();
    let mut fails = Vec::new();
    for name in ADVERSARIAL_NAMES {
        if let Err(e) = check(name) {
            fails.push(e);
        }
    }
    assert!(
        fails.is_empty(),
        "user function names collide with the native symbol namespace:\n{}",
        fails.join("\n")
    );
}

fn defines(ir: &str, symbol: &str) -> bool {
    ir.lines()
        .any(|line| line.starts_with("define") && line.contains(&format!("@{symbol}(")))
}

fn check(name: &str) -> Result<(), String> {
    let full = program(name);
    let symbol = native_symbol(name);
    let roots = prism::default_roots(Path::new("."));
    let mut cfg = prism::Config::from_env();
    // This gate must inspect and link code emitted by the compiler under test,
    // never satisfy itself from a previously linked artifact.
    cfg.flags.compiler_cache = false;

    let ir = prism::dump_on("llvm", &full, &roots, &cfg)
        .map_err(|e| format!("{name}: llvm dump failed: {e}"))?;
    if !defines(&ir, &symbol) {
        return Err(format!(
            "{name}: IR defines no `@{symbol}`; it was inlined away, so this case proves nothing"
        ));
    }
    if !defines(&ir, DISPATCHER) {
        return Err(format!(
            "{name}: IR defines no `@{DISPATCHER}`; the closure was devirtualized, so this case \
             no longer covers the codegen namespace"
        ));
    }

    let bin = temp_bin("symns", name);
    prism::build_on(&full, &roots, &bin, &cfg).map_err(|e| format!("{name}: build failed: {e}"))?;
    let out = Command::new(&bin)
        .output()
        .map_err(|e| format!("{name}: spawn failed: {e}"))?;
    cleanup_bin(&bin);

    let want = prism::interpret(&full).unwrap().term;
    let got = String::from_utf8_lossy(&out.stdout);
    if got != want {
        return Err(format!(
            "{name}: native disagrees with interpreter\n  native: {got:?}\n  interp: {want:?}"
        ));
    }
    Ok(())
}
