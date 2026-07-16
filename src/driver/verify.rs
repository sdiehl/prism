//! Correctness checks and attestation: the driver's judgments about a program
//! beyond "it compiles".
//!
//! Two kinds of check live here. The usage/allocation/replayability gates
//! (`fip_check`, `replayable_check`, `reconcile_effects`) run on every
//! check/build/interpret through the shared front end, rejecting a program whose
//! annotations its compiled form cannot honor. Attestation (`attest_on`) is the
//! diverse-double-compilation gate: it runs a program through two independent
//! backends and confirms their output is byte-identical, named by the shared
//! content hash and cross-checked against any signed package index.

use std::collections::BTreeSet;

use crate::coeffect::CoeffectFact;
use crate::core::fbip::borrow_sigs;
use crate::core::{
    check_fip, check_fip_linear, fip_annots, insert_rc, replayable_annots, reuse, Core,
};
use crate::error::{Error, TypeError};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::Checked;

#[cfg(feature = "native")]
use std::fmt::Write as _;
#[cfg(feature = "native")]
use std::fs;
#[cfg(feature = "native")]
use std::path::Path;
#[cfg(feature = "mlir")]
use std::process::Command;

#[cfg(feature = "native")]
use crate::pkg::transport::{DiskTransport, Transport};
#[cfg(feature = "native")]
use crate::pkg::trust::{parse_index, verify_signature, Verdict};
#[cfg(feature = "native")]
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::store::cert::{emit, parity_cert, BACKEND_LLVM, CLAIM_PARITY_PASSED_NAME};
#[cfg(feature = "native")]
use crate::store::disk::{self as store};

#[cfg(feature = "mlir")]
use super::build_mlir_on;
#[cfg(feature = "native")]
use super::execution::interp_transcript;
#[cfg(feature = "native")]
use super::native::run_native;
#[cfg(feature = "native")]
use super::{build_on, namespace_identity, Config};

// The signed-index cross-check line for a root, or empty when no store, index, or
// matching pointer is present. Read-only against the package index.
#[cfg(feature = "native")]
fn attest_index_line(root: &str, cfg: &Config) -> String {
    let store_root = store::resolve_store_path(cfg.flags.store_path.as_deref());
    let Ok(dst) = DiskTransport::open(&store_root) else {
        return String::new();
    };
    let Ok(Some(artifact)) = dst.index_artifact() else {
        return String::new();
    };
    let rows = parse_index(&artifact.body);
    let Some(row) = rows.iter().find(|r| r.root == root) else {
        return String::new();
    };
    let sig = match verify_signature(&artifact, &cfg.flags) {
        Verdict::Valid { identity: Some(id) } => format!("valid ({id})"),
        Verdict::Valid { identity: None } => "valid".to_string(),
        Verdict::Unsigned => "unsigned (dev mode)".to_string(),
        Verdict::Invalid(m) => format!("INVALID: {m}"),
        Verdict::Unavailable(m) => format!("unverifiable: {m}"),
    };
    format!("  index: {}@{} signature {sig}\n", row.name, row.tag)
}

// The second, independent backend for attestation: MLIR native when the feature
// and toolchain are present, otherwise the interpreter as the second oracle with
// the limitation named.
// The `Result` matters under the `mlir` feature (`build_mlir_on` and the
// native run can fail); the fallback path is infallible, so clippy sees an
// unnecessary wrap only in the default build.
#[cfg(feature = "native")]
#[allow(clippy::unnecessary_wraps)]
fn attest_second(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    tmp: &Path,
    stem: &str,
    interp: &[u8],
) -> Result<(&'static str, Vec<u8>, Option<String>), Error> {
    #[cfg(feature = "mlir")]
    {
        let has_tool = Command::new("mlir-translate")
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success());
        if has_tool {
            let bin = tmp.join(format!("{stem}_mlir"));
            build_mlir_on(src, roots, &bin, cfg)?;
            let out = run_native(&bin)?;
            let _ = fs::remove_file(&bin);
            return Ok(("MLIR", out, None));
        }
    }
    let _ = (src, roots, cfg, tmp, stem);
    Ok((
        "interpreter",
        interp.to_vec(),
        Some(
            "MLIR backend unavailable (build with --features mlir and install mlir-translate); \
             the interpreter is the independent second oracle"
                .to_string(),
        ),
    ))
}

/// Diverse double compilation: compile and run `src` through two independent
/// backends and confirm their output is byte-identical, attested by the shared
/// content hash (the whole-program namespace root).
///
/// This is Thompson's "Trusting Trust" defeated by construction and Wheeler's
/// diverse double compilation, made a standing check rather than a heroic
/// one-off: the same source, compiled two independent ways, must observably agree
/// to the byte, and the content hash names the identity both compiled. When the
/// MLIR toolchain is present the two backends are LLVM and MLIR; otherwise the
/// interpreter is the independent second oracle and the limitation is printed. If
/// a signed-index pointer exists for the root, its name, tag, and signature
/// verdict are cross-checked and reported.
///
/// # Errors
/// A front-end error, a codegen or link failure, or a divergence between the
/// backends (the attestation's whole point is that this never happens).
#[cfg(feature = "native")]
pub fn attest_on(src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    let identity = namespace_identity(src, roots)?;
    let root = identity.root;
    let interp = interp_transcript(src, roots, cfg)?;

    let tmp = std::env::temp_dir();
    let stem = format!("prism_attest_{}", std::process::id());
    let llvm_bin = tmp.join(format!("{stem}_llvm"));
    build_on(src, roots, &llvm_bin, cfg)?;
    let llvm_out = run_native(&llvm_bin)?;
    let _ = fs::remove_file(&llvm_bin);

    let (second_name, second_out, limitation) =
        attest_second(src, roots, cfg, &tmp, &stem, &interp)?;

    // The two backends must agree byte for byte; the interpreter oracle backstops
    // both, so a three-way agreement is what the green line asserts.
    if llvm_out != second_out || llvm_out != interp {
        return Err(Error::CodegenVerification(format!(
            "attest: backends diverged for root {root}; LLVM and {second_name} are not \
             byte-identical (this is the invariant the attestation exists to catch)"
        )));
    }

    let mut out = format!("attested: {root} identical across LLVM, {second_name}\n");
    if let Some(l) = limitation {
        let _ = writeln!(out, "  note: {l}");
    }
    out.push_str(&attest_index_line(&root, cfg));
    out.push_str(&attest_cert_line(&root, second_name, cfg));
    Ok(out)
}

// Emit (or find) the parity certificate for a successfully attested root, and
// report which. Never required for correctness: a store that cannot be opened or written
// simply yields no line, so a certificate failure never fails the attestation the
// byte-identity check already established.
#[cfg(feature = "native")]
fn attest_cert_line(root: &str, second_name: &str, cfg: &Config) -> String {
    let store_root = store::resolve_store_path(cfg.flags.store_path.as_deref());
    let Ok(store) = store::Store::open_or_create(&store_root) else {
        return String::new();
    };
    let cert = parity_cert(root, (BACKEND_LLVM, second_name));
    match emit(&store, &cert) {
        Ok(store::Written::New) => {
            format!(
                "  cert: emitted {CLAIM_PARITY_PASSED_NAME}@{}\n",
                cert.scheme
            )
        }
        Ok(store::Written::Hit) => {
            format!(
                "  cert: reused existing {CLAIM_PARITY_PASSED_NAME}@{}\n",
                cert.scheme
            )
        }
        Err(_) => String::new(),
    }
}

// Cross-check the two effect engines as a real assertion (not a debug_assert):
// the op-keyed call-graph fixpoint used by effect lowering (`latent_ops`)
// against each function's inferred row (the effect labels of its checked type,
// `DeclInfo::effects`). The agreed direction is containment: every effect a
// function can still perform must appear in its inferred row. A violation means
// the checker under-reported an effect a later pass will still try to lower, an
// internal-consistency bug surfaced here rather than as a miscompile.
// Synthesized ops that are not type-level effects are skipped rather than
// flagged.
pub(super) fn reconcile_effects(checked: &Checked, core: &Core) -> Result<(), Error> {
    let latent = crate::core::latent_ops(core);
    let empty = BTreeSet::new();
    // Validate against each function's inferred row (the labels of its checked
    // type), not the set-pass `effects` seed: the seed cannot count the scoped
    // masking that lets a `mask`ed effect tunnel past its handler, so only the
    // inferred row reflects what the function actually leaves unhandled.
    let inferred_rows: std::collections::BTreeMap<&str, &crate::types::Effects> = checked
        .decls
        .iter()
        .map(|d| (d.name.as_str(), &d.effects))
        .collect();
    for f in &core.fns {
        let Some(ops) = latent.get(&f.name) else {
            continue;
        };
        // An instance method is absent from `checked.decls` (those are the
        // top-level `fn`s); its effect discipline is enforced against the class
        // signature at `check_instance`, where an effect-polymorphic method may
        // legitimately perform the effects flowing through its row variable. It
        // has no standalone inferred row to reconcile against, so validating it
        // here against an empty row would spuriously flag that permitted effect.
        if crate::names::is_instance_method(f.name.as_str()) {
            continue;
        }
        let inferred = inferred_rows
            .get(f.name.as_str())
            .copied()
            .unwrap_or(&empty);
        let extra: Vec<&str> = ops
            .iter()
            .filter_map(|op| checked.eff_ops.get(op.as_str()))
            .map(|info| info.effect_name)
            .filter(|e| !inferred.contains(e))
            .collect::<BTreeSet<_>>()
            .iter()
            .map(|s| s.as_str())
            .collect();
        if !extra.is_empty() {
            let row: Vec<&str> = inferred.iter().map(|s| s.as_str()).collect();
            return Err(Error::InternalInvariant(format!(
                "effect reconciliation: `{}` can still perform {extra:?} after lowering, \
                 but its inferred row is {row:?}",
                f.name
            )));
        }
    }
    Ok(())
}

// Check the FP^2 discipline of every `fip`/`fbip`-annotated function. Linearity
// is a property of the SOURCE term, so it is checked on the raw elaborated core
// (`check_fip_linear`), using the typechecker's param/field types to exempt
// scalars (a `dup` on an immediate is a runtime no-op). Zero-allocation, the
// callee closure, and bounded stack are properties of the COMPILED term, so they
// are checked on the reuse-lowered core (`check_fip`). Runs on every
// check/build/interpret (shared `frontend`); pure annotated functions are
// unaffected by effect lowering, so this un-effect-lowered core matches
// `dump fbip`.
pub(super) fn fip_check(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &Core,
) -> Result<(), Error> {
    let annots = fip_annots(program);
    if annots.is_empty() {
        return Ok(());
    }
    let to_err = |msg: String| {
        // Point the diagnostic at the offending annotated function: its name
        // appears backtick-quoted in the message, so the first annotated decl
        // whose name occurs there owns the span.
        let owner = program
            .fns
            .iter()
            .filter(|d| annots.contains_key(&Sym::from(&d.name)))
            .find(|d| msg.contains(&format!("`{}`", d.name)));
        let span = owner.map_or_else(marginalia::Span::default, |d| d.span);
        // An `@ noalloc` function checks with `fbip` semantics, so the shared
        // checker phrases its message with `fbip`. Normalize the user-facing
        // family here: `fip`/`fbip` are usage checks, while `@ noalloc` is an
        // allocation certificate.
        let msg = match owner {
            Some(d) if d.no_alloc && d.fip == Fip::No => {
                let wa = format!("{} {}", crate::kw::AT, CoeffectFact::Noalloc);
                let m = msg.replace("`fbip`", &format!("`{wa}`"));
                allocation_certificate_message(&wa, Some(&d.name), &m)
            }
            Some(d) if d.fip == Fip::Fip => usage_check_message("fip", &d.name, &msg),
            Some(d) if d.fip == Fip::Fbip => usage_check_message("fbip", &d.name, &msg),
            _ => msg,
        };
        Error::Type(TypeError::TypeFailure { span, msg })
    };
    let sigs = borrow_sigs(program);
    let users: std::collections::BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    check_fip_linear(core, &annots, &checked.decls, &checked.ctors).map_err(to_err)?;
    check_fip(&reuse(&insert_rc(core, &sigs)), &annots, &sigs, &users).map_err(to_err)
}

fn allocation_certificate_message(kind: &str, name: Option<&str>, msg: &str) -> String {
    let rest = name.map_or_else(
        || {
            msg.strip_prefix(&format!("the `{kind}` block "))
                .unwrap_or_else(|| strip_sentence_prefix(msg))
        },
        |name| strip_marked_prefix(msg, name, kind),
    );
    name.map_or_else(
        || format!("allocation certificate `{kind}` failed for block: {rest}"),
        |name| format!("allocation certificate `{kind}` failed for function `{name}`: {rest}"),
    )
}

fn usage_check_message(kind: &str, name: &str, msg: &str) -> String {
    let rest = strip_marked_prefix(msg, name, kind);
    format!("usage check `{kind}` failed for function `{name}`: {rest}")
}

fn strip_marked_prefix<'a>(msg: &'a str, name: &str, kind: &str) -> &'a str {
    msg.strip_prefix(&format!("function `{name}` is marked `{kind}` but "))
        .or_else(|| msg.strip_prefix(&format!("a `{kind}` function ")))
        .unwrap_or_else(|| strip_sentence_prefix(msg))
}

fn strip_sentence_prefix(msg: &str) -> &str {
    msg.strip_prefix("function ")
        .or_else(|| msg.strip_prefix("a "))
        .unwrap_or(msg)
}

// Check every `replayable`-annotated function. The certificate is on the inferred
// principal row: it must stay within the recordable capabilities (`Console`,
// `FileSystem`, `Random`, `Env`, `Output`) plus the deterministic builtin effects
// (`Exn`, `Fail`). `Output` is admitted because replay/durable suppress it during
// the replayed prefix, so re-running it is sound. A row containing `IO` (un-logged
// nondeterminism: the system clock, srand) or any user-defined effect cannot be
// reproduced from a trace, so it is rejected with a caret at the function naming
// the offending effect(s).
pub(super) fn replayable_check(
    program: &Program<CorePhase>,
    checked: &Checked,
) -> Result<(), Error> {
    let annots = replayable_annots(program);
    if annots.is_empty() {
        return Ok(());
    }
    let allowed: std::collections::BTreeSet<Sym> = crate::names::INPUT_CAPABILITY_EFFECTS
        .iter()
        .copied()
        .chain([
            crate::names::OUTPUT_EFFECT,
            crate::names::EXN_EFFECT,
            crate::names::FAIL_EFFECT,
        ])
        .map(Sym::from)
        .collect();
    let inferred: std::collections::BTreeMap<&str, &crate::types::ty::Effects> = checked
        .decls
        .iter()
        .map(|i| (i.name.as_str(), &i.effects))
        .collect();
    for d in &program.fns {
        if !annots.contains(&Sym::from(&d.name)) {
            continue;
        }
        let Some(row) = inferred.get(d.name.as_str()).copied() else {
            continue;
        };
        let offending: Vec<&str> = row
            .iter()
            .filter(|e| !allowed.contains(*e))
            .map(|e| e.as_str())
            .collect();
        if !offending.is_empty() {
            let msg = format!(
                "function `{}` is marked `replayable` but performs non-replayable {} `{}`; \
                 a replayable function may use only Console, FileSystem, Random, Env, Clock, Output, Exn, Fail",
                d.name,
                if offending.len() == 1 {
                    "effect"
                } else {
                    "effects"
                },
                offending.join("`, `")
            );
            return Err(Error::Type(TypeError::TypeFailure { span: d.span, msg }));
        }
    }
    Ok(())
}
