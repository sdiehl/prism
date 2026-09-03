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

use std::collections::{BTreeMap, BTreeSet};

use crate::core::fbip::borrow_sigs;
use crate::core::{
    bounded_stack_annots, callable_requirements, check_alloc, check_bounded_stack,
    check_callable_flow, check_linear, fip_annots, insert_rc, latent_ops, linear_annots,
    newtype_ctors, replayable_annots, reuse, ClaimError, ClaimErrorKind, ClaimOrigin, Core,
    TypedCore, TypedElaborated,
};
use crate::error::{ErrKind, Error, TypeError};
use crate::kw::AT;
use crate::names::{
    is_instance_method, EXN_EFFECT, FAIL_EFFECT, INPUT_CAPABILITY_EFFECTS, OUTPUT_EFFECT,
};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::coeffect::CoeffectFact;
use crate::types::{Checked, Effects};

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
use crate::pkg::trust::{parse_index, private_temp_dir, verify_signature, Verdict};
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
    let store_root = store::resolve_store_path(cfg.flags().store_path.as_deref());
    let Ok(dst) = DiskTransport::open(&store_root) else {
        return String::new();
    };
    let Ok(Some(artifact)) = dst.index_artifact() else {
        return String::new();
    };
    let rows = parse_index(&artifact.body);
    let Some(row) = rows.iter().find(|r| r.root.as_str() == root) else {
        return String::new();
    };
    let sig = match verify_signature(&artifact, cfg.flags()) {
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

    // Stage the compiled binaries in a freshly created private directory rather
    // than at a predictable shared-temp path: a fixed `temp_dir()/name` an
    // attacker can guess is a symlink-follow / name-prediction race on a binary
    // about to be executed.
    let tmp = private_temp_dir("attest")?;
    let stem = format!("prism_attest_{}", std::process::id());
    let llvm_bin = tmp.join(format!("{stem}_llvm"));
    build_on(src, roots, &llvm_bin, cfg)?;
    let llvm_out = run_native(&llvm_bin)?;
    let _ = fs::remove_file(&llvm_bin);

    let (second_name, second_out, limitation) =
        attest_second(src, roots, cfg, &tmp, &stem, &interp)?;
    // The staged binaries were removed as they ran, so this clears the now-empty
    // private directory itself.
    let _ = fs::remove_dir_all(&tmp);

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
    let store_root = store::resolve_store_path(cfg.flags().store_path.as_deref());
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
    let latent = latent_ops(core);
    let empty = BTreeSet::new();
    // Validate against each function's inferred row (the labels of its checked
    // type), not the set-pass `effects` seed: the seed cannot count the scoped
    // masking that lets a `mask`ed effect tunnel past its handler, so only the
    // inferred row reflects what the function actually leaves unhandled.
    let inferred_rows: BTreeMap<&str, &Effects> = checked
        .defs
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
        if is_instance_method(f.name.as_str()) {
            continue;
        }
        let inferred = inferred_rows
            .get(f.name.as_str())
            .copied()
            .unwrap_or(&empty);
        let extra: Vec<&str> = ops
            .iter()
            .filter_map(|op| checked.defs.eff_ops.get(op.as_str()))
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

// Check every usage claim: the row facts (`@ noalloc`, `@ linear`,
// `@ bounded_stack`) and the `fip`/`fbip` keywords, which are those same facts
// bundled (`fbip` the allocation fact alone, `fip` all three), so each drive
// covers keyword-annotated and row-claimed functions together. Linearity is a
// property of the SOURCE term, so it is checked on the raw elaborated core
// (`check_linear`), using the typechecker's param/field types to exempt
// scalars (a `dup` on an immediate is a runtime no-op). The allocation budget
// and bounded stack are properties of the COMPILED term, so they are checked
// on the reuse-lowered core (`check_alloc` / `check_bounded_stack`). Runs on
// every check/build/interpret (shared `frontend`); pure annotated functions
// are unaffected by effect lowering, so this un-effect-lowered core matches
// `dump fbip`.
pub(super) fn fip_check(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &Core,
    typed: &TypedCore<TypedElaborated>,
) -> Result<(), Error> {
    let annots = fip_annots(program);
    let stack_claims = bounded_stack_annots(program);
    let linear_claims = linear_annots(program);
    let callable = callable_requirements(program);
    if annots.is_empty()
        && stack_claims.is_empty()
        && linear_claims.is_empty()
        && callable.is_empty()
    {
        return Ok(());
    }
    let to_err = |e: ClaimError| {
        // The rejection names its owner directly, so the span lookup and the
        // family framing key on data, never on message text.
        let owner = program.fns.iter().find(|d| d.name == e.fname.as_str());
        let span = owner.map_or_else(marginalia::Span::default, |d| d.span);
        let name = e.fname.to_string();
        // The claim the diagnostic names. A standalone row fact passes through
        // verbatim (`@ linear`, `@ bounded_stack`); the keyword vocabulary is
        // re-rendered from the declaration, so a graded `fip(2)` names its
        // budget, and a bare `@ noalloc` (which runs the shared drive under
        // `fbip` semantics) keeps its allocation-certificate spelling.
        let noalloc_claim = owner.is_some_and(|d| d.no_alloc && d.fip == Fip::No);
        let claim = match e.origin {
            ClaimOrigin::RowClaim => e.spelled.clone(),
            ClaimOrigin::Keyword if noalloc_claim => format!("{AT} {}", CoeffectFact::Noalloc),
            ClaimOrigin::Keyword => owner
                .and_then(|d| d.fip.render())
                .unwrap_or_else(|| e.spelled.clone()),
        };
        let detail = e.kind.detail();
        // One catalogue code per failing rule; `@ noalloc` alone takes the
        // allocation-certificate framing, every other spelling is a usage check.
        let kind = match e.kind.as_ref() {
            ClaimErrorKind::AllocBudgetExceeded { .. } if noalloc_claim => {
                ErrKind::AllocationCertificateFailed {
                    claim,
                    name,
                    detail,
                }
            }
            ClaimErrorKind::AllocBudgetExceeded { .. } => ErrKind::ClaimAllocBudgetExceeded {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::BorrowedParam => ErrKind::ClaimBorrowedParam {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::DuplicatesValue => ErrKind::ClaimDuplicatesValue {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::LinearityNotClosed { .. } => ErrKind::ClaimLinearityNotClosed {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::NonTailRecursion { .. } => ErrKind::ClaimNonTailRecursion {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::TrmcShapesMixed { .. } => ErrKind::ClaimTrmcShapesMixed {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::TrmcWithMutualCall { .. } => ErrKind::ClaimTrmcWithMutualCall {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::SccMemberUncertified { .. } => ErrKind::ClaimSccMemberUncertified {
                claim,
                name,
                detail,
            },
            ClaimErrorKind::StackNotClosed { .. } => ErrKind::ClaimStackNotClosed {
                claim,
                name,
                detail,
            },
            // The callable-certificate rejections carry their own framing: the
            // demand sits on a parameter's function type, not on the walked
            // function's own claim, so `claim` is unused here by design.
            ClaimErrorKind::CallableUncertified { .. } => {
                ErrKind::CallableCertificateMissing { name, detail }
            }
            ClaimErrorKind::CallableOpaque { .. } => {
                ErrKind::CallableCertificateOpaque { name, detail }
            }
        };
        let err = kind.at(span);
        match e.kind.note() {
            Some(note) => Error::Type(err.note(note)),
            None => Error::Type(err),
        }
    };
    let sigs = borrow_sigs(program);
    let users: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    let newtypes = newtype_ctors(program);
    // The linearity drive shares the source-term core: it runs pre-RC, so the
    // dup/drop the RC pass inserts to realize linear consumption are never
    // counted against a claiming function.
    check_linear(
        core,
        &linear_claims,
        &annots,
        &sigs,
        &checked.defs.decls,
        &checked.defs.ctors,
        &users,
    )
    .map_err(to_err)?;
    let lowered = reuse(&insert_rc(core, &sigs));
    check_alloc(
        &lowered,
        &annots,
        &users,
        &newtypes,
        &callable.certified_params(),
    )
    .map_err(to_err)?;
    // The bounded-stack drive shares the compiled-term core: its recursion
    // rules must agree byte-for-byte with what codegen loops.
    check_bounded_stack(&lowered, &stack_claims, &annots, &users).map_err(to_err)?;
    // The callable-certificate drive runs on the pre-optimizer typed core: a
    // value flowing into a `@ noalloc` function-typed parameter must prove its
    // whole call tree allocation-free, tier- and optimizer-invariantly.
    check_callable_flow(typed.functions(), &callable, &annots).map_err(to_err)
}

// Check every `replayable`-annotated function. The certificate is on the inferred
// principal row: it must stay within the recordable capabilities (`Console`,
// `FileSystem`, `Random`, `Env`, `Clock`, `Output`) plus the deterministic builtin
// effects (`Exn`, `Fail`). `Output` is admitted because replay/durable suppress it
// during the replayed prefix, so re-running it is sound. A row containing `IO` (un-logged
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
    let allowed: BTreeSet<Sym> = INPUT_CAPABILITY_EFFECTS
        .iter()
        .copied()
        .chain([OUTPUT_EFFECT, EXN_EFFECT, FAIL_EFFECT])
        .map(Sym::from)
        .collect();
    let inferred: BTreeMap<&str, &Effects> = checked
        .defs
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
