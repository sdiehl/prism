#![allow(clippy::many_single_char_names)]
#![allow(clippy::multiple_crate_versions)]
// `redundant_pub_crate` (nursery) and the rustc `unreachable_pub` lint pull in
// opposite directions for a `pub(crate)` item in a `pub(crate)` module, the
// honest visibility for an item shared between sibling crate-internal modules
// (the `tc` <-> `types` split). Keep the precise `pub(crate)` and silence the
// nursery half of the conflict.
#![allow(clippy::redundant_pub_crate)]

// Link in the mimalloc symbols so the C runtime shim resolves mi_*; no Rust code
// calls them directly (see the runtime/ C modules).
#[cfg(feature = "mimalloc")]
extern crate libmimalloc_sys as _;

#[cfg(feature = "native")]
// Public intentionally: external compiler hackers can implement `codegen::Isa`
// and reuse Prism's semantic Core-to-instruction lowering for experimental
// out-of-tree backends.
pub mod codegen;
// The CLI command bodies. Native-only: it drives clap parsing, project builds, the
// package manager, and the interpreter, none of which exist in a wasm build.
#[cfg(feature = "native")]
pub mod cli;
pub mod core;
pub mod debug;
pub mod docs;
pub mod driver;
pub mod error;
pub mod eval;
pub mod flags;
pub mod fmt;
pub mod hir;
pub mod kw;
pub mod lex;
pub mod lineage;
pub mod names;
pub mod parse;
pub mod patch;
// The package manager is native-only: it drives `crate::project` builds and the
// disk transport, neither of which exists in a wasm build, and every use site
// (the driver's transport/trust imports, the CLI) is already `native`-gated.
#[cfg(feature = "native")]
pub mod pkg;
#[cfg(feature = "native")]
pub mod project;
#[cfg(feature = "native")]
pub mod repl;
pub mod resolve;
pub mod stable_lock;
pub mod stdlib;
pub mod store;
pub mod sym;
pub mod syntax;
pub(crate) mod tc;
// `prism test` discovery and the harness runner. Native-only: it drives the CLI,
// the project loader, and the interpreter, none of which exist in a wasm build.
#[cfg(feature = "native")]
pub mod testing;
pub mod types;
pub(crate) mod util;
pub mod verify;
#[cfg(feature = "wasm")]
pub mod wasm;
pub mod wired;

/// Inclusive byte bounds of the printable ASCII range.
///
/// Bytes outside `LO..=HI` are non-printable and get escaped by the string
/// emitters (`codegen::emit`, `wasm`); shared here so both agree on the range.
pub const ASCII_PRINTABLE_LO: u8 = 0x20;
pub const ASCII_PRINTABLE_HI: u8 = 0x7E;

pub use core::{CorePass, EffectStrategy, OptLevel, PassSpec, EFFECT_TIERS};
pub use docs::{
    accept, preprocess_book, project_expect_files, project_pages, stdlib_expect_files,
    stdlib_pages, DocPage, ExpectFile, ExpectReport, Generated, ModuleSource, Report, TypeSpan,
    TypeSpans, TYPESPANS_FORMAT,
};
pub use driver::{
    apply_semantic_patch, check, check_at, check_modules_on, check_on, check_on_in,
    check_validated_on_in, check_with_seed, commit_to_store, core_ir, core_ir_full, core_of,
    debug_on, diff_on, dump, dump_at, dump_on, durable_run_on, effect_strategy_full,
    effect_strategy_on, effect_warnings_full, example_program, fetch_semantic_patch,
    impact_semantic_patch, interpret, interpret_at, interpret_deferred_holes, interpret_io_at,
    interpret_io_on, interpret_io_on_with_args, interpret_io_on_with_args_deferred_holes,
    interpret_on, module_graph, module_interface, namespace_identity, namespace_root,
    observe_run_on, observe_run_on_deferred_holes, off_platform_builtins, public_surface, query_on,
    rc_balanced, record_on, record_on_with_args, record_run_on, replay_on, replay_run_on, report,
    report_at, report_on, resume_observed_on, resume_on, shape_digests_of, source_diff_on,
    source_modules, stdlib_hash, step_ruler_on, store_def_inputs, suspend_at_cut_on,
    suspend_line_cuts, suspend_on, verify_semantic_patch_behavior, with_custom_prelude,
    with_prelude, BackendOpt, BehaviorCase, BehaviorCaseResult, BehaviorCorpus, BehaviorDivergence,
    BehaviorReceipt, CheckedModule, CompilerSession, Config, CutReport, CutTarget, DeltaReport,
    DurableRun, EvidenceTier, FetchReport, ImpactReport, InterfaceDelta, ModuleCheckReport,
    ModuleGraph, ModuleGraphNode, ModuleInterface, ModuleInterfaceEntry, ModuleInvalidation,
    ModuleInvalidationCause, NamespaceIdentity, PatchRefusal, PatchRefusalBody,
    PatchRefusalSubject, PublicDef, RecordedRun, RehydratedModuleInterface, Scheduler,
    SessionStats, StagedPatch, StdlibHash, StepRuler, StepRulerRow, SuspendAtCut, SuspendCut,
    SuspendResult, TimingSink, MODULE_GRAPH_FORMAT, MODULE_INTERFACE_FORMAT,
    PATCH_BEHAVIOR_CORPUS_FORMAT, PATCH_BEHAVIOR_FORMAT, PATCH_DELTA_FORMAT, PATCH_FETCH_FORMAT,
    PATCH_IMPACT_FORMAT, PATCH_REFUSAL_FORMAT, PATCH_STAGE_FORMAT, STEP_RULER_FORMAT,
};
#[cfg(feature = "native")]
pub use driver::{
    attest_on, build, build_at, build_on, build_on_report, emit_ir,
    verify_backend_recomposition_on, NativeBuildReport, NativeCacheStatus,
};
#[cfg(feature = "mlir")]
pub use driver::{build_mlir, build_mlir_at, build_mlir_on};
pub use error::{
    typed_hole_fault, Error, ErrorCode, ErrorPhase, HoleBinding, HoleCandidate, HoleReport,
    LexError, ParseError, TypeError, TYPED_HOLE,
};
pub use flags::{DynFlags, EffectTier, WarnDupes};
pub use fmt::{format, format_check, format_wire_accept};
pub use lineage::provenance::{Observation, ObservationTrace, OBSERVATION_TRACE_FORMAT};
pub use resolve::{
    default_roots, project_roots, project_roots_with_packages_and_std, project_roots_with_std, Root,
};
pub use sym::Sym;
pub use types::{show_effects, TypecheckSeed};
