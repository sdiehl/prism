//! The Prism compiler as a library.
//!
//! # Supported surface
//!
//! Most of the compiler is exposed so that tools can build ON it, not just call
//! it. The essential guarantee is that **merged Core is the semantic
//! authority**, so the surface is organized around consuming and producing Core:
//!
//! - [`core`]: the call-by-push-value Core IR and its content-addressed
//!   identity. A custom front end lowers to it; a custom back end reads it.
//! - [`codegen`]: the [`codegen::Isa`] trait and [`codegen::emit_with_isa`]:
//!   implement `Isa` to reuse Prism's semantic Core-to-instruction lowering for
//!   an out-of-tree backend.
//! - The front-end phases a custom front end can reuse to reach Core:
//!   [`lex`], [`parse`], [`resolve`], [`syntax`] (desugaring), [`hir`],
//!   [`types`], the versioned syntax exports (`dump syntax-tokens` /
//!   `surface-syntax` / `syntax-diagnostics`), and the resolved/checked
//!   inspection dumps (`dump tc-input` / `resolved-syntax` / `tc-facts` /
//!   `elab-input`).
//! - [`driver`]: the compile entry points (`check`, `dump`, `build`,
//!   `interpret`, the durable-run and patch surfaces), most re-exported at the
//!   crate root below.
//! - [`eval`]: the interpreter, the differential oracle every backend matches.
//! - Supporting durable and diagnostic types: [`error`], [`flags`], [`sym`],
//!   [`names`], [`resolve::Root`], [`store`], [`lineage`], [`stdlib`].
//!
//! Modules kept private (`pub(crate)`) are implementation detail with no
//! stability commitment: keyword tables (`kw`), the formatter internals
//! (surfaced only as [`fn@format`]), the wired-in stdlib symbol table (`wired`),
//! the verification passes (`verify`, driven through the CLI), and the doc
//! generator (`docs`, surfaced only through its re-exports).

#![allow(clippy::many_single_char_names)]
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
#[cfg(feature = "native")]
pub use prism_native as codegen;
// The CLI command bodies. Native-only: it drives clap parsing, project builds, the
// package manager, and the interpreter, none of which exist in a wasm build.
#[cfg(feature = "native")]
pub mod cli;
pub mod core;
pub mod debug;
// Internal: the doc generator is driven by the CLI and the mdbook preprocessor;
// its intended surface is the crate-root re-exports below, not the module.
pub(crate) mod docs;
pub mod driver;
pub use prism_syntax::error;
pub mod eval;
pub use prism_core::flags;
// Internal: the intended surface is the crate-root re-exports (`format`,
// `format_check`, `format_wire_accept`), not the module's helpers.
pub use prism_syntax::fmt;
pub mod hir;
// The code index: the whole-codebase artifact a program viewer reads. A
// projection of compiler facts (namespace layers, the Core dependency graph,
// checked effect rows) rather than a new analysis.
pub mod index;
// Internal: keyword tables are a lexer/parser detail, never a library commitment.
pub(crate) use prism_syntax::kw;
pub use prism_syntax::lex;
pub mod lineage;
pub use prism_syntax::names;
pub use prism_syntax::parse;
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
pub mod scheme_canon;
pub use scheme_canon::{canonical_scheme, SCHEME_CANON_CONTRACT};
pub mod stable;
pub use stable::lock as stable_lock;
pub mod stdlib;
pub mod store;
pub use prism_common::sym;
pub mod syntax;
pub(crate) mod tc;
// `prism test` discovery and the harness runner. Native-only: it drives the CLI,
// the project loader, and the interpreter, none of which exist in a wasm build.
#[cfg(feature = "native")]
pub mod testing;
#[path = "types.rs"]
pub mod types;

// Internal: `prism verify` is driven through the CLI; the module exposes no
// public items, so it is not a library surface.
pub(crate) mod verify;
#[cfg(feature = "wasm")]
pub mod wasm;
// Internal: the compiler's wired-in stdlib symbol table, not a library surface.
pub(crate) mod wired;

// The printable-ASCII byte bounds live in `prism_common`; re-exported at the
// crate root so `crate::ASCII_PRINTABLE_*` keeps resolving for the wasm and
// native string emitters, which share the range.
pub use prism_common::{ASCII_PRINTABLE_HI, ASCII_PRINTABLE_LO};

pub use core::{CorePass, EffectStrategy, OptLevel, PassSpec, EFFECT_TIERS};
pub use docs::{
    accept, preprocess_book, project_expect_files, project_pages, stdlib_expect_files,
    stdlib_modules, stdlib_pages, DocPage, ExpectFile, ExpectReport, Generated, ModuleSource,
    Report, TypeSpan, TypeSpans, TYPESPANS_FORMAT,
};
pub use driver::{
    apply_semantic_patch, check, check_allow_holes_on_in, check_at, check_modules_on, check_on,
    check_on_in, check_validated_on_in, check_with_seed, commit_to_store, core_ir, core_ir_full,
    core_of, debug_on, diff_on, dump, dump_at, dump_on, durable_run_on, effect_strategy_full,
    effect_strategy_on, effect_warnings_full, example_program, fetch_semantic_patch,
    impact_semantic_patch, interpret, interpret_at, interpret_deferred_holes, interpret_io_at,
    interpret_io_on, interpret_io_on_with_args, interpret_io_on_with_args_deferred_holes,
    interpret_on, module_graph, module_interface, namespace_identity, namespace_layers,
    namespace_root, observe_run_on, observe_run_on_deferred_holes, off_platform_builtins,
    public_surface, query_on, rc_balanced, record_on, record_on_with_args, record_run_on,
    replay_on, replay_run_on, report, report_at, report_on, resume_observed_on, resume_on,
    shape_digests_of, source_diff_on, source_modules, stdlib_hash, step_ruler_on, store_def_inputs,
    suspend_at_cut_on, suspend_line_cuts, suspend_on, type_tokens, verify_semantic_patch_behavior,
    with_custom_prelude, with_prelude, BackendOpt, BehaviorCase, BehaviorCaseResult,
    BehaviorCorpus, BehaviorDivergence, BehaviorReceipt, CheckedModule, CompilerSession, Config,
    CutReport, CutTarget, DeltaReport, DurableRun, EvidenceTier, FetchReport, ImpactReport,
    InterfaceDelta, ModuleCheckReport, ModuleGraph, ModuleGraphNode, ModuleInterface,
    ModuleInterfaceEntry, ModuleInvalidation, ModuleInvalidationCause, NamespaceIdentity,
    NamespaceLayers, PatchRefusal, PatchRefusalBody, PatchRefusalSubject, PublicDef, RecordedRun,
    RehydratedModuleInterface, Scheduler, SessionStats, StagedPatch, StdlibHash, StepRuler,
    StepRulerRow, SuspendAtCut, SuspendCut, SuspendResult, TimingSink, MODULE_GRAPH_FORMAT,
    MODULE_INTERFACE_FORMAT, PATCH_BEHAVIOR_CORPUS_FORMAT, PATCH_BEHAVIOR_FORMAT,
    PATCH_DELTA_FORMAT, PATCH_FETCH_FORMAT, PATCH_IMPACT_FORMAT, PATCH_REFUSAL_FORMAT,
    PATCH_STAGE_FORMAT, STEP_RULER_FORMAT,
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
pub use lineage::provenance::{Observation, ObservationTrace, OBSERVATION_TRACE_FORMAT};
pub use prism_syntax::fmt::{format, format_check};
pub use resolve::{
    default_roots, project_roots, project_roots_with_packages_and_std, project_roots_with_std,
    resolve_modules_seeing, Occurrence, Root,
};
pub use stable::wire_fmt::format_wire_accept;
pub use sym::Sym;
pub use types::{show_effects, TypecheckSeed};
