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
pub mod codegen;
pub mod core;
pub mod debug;
pub mod deprecated;
pub mod docs;
pub mod driver;
pub mod error;
pub mod eval;
pub mod fixpoint;
pub mod flags;
pub mod fmt;
pub mod fresh;
pub mod kw;
pub mod lex;
pub mod names;
pub mod parse;
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
pub(crate) mod scc;
pub mod stdlib;
pub mod store;
pub mod sym;
pub mod syntax;
pub(crate) mod tc;
pub mod types;
#[cfg(feature = "wasm")]
pub mod wasm;

/// Inclusive byte bounds of the printable ASCII range.
///
/// Bytes outside `LO..=HI` are non-printable and get escaped by the string
/// emitters (`codegen::emit`, `wasm`); shared here so both agree on the range.
pub const ASCII_PRINTABLE_LO: u8 = 0x20;
pub const ASCII_PRINTABLE_HI: u8 = 0x7E;

pub use core::{CorePass, OptLevel, PassSpec, EFFECT_TIERS};
pub use docs::{
    accept, preprocess_book, project_expect_files, project_pages, stdlib_expect_files,
    stdlib_pages, DocPage, ExpectFile, ExpectReport, Generated, ModuleSource, Report,
};
#[cfg(feature = "native")]
pub use driver::{attest_on, build, build_at, build_on, emit_ir};
#[cfg(feature = "mlir")]
pub use driver::{build_mlir, build_mlir_at, build_mlir_on};
pub use driver::{
    check, check_at, check_on, commit_to_store, core_ir, core_ir_full, core_of, debug_on, diff_on,
    dump, dump_at, dump_on, effect_strategy_full, effect_strategy_on, effect_warnings_full,
    example_program, interpret, interpret_at, interpret_io_at, interpret_io_on, namespace_root,
    off_platform_builtins, query_on, rc_balanced, record_on, replay_on, report, report_at,
    report_on, resume_on, shape_digests_of, source_modules, stdlib_hash, store_def_inputs,
    suspend_line_cuts, suspend_on, valid_backend_opt, with_custom_prelude, with_prelude, Config,
    Scheduler, StdlibHash, SuspendResult, BACKEND_OPT_LEVELS,
};
pub use error::{Error, LexError, ParseError, TypeError};
pub use flags::{DynFlags, EffectTier};
pub use fmt::{format, format_check, format_wire_accept};
pub use resolve::{default_roots, project_roots, Root};
pub use sym::Sym;
pub use types::show_effects;
