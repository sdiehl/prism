//! The Prism surface-syntax world.
//!
//! Keyword and sigil tables, the diagnostic substrate, the lexer and layout
//! pass, the LALRPOP grammar and parser entry points, the surface AST, and
//! the source formatter. This crate knows the shape of Prism source and
//! nothing of its semantics.

// Layout and pretty-printing code names spans, docs, and indices with the short
// letters the layout algebra uses; spelling them out obscures the algebra.
#![allow(clippy::many_single_char_names)]
// `redundant_pub_crate` (nursery) and the rustc `unreachable_pub` lint pull in
// opposite directions for a `pub(crate)` item in a private module, the honest
// visibility for an item shared between sibling crate-internal modules (the
// diagnostic-code table, the raw-string delimiters the lexer and formatter
// share). Keep the precise `pub(crate)` and silence the nursery half.
#![allow(clippy::redundant_pub_crate)]

pub mod ast;
pub mod coeffect;
pub mod error;
pub mod fmt;
pub mod kind;
pub mod kw;
pub mod lex;
pub mod names;
pub mod parse;
pub mod reflect;
pub mod sugar;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(
        clippy::all,
        clippy::pedantic,
        clippy::nursery,
        unreachable_pub,
        missing_debug_implementations
    )]
    grammar
);

pub use grammar::{ExprParser, ProgramParser, TypeSigParser};
