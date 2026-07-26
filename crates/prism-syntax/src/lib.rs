//! The Prism surface-syntax world.
//!
//! Keyword and sigil tables, the diagnostic substrate, the lexer and layout
//! pass, the LALRPOP grammar and parser entry points, the surface AST, and
//! the source formatter. This crate knows the shape of Prism source and
//! nothing of its semantics.

pub mod ast;
pub mod coeffect;
pub mod error;
pub mod fmt;
pub mod kind;
pub mod kw;
pub mod lex;
pub mod names;
pub mod parse;
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
