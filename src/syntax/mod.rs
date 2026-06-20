pub mod ast;
pub mod desugar;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(
        clippy::all,
        clippy::pedantic,
        clippy::nursery,
        unreachable_pub,
        missing_debug_implementations
    )]
    grammar,
    "/syntax/grammar.rs"
);

pub use grammar::{ExprParser, ProgramParser, TypeSigParser};
