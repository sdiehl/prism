mod code;
mod diag;
mod lex;
mod parse;
mod phase;
mod render;
mod source;
pub mod suggest;

pub use code::{ErrorCode, ErrorPhase};
pub use diag::{Diag, ErrKind, Frame, TypeError};
pub use lex::LexError;
pub use parse::ParseError;
pub use phase::Error;
pub use render::render_warning;
#[cfg(feature = "wasm")]
pub(crate) use source::line_col;
pub use source::SourceMap;
