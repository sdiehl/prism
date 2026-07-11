use thiserror::Error;

use super::code;
use super::{ErrorCode, ErrorPhase, LexError, ParseError, TypeError};

/// Error crossing a compiler API boundary.
///
/// Each semantic variant owns one stable code. Message text is payload, never the
/// discriminator used by callers or renderers.
#[derive(Debug, Error)]
pub enum Error {
    #[error("{0}")]
    Lex(#[from] LexError),
    #[error("{0}")]
    Parse(#[from] ParseError),
    #[error("{0}")]
    Type(#[from] TypeError),
    #[error("codegen: {0}")]
    CodegenBackend(String),
    #[error("documentation: {0}")]
    CodegenDocs(String),
    #[error("formatting: {0}")]
    CodegenFormat(String),
    #[error("dump: {0}")]
    CodegenDump(String),
    #[error("verification: {0}")]
    CodegenVerification(String),
    #[error("{0}")]
    ResolveModule(String),
    #[error("{0}")]
    ResolveProject(String),
    #[error("{0}")]
    ResolvePackage(String),
    #[error("{0}")]
    ResolveLineage(String),
    #[error("{0}")]
    ResolveCommand(String),
    #[error("{0}")]
    Io(#[from] std::io::Error),
    #[error("runtime: {0}")]
    RuntimeEvaluation(String),
    #[error("runtime replay: {0}")]
    RuntimeReplay(String),
    #[error("debugger: {0}")]
    RuntimeDebugger(String),
    #[error("internal compiler error: {0}, please report this")]
    InternalInvariant(String),
}

impl Error {
    /// Stable code for every error crossing the compiler API boundary.
    #[must_use]
    pub const fn code(&self) -> ErrorCode {
        match self {
            Self::Lex(error) => ErrorCode::new(ErrorPhase::Lex, error.code()),
            Self::Parse(error) => ErrorCode::new(ErrorPhase::Parse, error.code()),
            Self::Type(error) => error.error_code(),
            Self::CodegenBackend(_) => ErrorCode::new(ErrorPhase::Codegen, code::CODEGEN_BACKEND),
            Self::CodegenDocs(_) => ErrorCode::new(ErrorPhase::Codegen, code::CODEGEN_DOCS),
            Self::CodegenFormat(_) => ErrorCode::new(ErrorPhase::Codegen, code::CODEGEN_FORMAT),
            Self::CodegenDump(_) => ErrorCode::new(ErrorPhase::Codegen, code::CODEGEN_DUMP),
            Self::CodegenVerification(_) => {
                ErrorCode::new(ErrorPhase::Codegen, code::CODEGEN_VERIFICATION)
            }
            Self::ResolveModule(_) => ErrorCode::new(ErrorPhase::Resolve, code::RESOLVE_MODULE),
            Self::ResolveProject(_) => ErrorCode::new(ErrorPhase::Resolve, code::RESOLVE_PROJECT),
            Self::ResolvePackage(_) => ErrorCode::new(ErrorPhase::Resolve, code::RESOLVE_PACKAGE),
            Self::ResolveLineage(_) => ErrorCode::new(ErrorPhase::Resolve, code::RESOLVE_LINEAGE),
            Self::ResolveCommand(_) => ErrorCode::new(ErrorPhase::Resolve, code::RESOLVE_COMMAND),
            Self::Io(_) => ErrorCode::new(ErrorPhase::Io, code::IO),
            Self::RuntimeEvaluation(_) => {
                ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_EVALUATION)
            }
            Self::RuntimeReplay(_) => ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_REPLAY),
            Self::RuntimeDebugger(_) => ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_DEBUGGER),
            Self::InternalInvariant(_) => ErrorCode::new(ErrorPhase::Internal, code::INTERNAL),
        }
    }
}
