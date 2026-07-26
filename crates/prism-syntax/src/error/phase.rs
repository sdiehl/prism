use std::fmt;

use thiserror::Error;

use super::code;
use super::{ErrorCode, ErrorPhase, LexError, ParseError, TypeError};

/// A failure while translating checked declarations into the environment used
/// by typed-Core construction and verification.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TypedCoreEnvironmentFailure {
    #[error("invalid signature for `{item}`: {detail}")]
    InvalidSignature { item: String, detail: String },
}

/// A typed-Core witness that the elaborator could not construct.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TypedCoreConstructionFailure {
    #[error("`{function}` has no declared Core signature")]
    MissingGlobalSignature { function: String },
    #[error("`{function}` has {actual} parameter(s), but its Core signature declares {expected}")]
    ParameterArity {
        function: String,
        actual: usize,
        expected: usize,
    },
    #[error("cannot lower declaration `{declaration}`: {detail}")]
    InvalidDeclaration { declaration: String, detail: String },
    #[error("invalid witness in `{function}` at {path}: {detail}")]
    InvalidWitness {
        function: String,
        path: String,
        detail: String,
    },
}

/// One independently rejected typed-Core judgment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedCoreViolation {
    pub function: String,
    pub path: String,
    pub detail: String,
}

impl fmt::Display for TypedCoreViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}: {}", self.function, self.path, self.detail)
    }
}

/// The complete, structured result of independent typed-Core verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedCoreVerificationFailure {
    pub violations: Vec<TypedCoreViolation>,
}

impl fmt::Display for TypedCoreVerificationFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} violation(s)", self.violations.len())?;
        if let Some(first) = self.violations.first() {
            write!(f, ": {first}")?;
            if self.violations.len() > 1 {
                write!(f, "; and {} more", self.violations.len() - 1)?;
            }
        }
        Ok(())
    }
}

impl std::error::Error for TypedCoreVerificationFailure {}

/// Verified typed Core failed to erase back to its compatibility input.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
#[error("erasure changed the compatibility Core tree")]
pub struct TypedCoreErasureFailure;

/// A typed-Core dictionary specialization that could not preserve its scheme.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TypedCoreSpecializationFailure {
    #[error("erased typed specialization changed the compatibility Core tree")]
    CompatibilityDrift,
    #[error(
        "`{function}` declares {dictionary_arity} dictionary parameter(s), but its Core signature has {parameter_arity} parameter(s)"
    )]
    DictionaryArity {
        function: String,
        dictionary_arity: usize,
        parameter_arity: usize,
    },
    #[error(
        "dictionary parameter {dictionary_index} of `{function}` is incompatible with builder `{builder}`"
    )]
    IncompatibleDictionary {
        function: String,
        dictionary_index: usize,
        builder: String,
    },
    #[error(
        "call to `{function}` carries {actual} scheme argument(s), but specialization requires {expected}"
    )]
    SourceInstantiationArity {
        function: String,
        actual: usize,
        expected: usize,
    },
    #[error(
        "dictionary builder `{builder}` carries {actual} scheme argument(s), but specialization requires {expected}"
    )]
    BuilderInstantiationArity {
        builder: String,
        actual: usize,
        expected: usize,
    },
}

/// Typed-Core simplification did not reach a fixed point.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TypedCoreSimplifyFailure {
    #[error("typed Core simplification did not converge after {ticks} rewrite(s)")]
    RunawayRewrite { ticks: u64 },
}

/// Typed effect lowering could not produce a verified `EffectLowered` program.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TypedCoreEffectLoweringFailure {
    /// The built `EffectLowered` tree failed the independent verifier; the
    /// phase marker is never forged around an unverified tree.
    #[error("typed effect lowering produced an unverifiable program: {first}")]
    Verification { first: String, count: usize },
    /// An internal table or invariant broke mid-lowering.
    #[error("typed effect lowering internal invariant: {msg}")]
    Internal { msg: String },
}

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
    /// A canonical JSON semantic-patch refusal. The CLI prints this payload
    /// directly instead of wrapping it in a human diagnostic.
    #[error("{0}")]
    SemanticPatch(String),
    #[error("{0}")]
    Io(#[from] std::io::Error),
    #[error("runtime: {0}")]
    RuntimeEvaluation(String),
    #[error("runtime replay: {0}")]
    RuntimeReplay(String),
    #[error("debugger: {0}")]
    RuntimeDebugger(String),
    #[error("typed Core environment construction failed: {0}")]
    TypedCoreEnvironment(#[from] TypedCoreEnvironmentFailure),
    #[error("typed Core construction failed: {0}")]
    TypedCoreConstruction(#[from] TypedCoreConstructionFailure),
    #[error("typed Core verification failed: {0}")]
    TypedCoreVerification(#[from] TypedCoreVerificationFailure),
    #[error("typed Core erasure neutrality failed: {0}")]
    TypedCoreErasure(#[from] TypedCoreErasureFailure),
    #[error("typed Core specialization failed: {0}")]
    TypedCoreSpecialization(#[from] TypedCoreSpecializationFailure),
    #[error("typed Core simplification failed: {0}")]
    TypedCoreSimplify(#[from] TypedCoreSimplifyFailure),
    #[error("typed effect lowering failed: {0}")]
    TypedCoreEffectLowering(#[from] TypedCoreEffectLoweringFailure),
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
            Self::SemanticPatch(_) => ErrorCode::new(ErrorPhase::Resolve, code::PATCH_REFUSAL),
            Self::Io(_) => ErrorCode::new(ErrorPhase::Io, code::IO),
            Self::RuntimeEvaluation(_) => {
                ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_EVALUATION)
            }
            Self::RuntimeReplay(_) => ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_REPLAY),
            Self::RuntimeDebugger(_) => ErrorCode::new(ErrorPhase::Runtime, code::RUNTIME_DEBUGGER),
            Self::TypedCoreEnvironment(_) => code::TYPED_CORE_ENVIRONMENT,
            Self::TypedCoreConstruction(_) => code::TYPED_CORE_CONSTRUCTION,
            Self::TypedCoreVerification(_) => code::TYPED_CORE_VERIFICATION,
            Self::TypedCoreErasure(_) => code::TYPED_CORE_ERASURE,
            Self::TypedCoreSpecialization(_) => code::TYPED_CORE_SPECIALIZATION,
            Self::TypedCoreSimplify(_) => code::TYPED_CORE_SIMPLIFY,
            Self::TypedCoreEffectLowering(_) => code::TYPED_CORE_EFFECT_LOWERING,
            Self::InternalInvariant(_) => ErrorCode::new(ErrorPhase::Internal, code::INTERNAL),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::{
        TYPED_CORE_CONSTRUCTION, TYPED_CORE_ENVIRONMENT, TYPED_CORE_ERASURE, TYPED_CORE_SIMPLIFY,
        TYPED_CORE_SPECIALIZATION, TYPED_CORE_VERIFICATION,
    };

    #[test]
    fn typed_core_failures_use_their_canonical_codes() {
        let environment = Error::from(TypedCoreEnvironmentFailure::InvalidSignature {
            item: "intrinsic".into(),
            detail: "bad signature".into(),
        });
        let construction = Error::from(TypedCoreConstructionFailure::InvalidWitness {
            function: "main".into(),
            path: "body".into(),
            detail: "bad witness".into(),
        });
        let verification = Error::from(TypedCoreVerificationFailure {
            violations: vec![TypedCoreViolation {
                function: "main".into(),
                path: "body".into(),
                detail: "failed judgment".into(),
            }],
        });
        let erasure = Error::from(TypedCoreErasureFailure);
        let specialization = Error::from(TypedCoreSpecializationFailure::CompatibilityDrift);
        let simplify = Error::from(TypedCoreSimplifyFailure::RunawayRewrite { ticks: 5_000_001 });

        assert_eq!(environment.code(), TYPED_CORE_ENVIRONMENT);
        assert_eq!(construction.code(), TYPED_CORE_CONSTRUCTION);
        assert_eq!(verification.code(), TYPED_CORE_VERIFICATION);
        assert_eq!(erasure.code(), TYPED_CORE_ERASURE);
        assert_eq!(specialization.code(), TYPED_CORE_SPECIALIZATION);
        assert_eq!(simplify.code(), TYPED_CORE_SIMPLIFY);
    }
}
