use std::fmt;

/// Compiler subsystem that owns a diagnostic code range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorPhase {
    Type,
    Lex,
    Parse,
    Resolve,
    Lower,
    Codegen,
    Runtime,
    Io,
    Internal,
}

/// Stable external identity of a compiler diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ErrorCode {
    phase: ErrorPhase,
    spelling: &'static str,
}

impl ErrorCode {
    pub(crate) const fn new(phase: ErrorPhase, spelling: &'static str) -> Self {
        Self { phase, spelling }
    }

    #[must_use]
    pub const fn phase(self) -> ErrorPhase {
        self.phase
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        self.spelling
    }
}

pub(crate) const LEX_INVALID: &str = "E7000";
pub(crate) const LEX_EMPTY_HOLE: &str = "E7001";
pub(crate) const LEX_UNTERMINATED_HOLE: &str = "E7002";
pub(crate) const LEX_UNTERMINATED_STRING: &str = "E7003";
pub(crate) const LEX_NUMBER_SEPARATOR: &str = "E7004";
pub(crate) const PARSE_SYNTAX: &str = "E7100";
pub(crate) const PARSE_EOF: &str = "E7101";
pub(crate) const RESOLVE_MODULE: &str = "E7200";
pub(crate) const RESOLVE_PROJECT: &str = "E7201";
pub(crate) const RESOLVE_PACKAGE: &str = "E7202";
pub(crate) const RESOLVE_LINEAGE: &str = "E7203";
pub(crate) const RESOLVE_COMMAND: &str = "E7204";
pub(crate) const PATCH_REFUSAL: &str = "E7205";
pub(crate) const CODEGEN_BACKEND: &str = "E7400";
pub(crate) const CODEGEN_DOCS: &str = "E7401";
pub(crate) const CODEGEN_FORMAT: &str = "E7402";
pub(crate) const CODEGEN_DUMP: &str = "E7403";
pub(crate) const CODEGEN_VERIFICATION: &str = "E7404";
pub(crate) const RUNTIME_EVALUATION: &str = "E7500";
pub(crate) const RUNTIME_REPLAY: &str = "E7501";
pub(crate) const RUNTIME_DEBUGGER: &str = "E7502";
pub(crate) const IO: &str = "E7600";
pub(crate) const TYPE_MISMATCH_LEGACY: &str = "E1098";
pub(crate) const TYPE_OTHER_LEGACY: &str = "E1998";
/// Dedicated diagnostic identity for a named typed hole.
pub const TYPED_HOLE: ErrorCode = ErrorCode::new(ErrorPhase::Type, "E1021");
/// An exhaustive handler omitted a declared operation of an effect it names.
pub const INCOMPLETE_HANDLER: ErrorCode = ErrorCode::new(ErrorPhase::Type, "E5011");
pub(crate) const SCOPE_UNBOUND: &str = "E2000";
pub(crate) const SCOPE_OTHER_LEGACY: &str = "E2099";
/// The checked declarations could not be converted into the typed-Core
/// verification environment.
pub const TYPED_CORE_ENVIRONMENT: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9995");
/// Erasing verified typed Core changed the compatibility Core tree.
pub const TYPED_CORE_ERASURE: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9994");
/// A witness-preserving typed-Core specialization plan could not be constructed.
pub const TYPED_CORE_SPECIALIZATION: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9993");
/// Typed-Core simplification did not reach a fixed point within the runaway
/// rewrite bound.
pub const TYPED_CORE_SIMPLIFY: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9992");
/// Typed effect lowering could not produce a verified `EffectLowered` program.
pub const TYPED_CORE_EFFECT_LOWERING: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9991");
/// The elaborator could not construct a typed-Core witness.
pub const TYPED_CORE_CONSTRUCTION: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9996");
/// The independent typed-Core checker rejected a constructed witness.
pub const TYPED_CORE_VERIFICATION: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9997");
/// Internal Logic IR built for verification was not well-sorted. The internal IR
/// has no surface syntax, so this only fires on a compiler bug that built a
/// malformed obligation.
pub const SMT_LOGIC_WELLFORMED: ErrorCode = ErrorCode::new(ErrorPhase::Internal, "E9990");
pub(crate) const INTERNAL_TYPE: &str = "E9998";
pub(crate) const INTERNAL: &str = "E9999";

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.spelling)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn phase_codes_are_unique() {
        let codes = [
            LEX_INVALID,
            LEX_EMPTY_HOLE,
            LEX_UNTERMINATED_HOLE,
            LEX_UNTERMINATED_STRING,
            LEX_NUMBER_SEPARATOR,
            PARSE_SYNTAX,
            PARSE_EOF,
            RESOLVE_MODULE,
            RESOLVE_PROJECT,
            RESOLVE_PACKAGE,
            RESOLVE_LINEAGE,
            RESOLVE_COMMAND,
            PATCH_REFUSAL,
            CODEGEN_BACKEND,
            CODEGEN_DOCS,
            CODEGEN_FORMAT,
            CODEGEN_DUMP,
            CODEGEN_VERIFICATION,
            RUNTIME_EVALUATION,
            RUNTIME_REPLAY,
            RUNTIME_DEBUGGER,
            IO,
            TYPE_MISMATCH_LEGACY,
            TYPE_OTHER_LEGACY,
            TYPED_HOLE.as_str(),
            INCOMPLETE_HANDLER.as_str(),
            SCOPE_UNBOUND,
            SCOPE_OTHER_LEGACY,
            TYPED_CORE_ERASURE.as_str(),
            TYPED_CORE_SPECIALIZATION.as_str(),
            TYPED_CORE_SIMPLIFY.as_str(),
            TYPED_CORE_EFFECT_LOWERING.as_str(),
            TYPED_CORE_ENVIRONMENT.as_str(),
            TYPED_CORE_CONSTRUCTION.as_str(),
            TYPED_CORE_VERIFICATION.as_str(),
            SMT_LOGIC_WELLFORMED.as_str(),
            INTERNAL_TYPE,
            INTERNAL,
        ];
        assert_eq!(
            codes.len(),
            codes.into_iter().collect::<BTreeSet<_>>().len()
        );
    }
}
