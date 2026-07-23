//! Versioned semantic-patch artifacts and their structured surface-term payload.
//!
//! A patch never carries an unchecked source blob. Its replacement is a
//! canonical, lossless lexical tree over exactly one top-level declaration. The
//! tree is content-addressed independently of the patch envelope, and decoding
//! proves that it reconstructs canonical source with the same declaration kind
//! and name. This is intentionally a surface boundary rather than a serialization
//! of Prism's in-memory AST: compiler representation changes do not silently move
//! the wire format.

use std::fmt;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use thiserror::Error;

use crate::core::HASH_SCHEME;
use crate::kw;
use crate::syntax::ast::Program;

/// The semantic-patch artifact format.
pub const PATCH_FORMAT: &str = "prism-patch-v1";
/// The structured single-definition surface encoding carried by a patch.
pub const TERM_FORMAT: &str = "prism-surface-term-v1";

const TERM_ADDRESS_DOMAIN: &[u8] = b"prism-surface-term-address-v1";
const PATCH_ADDRESS_DOMAIN: &[u8] = b"prism-patch-address-v1";
pub(crate) const DIGEST_HEX_LEN: usize = 64;

/// A stable top-level declaration family in the structured surface encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TermKind {
    Value,
    Data,
    Effect,
    Error,
    Alias,
    Class,
    Instance,
    Pattern,
    Stable,
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Value => "value",
            Self::Data => "data",
            Self::Effect => "effect",
            Self::Error => "error",
            Self::Alias => "alias",
            Self::Class => "class",
            Self::Instance => "instance",
            Self::Pattern => "pattern",
            Self::Stable => "stable",
        };
        f.write_str(name)
    }
}

/// One lossless lexical node. `leading` owns the canonical trivia before the
/// token, while `lexeme` owns the token's exact source bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurfaceToken {
    pub leading: String,
    pub lexeme: String,
}

#[derive(Serialize)]
struct TermPayload<'a> {
    format: &'a str,
    kind: TermKind,
    name: &'a str,
    tokens: &'a [SurfaceToken],
    trailing: &'a str,
}

/// A canonical, content-addressed encoding of one surface declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurfaceTerm {
    pub format: String,
    pub digest: String,
    pub kind: TermKind,
    pub name: String,
    pub tokens: Vec<SurfaceToken>,
    pub trailing: String,
}

impl SurfaceTerm {
    /// Encode exactly one top-level declaration after applying Prism's canonical
    /// formatter. Comments and visibility markers are retained as syntax trivia.
    ///
    /// # Errors
    /// Fails when the source is invalid or does not contain exactly one supported
    /// declaration.
    pub fn from_source(source: &str) -> Result<Self, PatchArtifactError> {
        let canonical = crate::fmt::format(source)
            .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?;
        let site = only_site(&canonical)?;
        let (tokens, _) = crate::lex::lex_raw(&canonical)
            .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?;
        let mut nodes = Vec::with_capacity(tokens.len());
        let mut end = 0;
        for (start, _, next) in tokens {
            if start < end || next < start || next > canonical.len() {
                return Err(PatchArtifactError::InvalidTerm(
                    "lexer produced overlapping surface token ranges".to_string(),
                ));
            }
            nodes.push(SurfaceToken {
                leading: canonical[end..start].to_string(),
                lexeme: canonical[start..next].to_string(),
            });
            end = next;
        }
        let trailing = canonical[end..].to_string();
        let digest = term_digest(TERM_FORMAT, site.kind, &site.name, &nodes, &trailing)?;
        Ok(Self {
            format: TERM_FORMAT.to_string(),
            digest,
            kind: site.kind,
            name: site.name,
            tokens: nodes,
            trailing,
        })
    }

    /// Decode and validate the structured term, returning canonical Prism text.
    ///
    /// # Errors
    /// Refuses foreign formats, malformed addresses, non-canonical projections,
    /// and payloads whose parsed identity differs from their declared identity.
    pub fn render(&self) -> Result<String, PatchArtifactError> {
        if self.format != TERM_FORMAT {
            return Err(PatchArtifactError::ForeignTermFormat(self.format.clone()));
        }
        validate_digest(&self.digest, "term")?;
        let expected = term_digest(
            &self.format,
            self.kind,
            &self.name,
            &self.tokens,
            &self.trailing,
        )?;
        if self.digest != expected {
            return Err(PatchArtifactError::AddressMismatch {
                object: "term",
                expected,
                found: self.digest.clone(),
            });
        }
        let mut source = String::new();
        for token in &self.tokens {
            source.push_str(&token.leading);
            source.push_str(&token.lexeme);
        }
        source.push_str(&self.trailing);
        let canonical = crate::fmt::format(&source)
            .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?;
        if source != canonical {
            return Err(PatchArtifactError::NonCanonicalTerm);
        }
        let site = only_site(&source)?;
        if site.kind != self.kind || site.name != self.name {
            return Err(PatchArtifactError::TermIdentityMismatch {
                expected: format!("{} {}", self.kind, self.name),
                found: format!("{} {}", site.kind, site.name),
            });
        }
        Ok(source)
    }
}

/// One hash-scheme-tagged digest pin in a patch artifact. The target address
/// identifies the observed definition; the base address identifies its namespace.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PatchTarget {
    pub scheme: String,
    pub digest: String,
}

impl PatchTarget {
    #[must_use]
    pub fn new(digest: impl Into<String>) -> Self {
        Self {
            scheme: HASH_SCHEME.to_string(),
            digest: digest.into(),
        }
    }

    fn validate(&self) -> Result<(), PatchArtifactError> {
        if self.scheme != HASH_SCHEME {
            return Err(PatchArtifactError::ForeignHashScheme(self.scheme.clone()));
        }
        validate_digest(&self.digest, "target")
    }
}

#[derive(Serialize)]
struct PatchPayload<'a> {
    format: &'a str,
    base_namespace: &'a PatchTarget,
    target: &'a PatchTarget,
    replacement: &'a SurfaceTerm,
    claimed_delta: Option<&'a Value>,
}

/// A digest-pinned, versioned semantic patch.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PatchArtifact {
    pub format: String,
    pub digest: String,
    /// Whole semantic namespace the proposal was authored against. The target
    /// digest catches a changed definition; this catches every other world move.
    pub base_namespace: PatchTarget,
    pub target: PatchTarget,
    pub replacement: SurfaceTerm,
    /// Preserved as opaque proposal metadata; patch judgment never reads it.
    pub claimed_delta: Option<Value>,
}

impl PatchArtifact {
    /// Construct and content-address a patch artifact.
    ///
    /// # Errors
    /// Fails when the target or replacement is malformed.
    pub fn new(
        base_namespace: PatchTarget,
        target: PatchTarget,
        replacement: SurfaceTerm,
        claimed_delta: Option<Value>,
    ) -> Result<Self, PatchArtifactError> {
        base_namespace.validate()?;
        target.validate()?;
        replacement.render()?;
        let digest = patch_digest(
            PATCH_FORMAT,
            &base_namespace,
            &target,
            &replacement,
            claimed_delta.as_ref(),
        )?;
        Ok(Self {
            format: PATCH_FORMAT.to_string(),
            digest,
            base_namespace,
            target,
            replacement,
            claimed_delta,
        })
    }

    /// Validate every version and content-address boundary in the artifact.
    ///
    /// # Errors
    /// Refuses foreign formats, malformed digests, and changed payloads.
    pub fn validate(&self) -> Result<(), PatchArtifactError> {
        if self.format != PATCH_FORMAT {
            return Err(PatchArtifactError::ForeignPatchFormat(self.format.clone()));
        }
        validate_digest(&self.digest, "patch")?;
        self.base_namespace.validate()?;
        self.target.validate()?;
        self.replacement.render()?;
        let expected = patch_digest(
            &self.format,
            &self.base_namespace,
            &self.target,
            &self.replacement,
            self.claimed_delta.as_ref(),
        )?;
        if self.digest != expected {
            return Err(PatchArtifactError::AddressMismatch {
                object: "patch",
                expected,
                found: self.digest.clone(),
            });
        }
        Ok(())
    }
}

/// A stable refusal raised before semantic judging begins.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum PatchArtifactError {
    #[error("unsupported surface term format `{0}`")]
    ForeignTermFormat(String),
    #[error("unsupported patch format `{0}`")]
    ForeignPatchFormat(String),
    #[error("unsupported target hash scheme `{0}`")]
    ForeignHashScheme(String),
    #[error("invalid {0} digest; expected 64 lowercase hexadecimal characters")]
    InvalidDigest(&'static str),
    #[error("{object} address mismatch: expected {expected}, found {found}")]
    AddressMismatch {
        object: &'static str,
        expected: String,
        found: String,
    },
    #[error("invalid structured term: {0}")]
    InvalidTerm(String),
    #[error("structured term is not the canonical formatter projection")]
    NonCanonicalTerm,
    #[error("structured term declares `{expected}`, but decodes as `{found}`")]
    TermIdentityMismatch { expected: String, found: String },
    #[error("structured term must contain exactly one supported top-level declaration")]
    ExpectedOneDefinition,
    #[error("could not serialize patch artifact: {0}")]
    Serialization(String),
}

#[derive(Clone, Debug)]
struct DefinitionSite {
    kind: TermKind,
    name: String,
    start: usize,
    end: usize,
}

struct DefinitionLayout {
    sites: Vec<DefinitionSite>,
    boundaries: Vec<usize>,
}

/// Extract one named declaration as a canonical structured term.
///
/// # Errors
/// Fails when the source is invalid, the name is absent or ambiguous, or the
/// extracted declaration cannot round-trip through the term encoding.
pub fn extract_term(source: &str, name: &str) -> Result<SurfaceTerm, PatchArtifactError> {
    let matches = extract_terms(source)?
        .into_iter()
        .filter(|term| term.name == name)
        .collect::<Vec<_>>();
    let [term] = matches.as_slice() else {
        return Err(PatchArtifactError::InvalidTerm(format!(
            "definition `{name}` was not found uniquely"
        )));
    };
    Ok(term.clone())
}

/// Extract every supported declaration from a source with one whole-file format
/// pass, preserving source order.
///
/// # Errors
/// Fails when the source is invalid or any declaration cannot round-trip through
/// the structured term encoding.
pub fn extract_terms(source: &str) -> Result<Vec<SurfaceTerm>, PatchArtifactError> {
    let canonical = crate::fmt::format(source)
        .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?;
    let layout = definition_layout(&canonical)?;
    layout
        .sites
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let (start, end) =
                declaration_range(&canonical, &layout.sites, &layout.boundaries, index);
            SurfaceTerm::from_source(&canonical[start..end])
        })
        .collect()
}

/// Replace one named declaration with a validated structured term and format the
/// whole source canonically.
///
/// # Errors
/// Fails on a stale/ambiguous name, a name-changing replacement, or invalid
/// source after the splice.
pub fn replace_term(
    source: &str,
    target_name: &str,
    replacement: &SurfaceTerm,
) -> Result<String, PatchArtifactError> {
    let rendered = replacement.render()?;
    if replacement.name != target_name {
        return Err(PatchArtifactError::TermIdentityMismatch {
            expected: target_name.to_string(),
            found: replacement.name.clone(),
        });
    }
    let canonical = crate::fmt::format(source)
        .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?;
    let layout = definition_layout(&canonical)?;
    let matches = layout
        .sites
        .iter()
        .enumerate()
        .filter_map(|(index, site)| (site.name == target_name).then_some(index))
        .collect::<Vec<_>>();
    let [index] = matches.as_slice() else {
        return Err(PatchArtifactError::InvalidTerm(format!(
            "definition `{target_name}` was not found uniquely"
        )));
    };
    let site = &layout.sites[*index];
    if site.kind != replacement.kind {
        return Err(PatchArtifactError::TermIdentityMismatch {
            expected: format!("{} {target_name}", site.kind),
            found: format!("{} {}", replacement.kind, replacement.name),
        });
    }
    let (start, end) = declaration_range(&canonical, &layout.sites, &layout.boundaries, *index);
    let mut changed = String::with_capacity(canonical.len() - (end - start) + rendered.len());
    changed.push_str(&canonical[..start]);
    changed.push_str(&rendered);
    changed.push_str(&canonical[end..]);
    crate::fmt::format(&changed).map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))
}

fn term_digest(
    format: &str,
    kind: TermKind,
    name: &str,
    tokens: &[SurfaceToken],
    trailing: &str,
) -> Result<String, PatchArtifactError> {
    let payload = serde_json::to_vec(&TermPayload {
        format,
        kind,
        name,
        tokens,
        trailing,
    })
    .map_err(|error| PatchArtifactError::Serialization(error.to_string()))?;
    Ok(address(TERM_ADDRESS_DOMAIN, &payload))
}

fn patch_digest(
    format: &str,
    base_namespace: &PatchTarget,
    target: &PatchTarget,
    replacement: &SurfaceTerm,
    claimed_delta: Option<&Value>,
) -> Result<String, PatchArtifactError> {
    let payload = serde_json::to_vec(&PatchPayload {
        format,
        base_namespace,
        target,
        replacement,
        claimed_delta,
    })
    .map_err(|error| PatchArtifactError::Serialization(error.to_string()))?;
    Ok(address(PATCH_ADDRESS_DOMAIN, &payload))
}

fn address(domain: &[u8], payload: &[u8]) -> String {
    let mut hasher = blake3::Hasher::new();
    hash_field(&mut hasher, domain);
    hash_field(&mut hasher, payload);
    hasher.finalize().to_hex().to_string()
}

fn hash_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn validate_digest(digest: &str, object: &'static str) -> Result<(), PatchArtifactError> {
    if digest.len() == DIGEST_HEX_LEN
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        Ok(())
    } else {
        Err(PatchArtifactError::InvalidDigest(object))
    }
}

fn only_site(source: &str) -> Result<DefinitionSite, PatchArtifactError> {
    let program = crate::parse::parse(source)
        .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?
        .program;
    if !program.imports.is_empty() || !program.canonicals.is_empty() {
        return Err(PatchArtifactError::ExpectedOneDefinition);
    }
    let sites = sites(&program);
    let [site] = sites.as_slice() else {
        return Err(PatchArtifactError::ExpectedOneDefinition);
    };
    Ok(site.clone())
}

fn definition_layout(source: &str) -> Result<DefinitionLayout, PatchArtifactError> {
    let program = crate::parse::parse(source)
        .map_err(|error| PatchArtifactError::InvalidTerm(error.to_string()))?
        .program;
    let sites = sites(&program);
    let mut boundaries = sites.iter().map(|site| site.start).collect::<Vec<_>>();
    boundaries.extend(program.imports.iter().map(|item| item.span.start));
    boundaries.extend(program.canonicals.iter().map(|item| item.span.start));
    boundaries.sort_unstable();
    boundaries.dedup();
    Ok(DefinitionLayout { sites, boundaries })
}

fn sites(program: &Program) -> Vec<DefinitionSite> {
    let mut out = Vec::new();
    for declaration in &program.fns {
        out.push(DefinitionSite {
            kind: TermKind::Value,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.types {
        out.push(DefinitionSite {
            kind: TermKind::Data,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.effects {
        out.push(DefinitionSite {
            kind: TermKind::Effect,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.errors {
        out.push(DefinitionSite {
            kind: TermKind::Error,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.aliases {
        out.push(DefinitionSite {
            kind: TermKind::Alias,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.synonyms {
        out.push(DefinitionSite {
            kind: TermKind::Alias,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.classes {
        out.push(DefinitionSite {
            kind: TermKind::Class,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.instances {
        out.push(DefinitionSite {
            kind: TermKind::Instance,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.patterns {
        out.push(DefinitionSite {
            kind: TermKind::Pattern,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    for declaration in &program.stable {
        out.push(DefinitionSite {
            kind: TermKind::Stable,
            name: declaration.name.clone(),
            start: declaration.span.start,
            end: declaration.span.end,
        });
    }
    out.sort_by_key(|site| site.start);
    out
}

// Use the next top-level declaration rather than an AST end span as the upper
// bound. Layout-delimited bodies can close after their surface node's diagnostic
// span; the next declaration start is the parser-independent source boundary.
fn declaration_range(
    source: &str,
    sites: &[DefinitionSite],
    boundaries: &[usize],
    index: usize,
) -> (usize, usize) {
    let site = &sites[index];
    let start = item_start(source, site.start);
    let end = boundaries
        .iter()
        .copied()
        .find(|boundary| *boundary > site.start)
        .map_or(source.len(), |boundary| item_start(source, boundary));
    debug_assert!(site.end <= end);
    (start, end)
}

fn item_start(source: &str, offset: usize) -> usize {
    let mut start = line_start(source, offset);
    while start > 0 {
        let previous_end = start.saturating_sub(1);
        let previous_start = line_start(source, previous_end);
        let previous = source[previous_start..previous_end].trim();
        // A `deprecated` line attaches to the following declaration only when the
        // keyword is followed by a space, matching its surface token boundary
        // rather than any identifier merely starting with those letters.
        let is_deprecated_line = previous
            .strip_prefix(kw::DEPRECATED)
            .is_some_and(|rest| rest.starts_with(' '));
        if previous.starts_with(kw::LINE_COMMENT) || is_deprecated_line {
            start = previous_start;
        } else {
            break;
        }
    }
    start
}

fn line_start(source: &str, offset: usize) -> usize {
    source[..offset].rfind('\n').map_or(0, |index| index + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ORIGINAL: &str = "-- | Increment a number.\npub fn inc(x : Int) : Int = x + 1\n";

    #[test]
    fn term_round_trip_is_canonical_and_addressed() {
        let term = SurfaceTerm::from_source(ORIGINAL).unwrap();
        assert_eq!(term.kind, TermKind::Value);
        assert_eq!(term.name, "inc");
        assert_eq!(term.render().unwrap(), ORIGINAL);
        assert_eq!(term.digest.len(), DIGEST_HEX_LEN);

        let json = serde_json::to_vec(&term).unwrap();
        let decoded: SurfaceTerm = serde_json::from_slice(&json).unwrap();
        assert_eq!(decoded.render().unwrap(), ORIGINAL);
    }

    #[test]
    fn changed_term_bytes_are_refused() {
        let mut term = SurfaceTerm::from_source(ORIGINAL).unwrap();
        let one = term
            .tokens
            .iter_mut()
            .find(|token| token.lexeme == "1")
            .unwrap();
        one.lexeme = "2".to_string();
        assert!(matches!(
            term.render(),
            Err(PatchArtifactError::AddressMismatch { object: "term", .. })
        ));
    }

    #[test]
    fn patch_round_trip_pins_target_and_replacement() {
        let term = SurfaceTerm::from_source(ORIGINAL).unwrap();
        let patch = PatchArtifact::new(
            PatchTarget::new("b".repeat(DIGEST_HEX_LEN)),
            PatchTarget::new("a".repeat(DIGEST_HEX_LEN)),
            term,
            None,
        )
        .unwrap();
        patch.validate().unwrap();
        let bytes = serde_json::to_vec(&patch).unwrap();
        let decoded: PatchArtifact = serde_json::from_slice(&bytes).unwrap();
        decoded.validate().unwrap();
    }

    #[test]
    fn extract_and_replace_preserve_the_other_definitions() {
        let source = "fn before() = 0\n\n-- | Increment.\npub fn inc(x : Int) : Int = x + 1\n\nfn after() = 9\n";
        let current = extract_term(source, "inc").unwrap();
        assert_eq!(
            current.render().unwrap(),
            "-- | Increment.\npub fn inc(x : Int) : Int = x + 1\n"
        );
        let replacement =
            SurfaceTerm::from_source("-- | Increment twice.\npub fn inc(x : Int) : Int = x + 2\n")
                .unwrap();
        let changed = replace_term(source, "inc", &replacement).unwrap();
        assert!(changed.contains("fn before() = 0"));
        assert!(changed.contains("Increment twice"));
        assert!(changed.contains("fn after() = 9"));
        assert!(!changed.contains("x + 1"));
    }
}
