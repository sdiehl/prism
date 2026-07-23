//! The `prism-smt-query-v1` artifact: the canonical, content-addressed form of a
//! single verification obligation. It carries the narrowest logic, the
//! canonical SMT-LIB bytes, and the query digest that is its identity. The digest
//! deliberately commits only to the schema, logic, and canonical query bytes;
//! source-definition, contract, dependency, and typed-Core digests are outside
//! this artifact's identity.

use crate::verify::logic::Obligation;
use crate::verify::{normalize, smtlib};

pub(crate) const SCHEMA: &str = "prism-smt-query-v1";

/// A built query. The `digest` is the semantic identity: the schema, the logic,
/// and the canonical SMT-LIB bytes, hashed. It is independent of the Core content
/// hash by construction, since a solver never sees Core.
pub(crate) struct SmtQuery {
    pub(crate) logic: &'static str,
    pub(crate) smtlib: String,
    pub(crate) digest: String,
}

impl SmtQuery {
    /// Build the query for a well-formed obligation. Normalizes first, so the
    /// query is byte-identical for alpha-equivalent obligations.
    pub(crate) fn build(ob: &Obligation) -> Self {
        let norm = normalize::normalize(ob);
        let logic = smtlib::logic_name(&norm);
        let smtlib = smtlib::encode(&norm);
        let digest = query_digest(logic, &smtlib);
        Self {
            logic,
            smtlib,
            digest,
        }
    }

    /// The canonical, inspectable artifact envelope: a versioned header naming the
    /// logic and digest, then the SMT-LIB body. Deterministic; no paths, spans, or
    /// timestamps. This is what `dump smt` prints.
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(SCHEMA);
        out.push('\n');
        out.push_str("logic ");
        out.push_str(self.logic);
        out.push('\n');
        out.push_str("digest ");
        out.push_str(&self.digest);
        out.push('\n');
        out.push_str("--\n");
        out.push_str(&self.smtlib);
        out
    }
}

/// The query identity: a blake3 over the schema, logic, and canonical SMT-LIB
/// bytes. Changing an operator, literal, sort, or dependency changes the SMT-LIB
/// bytes and therefore this digest.
fn query_digest(logic: &str, smtlib: &str) -> String {
    let mut buf = Vec::new();
    buf.extend_from_slice(SCHEMA.as_bytes());
    buf.push(b'\n');
    buf.extend_from_slice(logic.as_bytes());
    buf.push(b'\n');
    buf.extend_from_slice(smtlib.as_bytes());
    blake3::hash(buf.as_slice()).to_hex().to_string()
}
