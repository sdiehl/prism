//! The verification interface: a module's logical exports and
//! contract summaries, content-addressed by a digest that is a pure function of
//! the logical content and independent of the runtime Core hash.
//!
//! It is the input to contract checking and (later) VC generation, distinct from
//! the runtime `ModuleInterface`: a proof-only edit moves this digest and only its
//! verification dependents, never the executable Core or native artifacts.

use std::collections::BTreeMap;

pub(crate) const SCHEMA: &str = "prism-verification-interface-v1";

/// Domain separator so the interface digest can never collide with a query or
/// contract digest built from a coincidentally identical byte stream.
const INTERFACE_DIGEST_DOMAIN: &[u8] = b"prism-verification-interface-v1";

/// The logical surface of a module: each `logic fn` by name with the digest of its
/// signature and body, and each contracted function by name with its contract
/// digest. The overall `digest` commits to both maps.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct VerificationInterface {
    logic: BTreeMap<String, String>,
    contracts: BTreeMap<String, String>,
    digest: String,
}

impl VerificationInterface {
    pub(crate) fn new(
        logic: BTreeMap<String, String>,
        contracts: BTreeMap<String, String>,
    ) -> Self {
        let digest = interface_digest(&logic, &contracts);
        Self {
            logic,
            contracts,
            digest,
        }
    }

    pub(crate) fn digest(&self) -> &str {
        &self.digest
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.logic.is_empty() && self.contracts.is_empty()
    }

    /// A deterministic, inspectable rendering: the schema, the interface digest,
    /// then the sorted `logic`/`contract` rows with their digests. No paths,
    /// spans, or timestamps, so it is stable across runs and checkout roots. This
    /// is what `dump verify` prints.
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(SCHEMA);
        out.push('\n');
        out.push_str("digest ");
        out.push_str(&self.digest);
        out.push('\n');
        for (name, digest) in &self.logic {
            out.push_str("logic ");
            out.push_str(name);
            out.push(' ');
            out.push_str(digest);
            out.push('\n');
        }
        for (name, digest) in &self.contracts {
            out.push_str("contract ");
            out.push_str(name);
            out.push(' ');
            out.push_str(digest);
            out.push('\n');
        }
        out
    }
}

/// A blake3 over the schema and the sorted `(name, digest)` rows of both maps. A
/// `BTreeMap` iterates in sorted key order, so the bytes are canonical.
fn interface_digest(
    logic: &BTreeMap<String, String>,
    contracts: &BTreeMap<String, String>,
) -> String {
    let mut buf = Vec::from(INTERFACE_DIGEST_DOMAIN);
    put_section(&mut buf, b"logic", logic);
    put_section(&mut buf, b"contract", contracts);
    blake3::hash(buf.as_slice()).to_hex().to_string()
}

fn put_section(buf: &mut Vec<u8>, tag: &[u8], rows: &BTreeMap<String, String>) {
    buf.extend_from_slice(tag);
    buf.extend_from_slice(&(rows.len() as u64).to_be_bytes());
    for (name, digest) in rows {
        buf.extend_from_slice(&(name.len() as u64).to_be_bytes());
        buf.extend_from_slice(name.as_bytes());
        buf.extend_from_slice(digest.as_bytes());
    }
}
