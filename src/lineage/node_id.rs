use std::fmt::Write as _;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MINTED_ID_SCHEME: &str = "sha256";

/// A digest-derived node identity. Never positional, never a path or name.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct NodeId(pub String);

pub(crate) fn minted_id(bytes: &[u8]) -> NodeId {
    NodeId(format!(
        "{MINTED_ID_SCHEME}:{}",
        hex(&Sha256::digest(bytes))
    ))
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}
