//! The capability-observation provenance protocol.
//!
//! Replay already records every capability observation a run performs so it can
//! reproduce the run byte for byte. This module promotes those observations to a
//! stable, hashable event protocol: each observation is a [`CapEvent`] carrying an
//! operation label, its argument values, and its result value; each event has a
//! canonical byte encoding and a `sha256` event hash; and a whole run's events fold
//! to one [`TraceDigest`] that names the run's observation sequence by hash.
//!
//! The protocol's contract is that recording a run and replaying its trace produce
//! the identical event sequence, and therefore the identical trace digest: the
//! interpreter re-runs the program deterministically during replay, so the same
//! operations fire with the same arguments and (served from the trace) the same
//! results. A run-lineage sidecar names its trace by this digest.
//!
//! The `.replay` trace file format is unchanged; these events are derived from the
//! same observations at the same interpreter sites, not a second on-disk format.

use std::fmt::Write as _;

use sha2::{Digest, Sha256};

/// The hash scheme every event hash, trace digest, and derived content digest in
/// this protocol commits to. Named once so a stored digest cannot disagree with
/// the scheme string that gives it meaning.
pub const EVENT_HASH_SCHEME: &str = "sha256";

// The domain tag folded into a trace digest, so a trace digest cannot collide with
// a bare event hash or another sha256 fold that happens over the same bytes.
const TRACE_FOLD_DOMAIN: &str = "prism-provenance-trace-v1";

// Per-value field tags in the canonical encoding. Scalars are inlined (they carry
// no delimiter); variable-length values are digested so an embedded newline can
// never forge a field boundary.
const VALUE_TAG_INT: &str = "int";
const VALUE_TAG_BOOL: &str = "bool";
const VALUE_TAG_STR: &str = "str";
const VALUE_TAG_BYTES: &str = "bytes";
const VALUE_TAG_UNIT: &str = "unit";

// Canonical operation labels for the recorded capability observations. One home for
// the family, referenced by the interpreter's observe sites; a rename here moves
// every event hash in lockstep rather than letting two sites disagree on a string.
// Capability prefixes whose event kinds are reserved: no operation label may
// use them until the boundary release defines their capability protocols, so
// external tooling reading event streams can rely on the prefixes staying
// meaningless until then. Mirrors the reserved seam effects in `names`.
pub const RESERVED_EVENT_CAPABILITIES: &[&str] =
    &[crate::names::NET_EFFECT, crate::names::ENTROPY_EFFECT];

/// Canonical capability operation in the provenance protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CapOp {
    EnvArgsCount,
    EnvArg,
    EnvGetenv,
    ConsoleReadLine,
    ConsoleReadInt,
    ProcessSystem,
    FsReadFile,
    FsReadFileBytes,
    FsFileExists,
    FsWriteFile,
    FsWriteBytes,
    FsAppendFile,
    FsRemoveFile,
    RandomRand,
    ClockWallNow,
    ClockMonoNow,
    ConsolePrint,
    ConsoleNewline,
    ConsoleEprint,
}

impl CapOp {
    /// Frozen protocol spelling used in event hashes and diagnostics.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::EnvArgsCount => "Env.args_count",
            Self::EnvArg => "Env.arg",
            Self::EnvGetenv => "Env.getenv",
            Self::ConsoleReadLine => "Console.read_line",
            Self::ConsoleReadInt => "Console.read_int",
            Self::ProcessSystem => "Process.system",
            Self::FsReadFile => "FileSystem.read_file",
            Self::FsReadFileBytes => "FileSystem.read_file_bytes",
            Self::FsFileExists => "FileSystem.file_exists",
            Self::FsWriteFile => "FileSystem.write_file",
            Self::FsWriteBytes => "FileSystem.write_bytes",
            Self::FsAppendFile => "FileSystem.append_file",
            Self::FsRemoveFile => "FileSystem.remove_file",
            Self::RandomRand => "Random.rand",
            Self::ClockWallNow => "Clock.wall_now",
            Self::ClockMonoNow => "Clock.mono_now",
            Self::ConsolePrint => "Console.print",
            Self::ConsoleNewline => "Console.newline",
            Self::ConsoleEprint => "Console.eprint",
        }
    }
}

pub const OP_ENV_ARGS_COUNT: CapOp = CapOp::EnvArgsCount;
pub const OP_ENV_ARG: CapOp = CapOp::EnvArg;
pub const OP_ENV_GETENV: CapOp = CapOp::EnvGetenv;
pub const OP_CONSOLE_READ_LINE: CapOp = CapOp::ConsoleReadLine;
pub const OP_CONSOLE_READ_INT: CapOp = CapOp::ConsoleReadInt;
pub const OP_PROCESS_SYSTEM: CapOp = CapOp::ProcessSystem;
pub const OP_FS_READ_FILE: CapOp = CapOp::FsReadFile;
pub const OP_FS_READ_FILE_BYTES: CapOp = CapOp::FsReadFileBytes;
pub const OP_FS_FILE_EXISTS: CapOp = CapOp::FsFileExists;
pub const OP_FS_WRITE_FILE: CapOp = CapOp::FsWriteFile;
pub const OP_FS_WRITE_BYTES: CapOp = CapOp::FsWriteBytes;
pub const OP_FS_APPEND_FILE: CapOp = CapOp::FsAppendFile;
pub const OP_FS_REMOVE_FILE: CapOp = CapOp::FsRemoveFile;
pub const OP_RANDOM_RAND: CapOp = CapOp::RandomRand;
pub const OP_CLOCK_WALL_NOW: CapOp = CapOp::ClockWallNow;
pub const OP_CLOCK_MONO_NOW: CapOp = CapOp::ClockMonoNow;
pub const OP_CONSOLE_PRINT: CapOp = CapOp::ConsolePrint;
pub const OP_CONSOLE_NEWLINE: CapOp = CapOp::ConsoleNewline;
pub const OP_CONSOLE_EPRINT: CapOp = CapOp::ConsoleEprint;

/// One argument or result value of a capability observation.
///
/// Held in the protocol's own value vocabulary, not the interpreter's runtime
/// values, so the encoding is a pure function of the observation and independent
/// of interpreter internals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventValue {
    Int(i64),
    Bool(bool),
    Str(String),
    Bytes(Vec<u8>),
    /// A read with no scalar result to record (there is currently none) or the
    /// absent result of an argument-only position.
    Unit,
}

impl EventValue {
    // The canonical one-field encoding. Scalars inline their value; variable-length
    // values commit their content digest, so no field value can contain the `\n`
    // that separates fields.
    fn encode(&self) -> String {
        match self {
            Self::Int(n) => format!("{VALUE_TAG_INT}:{n}"),
            Self::Bool(b) => format!("{VALUE_TAG_BOOL}:{}", u8::from(*b)),
            Self::Str(s) => format!("{VALUE_TAG_STR}:{}", sha256_hex(s.as_bytes())),
            Self::Bytes(v) => format!("{VALUE_TAG_BYTES}:{}", sha256_hex(v)),
            Self::Unit => format!("{VALUE_TAG_UNIT}:"),
        }
    }

    /// The raw bytes this value digests over, for a value whose content is worth a
    /// lineage node (a file's bytes, an environment value). Scalars have no content
    /// body and return `None`.
    #[must_use]
    pub fn content_bytes(&self) -> Option<Vec<u8>> {
        match self {
            Self::Str(s) => Some(s.as_bytes().to_vec()),
            Self::Bytes(v) => Some(v.clone()),
            Self::Int(_) | Self::Bool(_) | Self::Unit => None,
        }
    }

    /// This value as a string argument, when it is one (a path, an environment
    /// variable name).
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }
}

/// One recorded capability observation.
///
/// An operation, its arguments, and its result: the building block of the
/// provenance protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapEvent {
    /// A canonical operation label from the `OP_*` family.
    pub op: CapOp,
    /// The observed arguments, in call order.
    pub args: Vec<EventValue>,
    /// The observed result.
    pub result: EventValue,
}

impl CapEvent {
    // The canonical byte encoding: newline-separated op label, argument count, each
    // argument's field, then the result's field. Every variable-length value is
    // already digested by `EventValue::encode`, so the join is unambiguous.
    fn canonical(&self) -> String {
        let mut out = String::new();
        let _ = write!(out, "{}\n{}", self.op.label(), self.args.len());
        for arg in &self.args {
            let _ = write!(out, "\n{}", arg.encode());
        }
        let _ = write!(out, "\n{}", self.result.encode());
        out
    }

    /// The scheme-tagged event hash: `sha256:<hex>` over the canonical encoding.
    #[must_use]
    pub fn event_hash(&self) -> String {
        format!(
            "{EVENT_HASH_SCHEME}:{}",
            sha256_hex(self.canonical().as_bytes())
        )
    }
}

/// The digest of a whole run's observation sequence.
///
/// The scheme, the fold over the per-event hashes, and the event count. Two runs
/// of the same program on the same inputs (a record and a replay of its trace)
/// share this digest exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceDigest {
    pub scheme: &'static str,
    pub hash: String,
    pub events: usize,
}

/// Fold a run's events into its [`TraceDigest`].
#[must_use]
pub fn trace_digest(events: &[CapEvent]) -> TraceDigest {
    let mut folded = String::new();
    let _ = write!(folded, "{TRACE_FOLD_DOMAIN}\n{}", events.len());
    for event in events {
        let _ = write!(folded, "\n{}", event.event_hash());
    }
    TraceDigest {
        scheme: EVENT_HASH_SCHEME,
        hash: sha256_hex(folded.as_bytes()),
        events: events.len(),
    }
}

/// Lowercase-hex `sha256` of `bytes`. The one digest primitive the protocol and its
/// lineage consumers share.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn getenv(name: &str, value: &str) -> CapEvent {
        CapEvent {
            op: OP_ENV_GETENV,
            args: vec![EventValue::Str(name.to_string())],
            result: EventValue::Str(value.to_string()),
        }
    }

    // A newline in a string value must not forge a field boundary: two events that
    // differ only by where a newline sits must hash differently.
    #[test]
    fn newline_in_value_cannot_forge_a_field() {
        let a = getenv("A", "x\ny");
        let b = getenv("A\nx", "y");
        assert_ne!(a.event_hash(), b.event_hash());
    }

    // The trace digest is a pure function of the event sequence and its length.
    // Every live operation label stays outside the reserved capability
    // prefixes, so reserving them is a fact, not a hope.
    #[test]
    fn no_live_op_label_uses_a_reserved_capability() {
        let live = [
            OP_ENV_ARGS_COUNT,
            OP_ENV_ARG,
            OP_ENV_GETENV,
            OP_CONSOLE_READ_LINE,
            OP_CONSOLE_READ_INT,
            OP_PROCESS_SYSTEM,
            OP_FS_READ_FILE,
            OP_FS_READ_FILE_BYTES,
            OP_FS_FILE_EXISTS,
            OP_FS_WRITE_FILE,
            OP_FS_WRITE_BYTES,
            OP_FS_APPEND_FILE,
            OP_FS_REMOVE_FILE,
            OP_RANDOM_RAND,
            OP_CLOCK_WALL_NOW,
            OP_CLOCK_MONO_NOW,
        ];
        for op in live {
            for cap in RESERVED_EVENT_CAPABILITIES {
                assert!(
                    !op.label().starts_with(&format!("{cap}.")),
                    "live op `{}` uses reserved capability `{cap}`",
                    op.label()
                );
            }
        }
    }

    #[test]
    fn trace_digest_is_a_function_of_the_sequence() {
        let seq = vec![getenv("HOME", "/root"), getenv("PATH", "/bin")];
        assert_eq!(trace_digest(&seq), trace_digest(&seq.clone()));
        let mut reordered = seq.clone();
        reordered.reverse();
        assert_ne!(trace_digest(&seq).hash, trace_digest(&reordered).hash);
    }
}
