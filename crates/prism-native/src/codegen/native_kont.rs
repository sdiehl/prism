//! Native continuation metadata emitted beside LLVM modules.
//!
//! The table is intentionally textual: it must be easy to dump, inspect, and
//! parse from the C runtime without linking Rust code. This module owns the Rust
//! spelling of that wire text so driver dumps, LLVM globals, and tests cannot
//! drift independently.

use std::collections::BTreeMap;

use prism_common::format::FormatTag;
use prism_common::sym::Sym;
use prism_core::core::{Core, Hashes, HASH_SCHEME};

pub(crate) const TABLE_GLOBAL: &str = "prism_native_kont_table";
pub(crate) const STATE_MAP_GLOBAL: &str = "prism_native_kont_state_map";
pub(crate) const PTRS_GLOBAL: &str = "prism_native_kont_ptrs";
pub(crate) const PTRS_LEN_GLOBAL: &str = "prism_native_kont_ptrs_len";
// Mach-O section names are a `__SEGMENT,__section` pair; a bare ELF-style
// name lands in a nameless segment, which Darwin 25 rejects at exec with
// EBADMACHO. The snapshot normalizer maps both spellings to one canonical form.
#[cfg(target_os = "macos")]
pub(crate) const TABLE_SECTION: &str = "__DATA,__prism_kont";
#[cfg(not(target_os = "macos"))]
pub(crate) const TABLE_SECTION: &str = ".prism_kont";

pub(crate) const ENTER_SYMBOL: &str = "prism_native_kont_enter";
pub(crate) const ARG_SYMBOL: &str = "prism_native_kont_arg";
pub(crate) const TAILCALL_SYMBOL: &str = "prism_native_kont_tailcall";
pub(crate) const LEAVE_SYMBOL: &str = "prism_native_kont_leave";

#[cfg(test)]
pub(crate) const RUNTIME_SURFACE_SYMBOLS: &[&str] = &[
    "prism_native_kont_table_bytes",
    "prism_native_kont_table_len",
    "prism_native_kont_state_map_bytes",
    "prism_native_kont_state_map_len",
    "prism_native_kont_frame_mode",
    ENTER_SYMBOL,
    ARG_SYMBOL,
    TAILCALL_SYMBOL,
    LEAVE_SYMBOL,
    "prism_native_kont_shadow_depth",
    "prism_native_kont_state_lookup",
    "prism_native_kont_scheme",
    "prism_native_kont_bundle",
    "prism_native_kont_lookup",
    "prism_native_kont_lookup_ptr",
    "prism_native_kont_lookup_pc",
    "prism_native_kont_capture_frames",
    "prism_native_kont_capture_manifest",
    "prism_native_kont_resume_entry",
    TABLE_GLOBAL,
];

const SCHEME_ROW: &str = "scheme";
const BUNDLE_ROW: &str = "bundle";
const COMPILER_ROW: &str = "compiler";
const TARGET_ROW: &str = "target";
const BACKEND_ROW: &str = "backend";
const FLAG_ROW: &str = "flag";
const FN_ROW: &str = "fn";
const STATE_MAP_HEADER: &str = "state-map 1";
const SLOT_FORMAT_ROW: &str = "slot-format";
const SLOT_FORMAT: FormatTag = FormatTag::new("prism-native-abi-word-v1");
const STATE_ROW: &str = "state";
const ARITY_FIELD: &str = "arity";
const SLOTS_FIELD: &str = "slots";
const EMPTY_SLOTS: &str = "abi-word[]";

pub(crate) struct Row<'a> {
    pub symbol: &'a str,
    pub def_hash: &'a str,
    pub core_name: &'a str,
}

#[derive(Debug)]
pub struct IdentityRow<'a> {
    pub key: &'a str,
    pub value: String,
}

/// The `fn` rows of a continuation table, each `fn <symbol> <hash> <name>`.
///
/// # Errors
/// Refuses a `fn` row that does not carry exactly those three fields, so a
/// malformed table fails loudly instead of decoding to empty symbols.
pub(crate) fn rows(table: &str) -> Result<Vec<Row<'_>>, String> {
    table
        .lines()
        .filter(|line| line.split_whitespace().next() == Some(FN_ROW))
        .map(
            |line| match line.split_whitespace().collect::<Vec<_>>()[..] {
                [_, symbol, def_hash, core_name] => Ok(Row {
                    symbol,
                    def_hash,
                    core_name,
                }),
                _ => Err(format!("malformed native kont table row: {line}")),
            },
        )
        .collect()
}

#[must_use]
pub fn table(hashes: &Hashes, bundle: &str, identity: &[IdentityRow<'_>]) -> String {
    let mut names: Vec<&Sym> = hashes.keys().collect();
    names.sort_by_key(|s| s.as_str());

    let mut lines = vec![
        format!("{SCHEME_ROW}  {HASH_SCHEME}"),
        format!("{BUNDLE_ROW}  {bundle}"),
        format!("{COMPILER_ROW}  {}", env!("CARGO_PKG_VERSION")),
        format!("{TARGET_ROW}  {}", env!("PRISM_TARGET")),
        format!("{BACKEND_ROW}  llvm"),
    ];
    lines.extend(
        identity
            .iter()
            .map(|row| format!("{FLAG_ROW}  {}  {}", row.key, row.value)),
    );
    lines.extend(names.into_iter().map(|name| {
        format!(
            "{FN_ROW}      {}  {}  {}",
            super::native_symbol(name.as_str()),
            hashes[name],
            name.as_str()
        )
    }));
    terminated(lines)
}

/// The per-function ABI slot layout for every `fn` row of `table`.
///
/// # Errors
/// Refuses a `fn` row of `table` that does not carry exactly a symbol, a hash,
/// and a name.
pub fn state_map(core: &Core, table: &str) -> Result<String, String> {
    let layouts: BTreeMap<String, (usize, String)> = core
        .fns
        .iter()
        .map(|function| {
            let arity = function.params.len();
            (
                super::native_symbol(function.name.as_str()),
                (arity, abi_slots(arity)),
            )
        })
        .collect();

    let mut lines = vec![STATE_MAP_HEADER.to_string()];
    lines.extend(header_rows(table).map(str::to_string));
    lines.push(format!("{SLOT_FORMAT_ROW} {SLOT_FORMAT}"));
    for row in rows(table)? {
        if let Some((arity, slots)) = layouts.get(row.symbol) {
            lines.push(format!(
                "{STATE_ROW} {} {} {} {ARITY_FIELD} {} {SLOTS_FIELD} {}",
                row.symbol, row.def_hash, row.core_name, arity, slots
            ));
        }
    }
    Ok(terminated(lines))
}

fn terminated(lines: Vec<String>) -> String {
    lines.into_iter().map(|line| line + "\n").collect()
}

fn abi_slots(arity: usize) -> String {
    if arity == 0 {
        return EMPTY_SLOTS.to_string();
    }
    let slots = (0..arity)
        .map(|index| format!("arg{index}=%a{index}:word"))
        .collect::<Vec<_>>()
        .join(",");
    format!("abi-word[{slots}]")
}

fn header_rows(table: &str) -> impl Iterator<Item = &str> {
    table
        .lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with(FN_ROW))
}
