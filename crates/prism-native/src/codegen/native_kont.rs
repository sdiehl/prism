//! Native continuation metadata emitted beside LLVM modules.
//!
//! The table is intentionally textual: it must be easy to dump, inspect, and
//! parse from the C runtime without linking Rust code. This module owns the Rust
//! spelling of that wire text so driver dumps, LLVM globals, and tests cannot
//! drift independently.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use prism_common::sym::Sym;
use prism_core::core::{Core, Hashes, HASH_SCHEME};

pub const TABLE_GLOBAL: &str = "prism_native_kont_table";
pub const STATE_MAP_GLOBAL: &str = "prism_native_kont_state_map";
pub const PTRS_GLOBAL: &str = "prism_native_kont_ptrs";
pub const PTRS_LEN_GLOBAL: &str = "prism_native_kont_ptrs_len";
// Mach-O section names are a `__SEGMENT,__section` pair; a bare ELF-style
// name lands in a nameless segment, which Darwin 25 rejects at exec with
// EBADMACHO. The snapshot normalizer maps both spellings to one canonical form.
#[cfg(target_os = "macos")]
pub const TABLE_SECTION: &str = "__DATA,__prism_kont";
#[cfg(not(target_os = "macos"))]
pub const TABLE_SECTION: &str = ".prism_kont";

pub const ENTER_SYMBOL: &str = "prism_native_kont_enter";
pub const ARG_SYMBOL: &str = "prism_native_kont_arg";
pub const TAILCALL_SYMBOL: &str = "prism_native_kont_tailcall";
pub const LEAVE_SYMBOL: &str = "prism_native_kont_leave";

#[cfg(test)]
pub const RUNTIME_SURFACE_SYMBOLS: &[&str] = &[
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
const SLOT_FORMAT: &str = "prism-native-abi-word-v1";
const STATE_ROW: &str = "state";
const ARITY_FIELD: &str = "arity";
const SLOTS_FIELD: &str = "slots";
const EMPTY_SLOTS: &str = "abi-word[]";

pub struct Row<'a> {
    pub symbol: &'a str,
    pub def_hash: &'a str,
    pub core_name: &'a str,
}

pub struct IdentityRow<'a> {
    pub key: &'a str,
    pub value: String,
}

pub fn rows(table: &str) -> impl Iterator<Item = Row<'_>> {
    table.lines().filter_map(|line| {
        let mut parts = line.split_whitespace();
        (parts.next()? == FN_ROW).then(|| Row {
            symbol: parts.next().unwrap_or_default(),
            def_hash: parts.next().unwrap_or_default(),
            core_name: parts.next().unwrap_or_default(),
        })
    })
}

pub fn table(hashes: &Hashes, bundle: &str, identity: &[IdentityRow<'_>]) -> String {
    let mut names: Vec<&Sym> = hashes.keys().collect();
    names.sort_by_key(|s| s.as_str());

    let mut out = String::new();
    writeln!(out, "{SCHEME_ROW}  {HASH_SCHEME}").unwrap();
    writeln!(out, "{BUNDLE_ROW}  {bundle}").unwrap();
    writeln!(out, "{COMPILER_ROW}  {}", env!("CARGO_PKG_VERSION")).unwrap();
    writeln!(out, "{TARGET_ROW}  {}", env!("PRISM_TARGET")).unwrap();
    writeln!(out, "{BACKEND_ROW}  llvm").unwrap();
    for row in identity {
        writeln!(out, "{FLAG_ROW}  {}  {}", row.key, row.value).unwrap();
    }
    for name in names {
        writeln!(
            out,
            "{FN_ROW}      {}  {}  {}",
            super::native_symbol(name.as_str()),
            hashes[name],
            name.as_str()
        )
        .unwrap();
    }
    out
}

pub fn state_map(core: &Core, table: &str) -> String {
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

    let mut out = String::new();
    out.push_str(STATE_MAP_HEADER);
    out.push('\n');
    copy_header_rows(table, &mut out);
    writeln!(out, "{SLOT_FORMAT_ROW} {SLOT_FORMAT}").unwrap();
    for row in rows(table) {
        if let Some((arity, slots)) = layouts.get(row.symbol) {
            writeln!(
                out,
                "{STATE_ROW} {} {} {} {ARITY_FIELD} {} {SLOTS_FIELD} {}",
                row.symbol, row.def_hash, row.core_name, arity, slots
            )
            .unwrap();
        }
    }
    out
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

fn copy_header_rows(table: &str, out: &mut String) {
    for line in table.lines().filter(|line| !line.trim().is_empty()) {
        if !line.starts_with(FN_ROW) {
            out.push_str(line);
            out.push('\n');
        }
    }
}
