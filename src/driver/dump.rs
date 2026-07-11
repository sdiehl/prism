//! The `dump <phase>` surface: one phase dispatch that renders any pipeline
//! artifact (tokens, ast, types, core, the content hashes and shape digests,
//! the tier, captures, the usage summary, native kont tables, llvm/mlir) as
//! text, plus the two helpers only this surface uses. Split out of the driver so
//! `mod.rs` holds the compile/check/build entry points and this module holds
//! their read-only inspection face. Every external path (`prism::dump`,
//! `crate::dump`, `dump_on`) resolves through the re-export in `mod.rs`, so the
//! split is invisible to callers.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use crate::core::fbip::borrow_sigs;
use crate::core::{
    captures, fip_annots, hash_program, insert_rc, pp_core_pretty, reuse, CoreFn, DepGraph, Digest,
    HASH_SCHEME,
};
use crate::error::Error;
use crate::lex::lex;
use crate::parse::parse;
use crate::resolve::{default_roots, Root};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::{show_effects, Checked, Type};
use serde::Serialize;

#[cfg(feature = "mlir")]
use crate::codegen::emit_mlir;
#[cfg(feature = "native")]
use crate::codegen::{emit_llvm_with_native_kont_table, native_kont_state_map};

#[cfg(feature = "native")]
use super::build::compiled;
use super::identity::namespace_root_of;
#[cfg(feature = "native")]
use super::identity::{
    native_kont_table_for_with_rows, native_kont_table_of, NativeKontIdentityRows,
};
use super::report::types_section;
use super::{
    check_on, elaborated, frontend, hash_meta, lowered_core, prelude_fn_names, stdlib_hash,
    strip_prelude, Config, WireKind, NAMESPACE_FORMAT,
};

/// Format tag shared by all three usage-summary projections (`usage-summary`,
/// `usage-summary-md`, `usage-summary-json`). It heads each rendering and versions
/// the columns, so a package can commit any projection the way the tier manifest is
/// committed and a reader can tell which layout it is parsing.
const USAGE_SUMMARY_FORMAT: &str = "prism-usage-summary-v1";
// The canonical cell tokens the usage summary reports for a definition, shared by
// every projection so the three can never disagree. `noalloc`/`discipline` come
// from these fixed sets; the TSV bytes are guarded by tests, so the values are
// part of the output contract and defined once here.
const USAGE_NOALLOC_YES: &str = "yes";
const USAGE_NOALLOC_NO: &str = "no";
const USAGE_DISCIPLINE_NONE: &str = "-";
const USAGE_DISCIPLINE_FBIP: &str = "fbip";
const USAGE_DISCIPLINE_FIP: &str = "fip";
// The usage-summary columns, in order, naming both the TSV/markdown headers and the
// JSON fields.
const USAGE_SUMMARY_COLUMNS: [&str; 5] = ["name", "noalloc", "discipline", "borrow", "row"];

/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump(phase: &str, src: &str) -> Result<String, Error> {
    dump_at(phase, src, Path::new("."))
}

/// Like [`dump`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump_at(phase: &str, src: &str, base: &Path) -> Result<String, Error> {
    dump_on(phase, src, &default_roots(base), &Config::from_env())
}

/// Like [`dump_at`], but against an explicit module search path.
///
/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump_on(phase: &str, src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    match phase {
        "tokens" => {
            let (t, _) = lex(src)?;
            Ok(t.iter()
                .map(|(_, t, _)| format!("{t:?}"))
                .collect::<Vec<_>>()
                .join(" "))
        }
        "ast" => Ok(format!("{:#?}", parse(src)?.program)),
        "types" => Ok(types_section(&check_on(src, roots)?)),
        "core" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            Ok(pp_core_pretty(&strip_prelude(core.0, &prelude_fn_names()?)))
        }
        "core-json" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            Ok(crate::core::core_to_json(&core))
        }
        "core-hash" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let mut names: Vec<&Sym> = hashes.keys().collect();
            names.sort_by_key(|s| s.as_str());
            let mut out = String::new();
            for name in names {
                writeln!(
                    out,
                    "{}  {}",
                    &hashes[name][..crate::core::HASH_PREFIX_HEX],
                    name.as_str()
                )
                .unwrap();
            }
            Ok(out)
        }
        // The native kont reverse-table precursor: the deterministic map a
        // native suspendable build must emit so a saved native frame can name its
        // code by definition hash rather than by a raw function pointer.
        "native-kont-table" => {
            #[cfg(feature = "native")]
            {
                let (program, checked, core) = elaborated(src, roots)?;
                let hashes = hash_program(
                    &core,
                    &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
                );
                native_kont_table_of(&hashes, roots, cfg, NativeKontIdentityRows::Portable)
            }
            #[cfg(not(feature = "native"))]
            {
                Err(Error::CodegenDump(
                    "dump native-kont-table requires the native feature".to_string(),
                ))
            }
        }
        "native-kont-state-map" => {
            #[cfg(feature = "native")]
            {
                let (program, checked, core) = elaborated(src, roots)?;
                let hashes = hash_program(
                    &core,
                    &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
                );
                let table =
                    native_kont_table_of(&hashes, roots, cfg, NativeKontIdentityRows::Portable)?;
                Ok(native_kont_state_map(&core, &table))
            }
            #[cfg(not(feature = "native"))]
            {
                Err(Error::CodegenDump(
                    "dump native-kont-state-map requires the native feature".to_string(),
                ))
            }
        }
        // Structural shape digests of the file's datatypes and effects (prelude
        // included, like `core-hash` shows prelude fns). One line per declaration.
        "shape" => {
            let (program, _, _) = frontend(src, roots, cfg)?;
            let shapes = crate::core::shape_digests(&program.types, &program.effects);
            let mut out = String::new();
            for (name, h) in &shapes {
                writeln!(out, "{}  {name}", &h[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            Ok(out)
        }
        // Structural duplicates: definitions that hash identically are the same
        // behavior under different names (a user `fact` and the prelude
        // `factorial`, say). One line per group of clones, `<hash>  a, b, c`.
        "dupes" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let mut by_hash: BTreeMap<&str, Vec<&Sym>> = BTreeMap::new();
            for (sym, h) in &hashes {
                by_hash.entry(h.as_str()).or_default().push(sym);
            }
            let mut groups: Vec<(&&str, &Vec<&Sym>)> =
                by_hash.iter().filter(|(_, v)| v.len() > 1).collect();
            groups.sort_by_key(|(_, v)| v.iter().map(|s| s.as_str()).min().unwrap_or(""));
            let mut out = String::new();
            for (h, members) in groups {
                let mut names: Vec<&str> = members.iter().map(|s| s.as_str()).collect();
                names.sort_unstable();
                writeln!(
                    out,
                    "{}  {}",
                    &h[..crate::core::HASH_PREFIX_HEX],
                    names.join(", ")
                )
                .unwrap();
            }
            if out.is_empty() {
                out.push_str("no structural duplicates\n");
            }
            Ok(out)
        }
        // The two-layer store shape as a read-only export, wrapped in the one wire
        // envelope: a header of the hash scheme tag, the kind (`def`,
        // this being the store's definition layer), and the contract digest (the
        // namespace's own Merkle root), plus the export layout version and the
        // producing compiler version, so a persisted export is self-describing
        // about its format and its content address from the first bytes. Each
        // definition carries its content hash, the anonymous layer (the direct
        // dependency hashes, names erased, which is what the hash actually commits
        // to), and the metadata layer (the human name and inferred type). Docs and
        // spans belong to the metadata layer too and join it when the on-disk
        // store lands.
        "namespace" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let graph = DepGraph::of(&core);
            let types: BTreeMap<&str, String> = checked
                .decls
                .iter()
                .map(|d| (d.name.as_str(), d.ty.show()))
                .collect();
            let mut names: Vec<&Sym> = hashes.keys().collect();
            names.sort_by_key(|s| s.as_str());
            let entries: Vec<serde_json::Value> = names
                .iter()
                .map(|name| {
                    let mut deps: Vec<&str> = graph
                        .direct_deps(**name)
                        .iter()
                        .filter_map(|d| hashes.get(d).map(Digest::as_str))
                        .collect();
                    deps.sort_unstable();
                    serde_json::json!({
                        "hash": hashes[name],
                        "meta": { "name": name.as_str(), "type": types.get(name.as_str()) },
                        "anon": { "deps": deps },
                    })
                })
                .collect();
            // The one envelope header: scheme tag, kind, contract
            // digest, then the body. This export is the store's `def` layer, so
            // its kind is `def`; its contract digest is the namespace's own root,
            // a Merkle fold over the sorted `name -> content-hash` entries (the
            // same fold `stdlib_hash` uses), so the digest moves under any content
            // change and is checkable before the body is read.
            let contract = namespace_root_of(&program, &checked, &core)?;
            let doc = serde_json::json!({
                "envelope": {
                    "scheme": HASH_SCHEME,
                    "kind": WireKind::Def.tag(),
                    "contract": contract,
                    "format": NAMESPACE_FORMAT,
                    "compiler": env!("CARGO_PKG_VERSION"),
                },
                "defs": entries,
            });
            Ok(serde_json::to_string_pretty(&doc).unwrap_or_default())
        }
        // The whole standard library's fingerprint. Ignores `src`/`roots`: the
        // stdlib is embedded, so the file argument is only a CLI placeholder.
        "stdlib-hash" => {
            let h = stdlib_hash()?;
            let mut out = String::new();
            writeln!(out, "scheme    {}", h.scheme).unwrap();
            writeln!(out, "version   {}", h.version).unwrap();
            writeln!(out, "root      {}", h.root).unwrap();
            let mut defs: Vec<&Sym> = h.defs.keys().collect();
            defs.sort_by_key(|s| s.as_str());
            for name in defs {
                writeln!(
                    out,
                    "def   {}  {}",
                    &h.defs[name][..crate::core::HASH_PREFIX_HEX],
                    name.as_str()
                )
                .unwrap();
            }
            for (name, dg) in &h.shapes {
                writeln!(out, "shape {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            for (name, dg) in &h.classes {
                writeln!(out, "class {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            for (name, dg) in &h.instances {
                writeln!(out, "inst  {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            Ok(out)
        }
        "fbip" => {
            let (program, _, core) = frontend(src, roots, cfg)?;
            let sigs = borrow_sigs(&program);
            Ok(pp_core_pretty(&reuse(&insert_rc(&core, &sigs))))
        }
        "lowered" => {
            let (_, lowered, _, _) = lowered_core(src, roots, cfg)?;
            Ok(pp_core_pretty(&lowered))
        }
        // The effect-lowering tier this program's handlers lower to (`pure`,
        // `evidence`, `state-fusion`, `local-partial`, `selective-free-monad`,
        // `whole-program-free-monad`). A pure cost classification, never
        // observable in output; `tests/perf_gate.rs` pins it per corpus program
        // so a silent fusion-to-free-monad collapse surfaces as a reviewable diff.
        "tier" => {
            let (_, checked, core) = frontend(src, roots, cfg)?;
            Ok(format!(
                "{}\n",
                crate::core::effect_strategy(
                    &core,
                    &checked.ctors,
                    &cfg.flags,
                    &checked.op_grades()
                )?
            ))
        }
        // Closure-capture facts: for each of the program's own lambdas and
        // thunks, the bindings it closes over and the scoped operations it
        // performs, each classified portable / nonportable / unknown for a move
        // across a suspend boundary. Diagnostic only; changes no output.
        "captures" => {
            let (_, checked, core) = elaborated(src, roots)?;
            let prelude = prelude_fn_names()?;
            let user_fns: Vec<&CoreFn> = core
                .fns
                .iter()
                .filter(|f| !prelude.contains(&f.name))
                .collect();
            let code_names: BTreeSet<Sym> = user_fns
                .iter()
                .map(|f| f.name)
                .filter(|n| !crate::names::is_synthesized(n.as_str()))
                .collect();
            let decl_ty: BTreeMap<Sym, Type> = checked
                .decls
                .iter()
                .map(|d| (Sym::new(&d.name), d.ty.clone()))
                .collect();
            Ok(captures::render(&captures::facts(
                &user_fns,
                &code_names,
                &decl_ty,
            )))
        }
        // One row per top-level definition of the usage facts the compiler already
        // holds: the allocation certificate, the fip/fbip discipline, the
        // per-parameter borrow mask, and the effect row, headed by the format and
        // the whole-program lowering tier. Three projections share one row
        // computation so they can never disagree: the TSV machine format (pinned by
        // tests), a human-readable markdown table, and a JSON document. A package
        // can commit any of them the way the tier manifest is committed.
        "usage-summary" => {
            let (rows, tier) = usage_summary_data(src, roots, cfg)?;
            Ok(usage_summary_tsv(&rows, &tier))
        }
        "usage-summary-md" => {
            let (rows, tier) = usage_summary_data(src, roots, cfg)?;
            Ok(usage_summary_md(&rows, &tier))
        }
        "usage-summary-json" => {
            let (rows, tier) = usage_summary_data(src, roots, cfg)?;
            Ok(usage_summary_json(&rows, &tier))
        }
        #[cfg(feature = "native")]
        "llvm" => {
            let (_, core, ctors) = compiled(src, roots, cfg)?;
            let native_kont_table =
                native_kont_table_for_with_rows(src, roots, cfg, NativeKontIdentityRows::Portable)?;
            emit_llvm_with_native_kont_table(
                &core,
                &ctors,
                &native_kont_table,
                cfg.flags.native_kont_frames,
            )
            .map_err(Error::CodegenDump)
        }
        #[cfg(feature = "mlir")]
        "mlir" => {
            let (_, core, ctors) = compiled(src, roots, cfg)?;
            emit_mlir(&core, &ctors).map_err(Error::CodegenDump)
        }
        other => Err(Error::CodegenDump(format!("unknown phase {other}"))),
    }
}

// One row of the usage summary: the facts the compiler already holds for a single
// top-level definition, as canonical string cells shared verbatim by every
// projection so the TSV, markdown, and JSON renderings can never diverge.
struct UsageRow {
    name: String,
    noalloc: &'static str,
    discipline: &'static str,
    borrow: String,
    row: String,
}

// The JSON projection: the format tag and whole-program tier, then the rows as
// objects keyed by the shared column names. Borrowed from the `UsageRow` cells so
// the values are identical to the TSV and markdown projections.
#[derive(Serialize)]
struct UsageSummaryJson<'a> {
    format: &'a str,
    tier: &'a str,
    definitions: Vec<UsageDefJson<'a>>,
}

#[derive(Serialize)]
struct UsageDefJson<'a> {
    name: &'a str,
    noalloc: &'a str,
    discipline: &'a str,
    borrow: &'a str,
    row: &'a str,
}

// The single fact source behind all three usage projections. Elaborates `src`,
// resolves the whole-program lowering tier, and builds the name-sorted rows of the
// facts the compiler already holds: the allocation certificate (`Decl::no_alloc`),
// the fip/fbip discipline (`Decl::fip`), the per-parameter borrow mask
// (`borrow_sigs`), and the checked effect row. Every fact is read from its
// canonical source, none re-derived. Rows are scoped to the program's own
// definitions: the entry file's root module plus every module a `Dir` root
// serves. Definitions pulled from the standard library or a dependency bundle
// are excluded, so a package's committed summary drifts only when the package's
// own source changes, never when an imported library's does.
fn usage_summary_data(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Vec<UsageRow>, String), Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    let tier =
        crate::core::effect_strategy(&core, &checked.ctors, &cfg.flags, &checked.op_grades())?;
    let prelude = prelude_fn_names()?;
    let mut foreign_modules: BTreeMap<String, bool> = BTreeMap::new();
    let mut own: BTreeSet<Sym> = BTreeSet::new();
    for f in &core.fns {
        let name = f.name.as_str();
        if prelude.contains(&f.name) || crate::names::is_synthesized(name) {
            continue;
        }
        let module = crate::names::module_of(name);
        let foreign = if module.is_empty() {
            false
        } else if let Some(&cached) = foreign_modules.get(module) {
            cached
        } else {
            let served = crate::resolve::serving_root(module, roots)?;
            let foreign = !matches!(served, Some(Root::Dir(_)));
            foreign_modules.insert(module.to_string(), foreign);
            foreign
        };
        if !foreign {
            own.insert(f.name);
        }
    }
    Ok((usage_rows(&program, &checked, &own), tier.to_string()))
}

// The shared, name-sorted rows: one per own (non-prelude, non-synthesized)
// definition, each cell read from its canonical source.
fn usage_rows(
    program: &Program<CorePhase>,
    checked: &Checked,
    own: &BTreeSet<Sym>,
) -> Vec<UsageRow> {
    let sigs = borrow_sigs(program);
    let decls: BTreeMap<&str, &crate::syntax::ast::Decl<CorePhase>> =
        program.fns.iter().map(|d| (d.name.as_str(), d)).collect();
    let mut rows: Vec<UsageRow> = Vec::new();
    for info in &checked.decls {
        let name = info.name.as_str();
        if !own.contains(&Sym::new(name)) {
            continue;
        }
        let Some(decl) = decls.get(name) else {
            continue;
        };
        let noalloc = if decl.no_alloc {
            USAGE_NOALLOC_YES
        } else {
            USAGE_NOALLOC_NO
        };
        let discipline = match decl.fip {
            Fip::No => USAGE_DISCIPLINE_NONE,
            Fip::Fbip => USAGE_DISCIPLINE_FBIP,
            Fip::Fip => USAGE_DISCIPLINE_FIP,
        };
        rows.push(UsageRow {
            name: name.to_string(),
            noalloc,
            discipline,
            borrow: borrow_mask(sigs.get(&Sym::new(name))),
            row: show_effects(&info.effects),
        });
    }
    rows.sort_by(|a, b| a.name.cmp(&b.name));
    rows
}

// The TSV projection behind `dump usage-summary`: one tab-separated line per
// definition. The header names the format and the whole-program lowering `tier`;
// tier is a whole-program cost decision, so it heads the table rather than
// repeating on every line. These bytes are guarded by tests; do not reshape them.
fn usage_summary_tsv(rows: &[UsageRow], tier: &str) -> String {
    let mut out = String::new();
    writeln!(out, "# {USAGE_SUMMARY_FORMAT}\ttier={tier}").unwrap();
    writeln!(out, "# {}", USAGE_SUMMARY_COLUMNS.join("\t")).unwrap();
    for r in rows {
        writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}",
            r.name, r.noalloc, r.discipline, r.borrow, r.row
        )
        .unwrap();
    }
    out
}

// The markdown projection behind `dump usage-summary-md`: a title line carrying
// the format id and tier, then a pipe table. Cells are unpadded and single-spaced
// so the bytes are trivially stable, and every cell escapes `|` (an effect row may
// carry a `{X | e}` tail) so the table never breaks.
/// Minimum dash run in a markdown table separator cell; columns narrower than
/// this are padded to it, matching the canonical table layout `dprint fmt`
/// produces so a committed summary is stable under the repo formatter.
const MD_SEPARATOR_MIN: usize = 3;

fn usage_summary_md(rows: &[UsageRow], tier: &str) -> String {
    let cells: Vec<[String; 5]> = rows
        .iter()
        .map(|r| {
            [
                md_cell(&r.name),
                md_cell(r.noalloc),
                md_cell(r.discipline),
                md_cell(&r.borrow),
                md_cell(&r.row),
            ]
        })
        .collect();
    let widths: Vec<usize> = USAGE_SUMMARY_COLUMNS
        .iter()
        .enumerate()
        .map(|(i, header)| {
            cells
                .iter()
                .map(|row| row[i].chars().count())
                .chain([header.chars().count(), MD_SEPARATOR_MIN])
                .max()
                .unwrap_or(MD_SEPARATOR_MIN)
        })
        .collect();
    let line = |fields: &[String]| {
        let padded: Vec<String> = fields
            .iter()
            .zip(&widths)
            .map(|(cell, w)| format!("{cell:<w$}"))
            .collect();
        format!("| {} |", padded.join(" | "))
    };
    let mut out = String::new();
    writeln!(out, "# {USAGE_SUMMARY_FORMAT} (tier={tier})").unwrap();
    writeln!(out).unwrap();
    let headers: Vec<String> = USAGE_SUMMARY_COLUMNS
        .iter()
        .map(|h| (*h).to_string())
        .collect();
    writeln!(out, "{}", line(&headers)).unwrap();
    let seps: Vec<String> = widths.iter().map(|w| "-".repeat(*w)).collect();
    writeln!(out, "{}", line(&seps)).unwrap();
    for row in &cells {
        writeln!(out, "{}", line(row.as_slice())).unwrap();
    }
    out
}

// A markdown table cell: escape `|` so a row-polymorphic effect tail (`{X | e}`)
// cannot break the pipe table.
fn md_cell(s: &str) -> String {
    s.replace('|', "\\|")
}

// The JSON projection behind `dump usage-summary-json`: the shared rows as a serde
// document, pretty-printed deterministically.
fn usage_summary_json(rows: &[UsageRow], tier: &str) -> String {
    let doc = UsageSummaryJson {
        format: USAGE_SUMMARY_FORMAT,
        tier,
        definitions: rows
            .iter()
            .map(|r| UsageDefJson {
                name: &r.name,
                noalloc: r.noalloc,
                discipline: r.discipline,
                borrow: &r.borrow,
                row: &r.row,
            })
            .collect(),
    };
    serde_json::to_string_pretty(&doc).unwrap_or_default()
}

// The compact per-parameter borrow mask: `b` for a borrowed parameter, `-` for
// an owned one, and a lone `-` for a definition that takes no parameters.
fn borrow_mask(sig: Option<&Vec<bool>>) -> String {
    match sig {
        Some(bs) if !bs.is_empty() => bs.iter().map(|&b| if b { 'b' } else { '-' }).collect(),
        _ => "-".to_string(),
    }
}
