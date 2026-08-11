//! Rust-authoritative bootstrap shadow checking.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::{file_name, resolve_input, CmdError, CmdResult};
use crate::error::Error;
use crate::{dump_on, interpret_io_on_with_args, with_prelude, Config, OptLevel, Root};

const REPORT_SCHEMA: &str = "prism-bootstrap-check-v1";
const SHADOW_NAME: &str = "prism-t1";
const AUTHORITY: &str = "rust";
const STATUS_PARITY: &str = "parity";
const STATUS_DISAGREEMENT: &str = "disagreement";
const PROTOCOL_VERSION: &str = "1";
const RECORD_HEADER: &str = "BOOTSTRAP";
const RECORD_COVERAGE: &str = "COVERAGE";
const RECORD_UNSUPPORTED: &str = "UNSUPPORTED";
const RECORD_FACT: &str = "FACT";
const RECORD_DIFF: &str = "DIFF";
const RECORD_ERROR: &str = "ERROR";
const DIFF_NONE: &str = "NONE";
const DIFF_AT: &str = "AT";
const DIFF_LEFT_END: &str = "LEFT_END";
const DIFF_RIGHT_END: &str = "RIGHT_END";
const PERCENT_SCALE: f64 = 100.0;
const CHECKER_SRC: &str = include_str!("../../packages/tc/src/Bootstrap.pr");
const TC_SRC: &str = include_str!("../../packages/tc/src/Tc.pr");

#[derive(Deserialize)]
struct RustFacts {
    decls: Vec<RustDecl>,
}

#[derive(Deserialize)]
struct RustDecl {
    name: String,
    scheme: String,
}

#[derive(Debug, Serialize)]
struct BootstrapReport {
    schema: &'static str,
    authority: &'static str,
    shadow: &'static str,
    status: &'static str,
    source: String,
    coverage: Coverage,
    unsupported: Vec<Unsupported>,
    facts: Vec<FactReport>,
    first_divergence: Option<Divergence>,
}

#[derive(Debug, Serialize)]
struct Coverage {
    supported_nodes: u32,
    total_nodes: u32,
    percent: f64,
}

#[derive(Debug, Serialize)]
struct Unsupported {
    function: String,
    kind: String,
    span: [usize; 2],
    nodes: u32,
    reason: String,
}

#[derive(Debug, Serialize)]
struct ShadowFact {
    name: String,
    scheme: String,
}

#[derive(Debug, Serialize)]
struct FactReport {
    name: String,
    rust: Option<String>,
    prism: String,
    agrees: bool,
}

#[derive(Debug, Serialize)]
struct Divergence {
    index: usize,
    kind: String,
    rust: Option<String>,
    prism: Option<String>,
}

#[derive(Default)]
struct Protocol {
    supported_nodes: u32,
    total_nodes: u32,
    unsupported: Vec<Unsupported>,
    facts: Vec<ShadowFact>,
    first: Option<Divergence>,
}

/// Run the pure Prism T1 checker as evidence after Rust has accepted `file`.
///
/// A disagreement is report-only. This command returns failure only when the
/// authoritative Rust check or the workbench machinery itself cannot run.
pub fn check_cmd(file: &Path, json: bool, cfg: &Config) -> CmdResult {
    let (src, mut roots, name, _out) = resolve_input(file, cfg)?;

    // These dumps all pass through the normal Rust checker. If it refuses, the
    // command stops here: the shadow never grants or denies compilation.
    let tc_input = dump_on("tc-input", &src, &roots, cfg)
        .map_err(|error| (error, src.clone(), name.clone()))?;
    let resolved = dump_on("resolved-syntax", &src, &roots, cfg)
        .map_err(|error| (error, src.clone(), name.clone()))?;
    let surface = dump_on("surface-syntax", &src, &roots, cfg)
        .map_err(|error| (error, src.clone(), name.clone()))?;
    let facts_text = dump_on("tc-facts", &src, &roots, cfg)
        .map_err(|error| (error, src.clone(), name.clone()))?;
    let rust_facts: RustFacts = serde_json::from_str(&facts_text).map_err(|error| {
        command_error(
            format!("invalid Rust tc-facts artifact: {error}"),
            &src,
            &name,
        )
    })?;

    let oracle = rust_facts
        .decls
        .iter()
        .map(|decl| format!("{} :: {}", decl.name, canonical_scheme(&decl.scheme)))
        .collect::<Vec<_>>()
        .join("\n");

    let mut modules = BTreeMap::new();
    modules.insert("Tc".to_owned(), TC_SRC.to_owned());
    roots.push(Root::source_bundle("bootstrap checker".into(), modules));

    let mut output = Vec::new();
    // The checker is an interpreter oracle. Core optimization cannot improve
    // its evidence and is disproportionately expensive for the checker.
    let mut shadow_cfg = cfg.clone();
    shadow_cfg.flags.opt_level = OptLevel::O0;
    shadow_cfg.passes = None;
    shadow_cfg.timing = None;
    interpret_io_on_with_args(
        &with_prelude(CHECKER_SRC),
        &roots,
        &mut output,
        &mut &b""[..],
        &shadow_cfg,
        vec![tc_input, resolved, surface, oracle],
    )
    .map_err(|error| {
        command_error(
            format!("Prism T1 shadow failed to run: {error}"),
            &src,
            &name,
        )
    })?;
    let protocol_text = String::from_utf8(output).map_err(|error| {
        command_error(
            format!("Prism T1 shadow emitted non-UTF-8 output: {error}"),
            &src,
            &name,
        )
    })?;
    let protocol =
        parse_protocol(&protocol_text).map_err(|message| command_error(message, &src, &name))?;

    let rust_by_name: HashMap<_, _> = rust_facts
        .decls
        .into_iter()
        .map(|decl| (decl.name, canonical_scheme(&decl.scheme)))
        .collect();
    let fact_reports = protocol
        .facts
        .into_iter()
        .map(|fact| {
            let rust = rust_by_name.get(&fact.name).cloned();
            let agrees = rust.as_deref() == Some(fact.scheme.as_str());
            FactReport {
                name: fact.name,
                rust,
                prism: fact.scheme,
                agrees,
            }
        })
        .collect();
    let percent = if protocol.total_nodes == 0 {
        PERCENT_SCALE
    } else {
        f64::from(protocol.supported_nodes) * PERCENT_SCALE / f64::from(protocol.total_nodes)
    };
    let report = BootstrapReport {
        schema: REPORT_SCHEMA,
        authority: AUTHORITY,
        shadow: SHADOW_NAME,
        status: if protocol.first.is_none() {
            STATUS_PARITY
        } else {
            STATUS_DISAGREEMENT
        },
        source: file_name(file),
        coverage: Coverage {
            supported_nodes: protocol.supported_nodes,
            total_nodes: protocol.total_nodes,
            percent,
        },
        unsupported: protocol.unsupported,
        facts: fact_reports,
        first_divergence: protocol.first,
    };

    if json {
        let rendered = serde_json::to_string_pretty(&report).map_err(|error| {
            command_error(
                format!("could not encode bootstrap report: {error}"),
                &src,
                &name,
            )
        })?;
        println!("{rendered}");
    } else {
        render_text(&report);
    }
    Ok(())
}

fn command_error(message: String, src: &str, name: &str) -> CmdError {
    (
        Error::ResolveCommand(message),
        src.to_owned(),
        name.to_owned(),
    )
}

fn parse_protocol(text: &str) -> Result<Protocol, String> {
    let mut report = Protocol::default();
    let mut saw_header = false;
    let mut saw_coverage = false;
    let mut saw_diff = false;
    for line in text.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        match fields.as_slice() {
            [RECORD_HEADER, PROTOCOL_VERSION] if !saw_header => saw_header = true,
            [RECORD_COVERAGE, supported, total] if !saw_coverage => {
                saw_coverage = true;
                report.supported_nodes = parse_u32(supported, "supported node count")?;
                report.total_nodes = parse_u32(total, "total node count")?;
            }
            [RECORD_UNSUPPORTED, function, kind, lo, hi, nodes, reason] => {
                report.unsupported.push(Unsupported {
                    function: (*function).to_owned(),
                    kind: (*kind).to_owned(),
                    span: [
                        parse_usize(lo, "unsupported span start")?,
                        parse_usize(hi, "unsupported span end")?,
                    ],
                    nodes: parse_u32(nodes, "unsupported node count")?,
                    reason: (*reason).to_owned(),
                });
            }
            [RECORD_FACT, name, scheme] => report.facts.push(ShadowFact {
                name: (*name).to_owned(),
                scheme: (*scheme).to_owned(),
            }),
            [RECORD_DIFF, DIFF_NONE] if !saw_diff => saw_diff = true,
            [RECORD_DIFF, kind, index, rust, prism]
                if !saw_diff && matches!(*kind, DIFF_AT | DIFF_LEFT_END | DIFF_RIGHT_END) =>
            {
                saw_diff = true;
                report.first = Some(Divergence {
                    index: parse_usize(index, "divergence index")?,
                    kind: kind.to_ascii_lowercase().replace('_', "-"),
                    rust: (!rust.is_empty()).then(|| (*rust).to_owned()),
                    prism: (!prism.is_empty()).then(|| (*prism).to_owned()),
                });
            }
            [RECORD_ERROR, message] => {
                return Err(format!("Prism T1 artifact decode failed: {message}"));
            }
            [""] => {}
            _ => return Err(format!("invalid Prism T1 protocol line: {line}")),
        }
    }
    if !saw_header || !saw_coverage || !saw_diff {
        return Err("incomplete Prism T1 protocol".into());
    }
    if report.supported_nodes > report.total_nodes {
        return Err(format!(
            "invalid Prism T1 coverage: {} supported nodes exceeds {} total nodes",
            report.supported_nodes, report.total_nodes
        ));
    }
    Ok(report)
}

fn parse_usize(text: &str, label: &str) -> Result<usize, String> {
    text.parse()
        .map_err(|_| format!("invalid {label} in Prism T1 protocol: {text}"))
}

fn parse_u32(text: &str, label: &str) -> Result<u32, String> {
    text.parse()
        .map_err(|_| format!("invalid {label} in Prism T1 protocol: {text}"))
}

fn render_text(report: &BootstrapReport) {
    println!("Rust check: accepted (authoritative)");
    println!("Prism T1 shadow: {}", report.status);
    println!(
        "Coverage: {}/{} nodes ({:.1}%)",
        report.coverage.supported_nodes, report.coverage.total_nodes, report.coverage.percent
    );
    for row in &report.unsupported {
        println!(
            "  coverage {}: {} at {}..{} ({})",
            row.function, row.kind, row.span[0], row.span[1], row.reason
        );
    }
    if let Some(first) = &report.first_divergence {
        println!("First divergent fact: {} ({})", first.index, first.kind);
        println!("  Rust: {}", first.rust.as_deref().unwrap_or("<ended>"));
        println!("  Prism: {}", first.prism.as_deref().unwrap_or("<ended>"));
        println!("Shadow evidence only; Rust acceptance is unchanged.");
    }
}

// Canonicalize only the binders introduced by a leading forall. The rest of
// Rust's stable type spelling is already the spelling the T1 checker emits.
fn canonical_scheme(scheme: &str) -> String {
    let Some(rest) = scheme.strip_prefix("forall ") else {
        return scheme.to_owned();
    };
    let Some((binders, body)) = rest.split_once(". ") else {
        return scheme.to_owned();
    };
    let names: Vec<_> = binders.split_whitespace().collect();
    let replacements: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(index, name)| (*name, format!("${index}")))
        .collect();
    let mut normalized = String::with_capacity(body.len());
    let mut token = String::new();
    let flush = |token: &mut String, out: &mut String| {
        if token.is_empty() {
            return;
        }
        if let Some(replacement) = replacements.get(token.as_str()) {
            out.push_str(replacement);
        } else {
            out.push_str(token);
        }
        token.clear();
    };
    for ch in body.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            token.push(ch);
        } else {
            flush(&mut token, &mut normalized);
            normalized.push(ch);
        }
    }
    flush(&mut token, &mut normalized);
    let canonical_binders = (0..names.len())
        .map(|index| format!("${index}"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("forall {canonical_binders}. {normalized}")
}

#[cfg(test)]
mod tests {
    use super::{canonical_scheme, parse_protocol};

    #[test]
    fn canonicalizes_forall_binders_without_touching_names() {
        assert_eq!(
            canonical_scheme("forall a b. (a, Maybe(b)) -> a"),
            "forall $0 $1. ($0, Maybe($1)) -> $0"
        );
        assert_eq!(canonical_scheme("(Int) -> Bool"), "(Int) -> Bool");
    }

    #[test]
    fn protocol_requires_and_decodes_every_singleton_record() {
        let protocol = parse_protocol(
            "BOOTSTRAP\t1\nCOVERAGE\t7\t9\nFACT\tmain\tInt\nDIFF\tAT\t2\tInt\tBool\n",
        )
        .expect("complete protocol");
        assert_eq!(protocol.supported_nodes, 7);
        assert_eq!(protocol.total_nodes, 9);
        assert_eq!(protocol.facts.len(), 1);
        let first = protocol.first.expect("divergence");
        assert_eq!(first.index, 2);
        assert_eq!(first.kind, "at");
    }

    #[test]
    fn protocol_rejects_missing_or_duplicate_singleton_records() {
        let missing_coverage = "BOOTSTRAP\t1\nDIFF\tNONE\n";
        assert!(parse_protocol(missing_coverage).is_err());

        let duplicate_diff = "BOOTSTRAP\t1\nCOVERAGE\t1\t1\nDIFF\tNONE\nDIFF\tNONE\n";
        assert!(parse_protocol(duplicate_diff).is_err());

        let impossible_coverage = "BOOTSTRAP\t1\nCOVERAGE\t2\t1\nDIFF\tNONE\n";
        assert!(parse_protocol(impossible_coverage).is_err());
    }
}
