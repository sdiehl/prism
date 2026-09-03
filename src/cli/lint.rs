//! `prism lint`: judge source files against the house style rules.
//!
//! The Rust front end parses each target and produces its surface-syntax
//! artifact; the rules themselves live in the Prism `lint` package, which runs
//! interpreted in one session over every document and reports findings on a
//! tab-separated line protocol. This module walks the targets, hosts the
//! session, and renders the report.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::{glob_pr, resolve_input, tool_package_source, CmdError, CmdResult};
use crate::error::Error;
use crate::{dump_on, interpret_io_on_with_args, with_prelude, Config, OptLevel, Root};

const REPORT_SCHEMA: &str = "prism-lint-v1";
const PROTOCOL_VERSION: &str = "1";
const RECORD_HEADER: &str = "LINT";
const RECORD_SUPPRESSED: &str = "SUPPRESSED";
const RECORD_FINDING: &str = "FINDING";
const RECORD_ERROR: &str = "ERROR";
const SURFACE_PHASE: &str = "surface-syntax";
const NAMESPACE_PHASE: &str = "namespace";
// The ambient namespace is dumped against a stub program whose own entry
// point is not a known name.
const NAMESPACE_PROBE: &str = "let main = 0\n";
const ENTRY_NAME: &str = "main";
const BUNDLE_LABEL: &str = "lint rules";
const TOOL_PACKAGE: &str = "lint";
const ENTRY_MODULE: &str = "Lint";
const LINT_SRC: &str = include_str!("../../packages/lint/src/Lint.pr");
const RULES_SRC: &str = include_str!("../../packages/lint/src/Rules.pr");
const FINDINGS_SRC: &str = include_str!("../../packages/lint/src/Findings.pr");
const PRAGMA_SRC: &str = include_str!("../../packages/lint/src/Pragma.pr");
const LIMITS_SRC: &str = include_str!("../../packages/lint/src/Limits.pr");
/// The modules the entry point imports, each with the copy compiled into this
/// binary. One home for the family: adding a rule module is one line here.
const RULE_MODULES: &[(&str, &str)] = &[
    ("Rules", RULES_SRC),
    ("Findings", FINDINGS_SRC),
    ("Pragma", PRAGMA_SRC),
    ("Limits", LIMITS_SRC),
];

#[derive(Deserialize)]
struct Namespace {
    defs: Vec<NamespaceDef>,
}

#[derive(Deserialize)]
struct NamespaceDef {
    meta: NamespaceMeta,
}

#[derive(Deserialize)]
struct NamespaceMeta {
    name: String,
}

#[derive(Serialize)]
struct Finding {
    code: String,
    path: String,
    line: usize,
    col: usize,
    span: [usize; 2],
    message: String,
}

#[derive(Serialize)]
struct LintReport {
    schema: &'static str,
    files: usize,
    suppressed: usize,
    findings: Vec<Finding>,
}

/// Judge `paths` against the house style rules.
///
/// Paths are files, or directories walked for `.pr` files. Findings fail the
/// exit code unless `advisory` is set; suppressions via `-- lint: allow(..)`
/// pragmas are counted, never silent.
pub fn lint_cmd(paths: &[PathBuf], json: bool, advisory: bool, cfg: &Config) -> CmdResult {
    let targets = collect_targets(paths);
    if targets.is_empty() {
        println!("no .pr files to lint");
        return Ok(());
    }

    let std_roots = vec![Root::Embedded(crate::stdlib::STDLIB)];
    let namespace_text = dump_on(
        NAMESPACE_PHASE,
        &with_prelude(NAMESPACE_PROBE),
        &std_roots,
        cfg,
    )
    .map_err(|e| (e, String::new(), NAMESPACE_PHASE.to_owned()))?;
    let known = known_names(&namespace_text).map_err(|m| lint_error(m, ""))?;

    // Rust parses every target up front; the package only ever sees decoded
    // surface artifacts. Explicitly named files must parse, while files
    // reached by walking a directory are skipped with a notice, so one
    // unparseable fixture cannot fail a whole-tree run.
    let mut documents = Vec::new();
    for (path, strict) in &targets {
        let (src, roots, name, _out) = resolve_input(path, cfg)?;
        match dump_on(SURFACE_PHASE, &src, &roots, cfg) {
            Ok(surface) => documents.push((surface, path.display().to_string())),
            Err(e) if *strict => return Err((e, src, name)),
            Err(_) => eprintln!("{}: skipped (does not parse)", path.display()),
        }
    }

    let mut args = vec![known.join("\n"), documents.len().to_string()];
    for (surface, path) in documents {
        args.push(surface);
        args.push(path);
    }
    let files = (args.len() - 2) / 2;

    let rules = tool_package_source(TOOL_PACKAGE, ENTRY_MODULE, LINT_SRC, cfg)
        .map_err(|e| lint_error(e.to_string(), ""))?;
    let mut modules = BTreeMap::new();
    for (module, embedded) in RULE_MODULES {
        let source = tool_package_source(TOOL_PACKAGE, module, embedded, cfg)
            .map_err(|e| lint_error(e.to_string(), ""))?;
        modules.insert((*module).to_owned(), source);
    }
    let roots = vec![
        Root::source_bundle(BUNDLE_LABEL.into(), modules),
        Root::Embedded(crate::stdlib::STDLIB),
    ];

    // The rules are an interpreter oracle over already-parsed syntax; Core
    // optimization cannot improve their judgment and is disproportionately
    // expensive for a lint pass.
    let mut shadow_cfg = cfg.clone().use_level(OptLevel::O0);
    shadow_cfg.set_timing(None);
    let mut output = Vec::new();
    interpret_io_on_with_args(
        &with_prelude(&rules),
        &roots,
        &mut output,
        &mut &b""[..],
        &shadow_cfg,
        args,
    )
    .map_err(|e| lint_error(format!("lint rules failed to run: {e}"), ""))?;
    let protocol_text = String::from_utf8(output)
        .map_err(|e| lint_error(format!("lint rules emitted non-UTF-8 output: {e}"), ""))?;
    let (findings, suppressed) = parse_protocol(&protocol_text).map_err(|m| lint_error(m, ""))?;

    let report = LintReport {
        schema: REPORT_SCHEMA,
        files,
        suppressed,
        findings,
    };
    if json {
        let rendered = serde_json::to_string_pretty(&report)
            .map_err(|e| lint_error(format!("could not encode lint report: {e}"), ""))?;
        println!("{rendered}");
    } else {
        render_text(&report);
    }
    if !advisory && !report.findings.is_empty() {
        return Err(lint_error(
            format!("{} lint findings", report.findings.len()),
            "",
        ));
    }
    Ok(())
}

fn lint_error(message: String, src: &str) -> CmdError {
    (
        Error::ResolveCommand(message),
        src.to_owned(),
        String::new(),
    )
}

// Files to lint: named files as strict targets, directories walked for `.pr`
// files as lenient ones, the current directory when nothing is named.
fn collect_targets(paths: &[PathBuf]) -> Vec<(PathBuf, bool)> {
    let mut targets: Vec<(PathBuf, bool)> = Vec::new();
    if paths.is_empty() {
        targets.extend(glob_pr(Path::new(".")).into_iter().map(|p| (p, false)));
    } else {
        for p in paths {
            if p.is_dir() {
                targets.extend(glob_pr(p).into_iter().map(|q| (q, false)));
            } else {
                targets.push((p.clone(), true));
            }
        }
    }
    targets.sort();
    targets.dedup();
    targets
}

// The flat ambient namespace: every undotted definition name from the
// namespace artifact. Top-level user functions share this namespace with the
// prelude, so any of these names silently captures.
fn known_names(namespace_text: &str) -> Result<Vec<String>, String> {
    let namespace: Namespace = serde_json::from_str(namespace_text)
        .map_err(|e| format!("invalid namespace artifact: {e}"))?;
    let mut known: Vec<String> = namespace
        .defs
        .into_iter()
        .map(|def| def.meta.name)
        .filter(|name| !name.contains('.') && name != ENTRY_NAME)
        .collect();
    known.sort();
    known.dedup();
    Ok(known)
}

fn parse_protocol(text: &str) -> Result<(Vec<Finding>, usize), String> {
    let mut findings = Vec::new();
    let mut suppressed = 0usize;
    let mut saw_header = false;
    for line in text.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        match fields.as_slice() {
            [RECORD_HEADER, PROTOCOL_VERSION] if !saw_header => saw_header = true,
            [RECORD_SUPPRESSED, _path, count] => {
                suppressed += parse_number(count, "suppressed count")?;
            }
            [RECORD_FINDING, code, path, line_no, col, lo, hi, message] => {
                findings.push(Finding {
                    code: (*code).to_owned(),
                    path: (*path).to_owned(),
                    line: parse_number(line_no, "finding line")?,
                    col: parse_number(col, "finding column")?,
                    span: [
                        parse_number(lo, "finding span start")?,
                        parse_number(hi, "finding span end")?,
                    ],
                    message: (*message).to_owned(),
                });
            }
            [RECORD_ERROR, path, message] => {
                return Err(format!("lint artifact decode failed for {path}: {message}"));
            }
            [""] => {}
            _ => return Err(format!("invalid lint protocol line: {line}")),
        }
    }
    if !saw_header {
        return Err("incomplete lint protocol".into());
    }
    Ok((findings, suppressed))
}

fn parse_number(text: &str, label: &str) -> Result<usize, String> {
    text.parse()
        .map_err(|_| format!("invalid {label} in lint protocol: {text}"))
}

fn render_text(report: &LintReport) {
    for f in &report.findings {
        println!(
            "{}:{}:{}: [{}] {}",
            f.path, f.line, f.col, f.code, f.message
        );
    }
    println!(
        "{} files, {} findings, {} suppressed",
        report.files,
        report.findings.len(),
        report.suppressed
    );
}

#[cfg(test)]
mod tests {
    use super::{known_names, parse_protocol, PRAGMA_SRC};
    use crate::docs::extract::PRAGMA_MARKER;

    /// Both pragma spellings the rule package declares carry the marker the doc
    /// generator strips, so a suppression can never reach a published page.
    #[test]
    fn pragma_marker_matches_the_rule_package() {
        for form in ["-- lint: allow(", "-- lint: allow-file("] {
            assert!(
                PRAGMA_SRC.contains(&format!("\"{form}\"")),
                "`Pragma.pr` no longer declares `{form}`"
            );
            assert!(
                form.contains(PRAGMA_MARKER),
                "`{form}` does not carry the marker the doc generator strips"
            );
        }
    }

    #[test]
    fn protocol_decodes_findings_and_sums_suppressions() {
        let text = "LINT\t1\nSUPPRESSED\ta.pr\t2\nFINDING\tL0101\ta.pr\t3\t5\t40\t60\tdeep\nSUPPRESSED\tb.pr\t1\n";
        let (findings, suppressed) = parse_protocol(text).expect("complete protocol");
        assert_eq!(suppressed, 3);
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].code, "L0101");
        assert_eq!(findings[0].span, [40, 60]);
    }

    #[test]
    fn protocol_rejects_missing_header_and_decode_errors() {
        assert!(parse_protocol("SUPPRESSED\ta.pr\t0\n").is_err());
        assert!(parse_protocol("LINT\t1\nERROR\ta.pr\tbad schema\n").is_err());
    }

    #[test]
    fn known_names_keeps_only_the_flat_namespace() {
        let text = r#"{"defs": [
            {"meta": {"name": "map"}},
            {"meta": {"name": "Data.List.map"}},
            {"meta": {"name": "main"}},
            {"meta": {"name": "map"}}
        ]}"#;
        let known = known_names(text).expect("valid namespace");
        assert_eq!(known, vec!["map".to_owned()]);
    }
}
