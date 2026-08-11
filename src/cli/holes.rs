//! `prism check --at-hole` and `--fill`: typed holes that answer.
//!
//! `--at-hole` reports each typed hole in the input: the expected type, the
//! effect row the hole must satisfy, and the in-scope bindings ranked by type
//! fit. `--fill` additionally rewrites the source in place, but only for a hole
//! whose fit is unambiguous: exactly one in-scope binding whose type exactly
//! matches the expected type. The checker never guesses: no literal is ever
//! synthesized, and a hole with zero or several exact candidates is reported
//! and left untouched.

use std::cmp::Reverse;
use std::fs;
use std::path::Path;

use serde::Serialize;

use crate::cli::{check_input, file_name, is_project, resolve_input, CmdError, CmdResult};
use crate::error::source::line_col;
use crate::error::{Error, HoleBinding, HoleCandidate, HoleReport, SourceMap};
use crate::{check_allow_holes_on_in, check_validated_on_in, Config};

// A rewrite edits one file in place, so a multi-module project input has no
// single file to edit and is declined rather than guessed at.
const PROJECT_FILL_REFUSAL: &str =
    "`--fill` rewrites one source file in place: pass a `.pr` file rather than a project";
// Why a hole was left as written. Each is a hard rule: the compiler fills only
// an in-scope name whose type is exactly the expected type, and only in the
// user's own file.
const NO_EXACT: &str = "no exact candidate";
const AMBIGUOUS: &str = "ambiguous";
const IN_PRELUDE: &str = "hole is in the prepended prelude";
// An unconstrained hole fits every name in scope, so the human list stops after
// a screenful and says how many it withheld. The checker ranks exact fits first,
// so truncation keeps the informative end of the list; `--json` is never capped.
const MAX_SHOWN_CANDIDATES: usize = 12;
const MORE_CANDIDATES_HINT: &str = "--json lists all";

// The fill verdict for one hole. `One` is the only case that ever edits source.
#[derive(Debug, PartialEq, Eq)]
enum Fill<'a> {
    // Exactly one in-scope binding whose type is identical to the expected type.
    One(&'a str),
    // Nothing in scope matches exactly; a rewrite would be a guess.
    NoExact,
    // Several exact fits: choosing one would be a coin flip.
    Ambiguous(Vec<&'a str>),
    // The hole sits in the prepended prelude, which is not the user's file.
    Prelude,
}

impl Fill<'_> {
    // The rendered reason a hole was left alone, or `None` when it is fillable.
    fn note(&self) -> Option<String> {
        match self {
            Self::One(_) => None,
            Self::NoExact => Some(NO_EXACT.to_string()),
            Self::Ambiguous(names) => Some(format!("{AMBIGUOUS}: {}", names.join(", "))),
            Self::Prelude => Some(IN_PRELUDE.to_string()),
        }
    }
}

// One hole as machine-consumable JSON: the checker's own report with spans
// remapped to the user's file and a line:col added. The fill verdict is carried
// whether or not `--fill` ran, because `--fill` applies exactly this verdict:
// the object a query sees is the object a rewrite acts on.
#[derive(Serialize)]
struct HoleJson<'a> {
    name: &'a str,
    file: &'a str,
    line: u32,
    col: u32,
    // Byte offsets into the user's own file (into the full prelude-prefixed
    // source when the hole is inside the prelude, where no user offset exists).
    start: usize,
    end: usize,
    in_prelude: bool,
    expected: &'a str,
    effects: &'a str,
    in_scope: usize,
    bindings: &'a [HoleBinding],
    candidates: &'a [HoleCandidate],
    #[serde(skip_serializing_if = "Option::is_none")]
    fillable_with: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    unfillable_because: Option<String>,
}

// A hole paired with everything derived from it: where it lands in the user's
// file and what, if anything, may replace it.
struct Site<'a> {
    report: &'a HoleReport,
    // `None` for a hole inside the prepended prelude.
    span: Option<(usize, usize)>,
    line: u32,
    col: u32,
    fill: Fill<'a>,
}

// `prism check FILE --at-hole [--fill] [--json]`.
pub fn at_hole_cmd(arg: Option<&Path>, fill: bool, json: bool, cfg: &Config) -> CmdResult {
    let input = check_input(arg)?;
    if fill && is_project(&input) {
        return Err((
            Error::ResolveCommand(PROJECT_FILL_REFUSAL.into()),
            String::new(),
            file_name(&input),
        ));
    }
    let (program, roots, name, _) = resolve_input(&input, cfg)?;
    // Holes are retained as reports; every other type error is raised and
    // rendered exactly as a plain `prism check` renders it.
    let checked = check_allow_holes_on_in(&program, &roots, cfg)
        .map_err(|e| (e, program.clone(), name.clone()))?;
    let map = SourceMap::new(&program);
    let sites = sites(&checked.holes, &map);
    if json {
        emit_json(&sites, &name);
    } else {
        emit_text(&sites, &name);
    }
    if fill {
        apply_fills(&input, &name, &map, &sites, json, cfg)?;
    }
    Ok(())
}

// Pair every hole with its user-file position and fill verdict.
fn sites<'a>(holes: &'a [HoleReport], map: &SourceMap<'_>) -> Vec<Site<'a>> {
    holes
        .iter()
        .map(|report| {
            let span = user_span(report, map.prelude_len());
            let (line, col) = span.map_or_else(
                || line_col(map.full(), report.start),
                |(start, _)| line_col(map.user(), start),
            );
            let fill = span.map_or(Fill::Prelude, |_| fill_of(&report.candidates));
            Site {
                report,
                span,
                line,
                col,
                fill,
            }
        })
        .collect()
}

// A hole's span indexes into the prelude-prefixed source the checker saw. The
// user's own file starts at `prelude_len`; a span below it belongs to the
// prelude and has no position in the file being edited.
fn user_span(report: &HoleReport, prelude_len: usize) -> Option<(usize, usize)> {
    (report.start >= prelude_len).then(|| (report.start - prelude_len, report.end - prelude_len))
}

// The fill rule, and the whole of it: exactly one in-scope binding whose type is
// identical to the expected type. A merely compatible (more general) candidate
// is never chosen, and neither is one of several exact fits.
fn fill_of(candidates: &[HoleCandidate]) -> Fill<'_> {
    let exact: Vec<&str> = candidates
        .iter()
        .filter(|c| c.exact)
        .map(|c| c.name.as_str())
        .collect();
    match exact.as_slice() {
        [] => Fill::NoExact,
        [only] => Fill::One(only),
        _ => Fill::Ambiguous(exact),
    }
}

fn emit_text(sites: &[Site<'_>], name: &str) {
    for site in sites {
        let report = site.report;
        println!("?{} at {name}:{}:{}", report.name, site.line, site.col);
        println!("  expected   {}", report.expected);
        println!("  effects    {}", report.effects);
        println!("  candidates {}", candidate_count(report));
        for candidate in report.candidates.iter().take(MAX_SHOWN_CANDIDATES) {
            let mark = if candidate.exact { " (exact)" } else { "" };
            println!("    {} : {}{mark}", candidate.name, candidate.ty);
        }
        let withheld = withheld_candidates(report);
        if withheld > 0 {
            println!("    ... and {withheld} more ({MORE_CANDIDATES_HINT})");
        }
        println!("  in scope   {} bindings", report.bindings.len());
        if matches!(site.fill, Fill::Prelude) {
            println!("  note       {IN_PRELUDE}");
        }
    }
}

// How many candidates the human list leaves unprinted. The count line above it
// always names the full total, so a truncated list is never mistaken for all of
// them.
const fn withheld_candidates(report: &HoleReport) -> usize {
    report.candidates.len().saturating_sub(MAX_SHOWN_CANDIDATES)
}

fn candidate_count(report: &HoleReport) -> String {
    match report.candidates.len() {
        0 => "none".to_string(),
        n => n.to_string(),
    }
}

fn emit_json(sites: &[Site<'_>], name: &str) {
    let payload: Vec<HoleJson<'_>> = sites.iter().map(|site| site.json(name)).collect();
    let text =
        serde_json::to_string(&payload).expect("hole reports are a closed serializable type");
    println!("{text}");
}

impl Site<'_> {
    fn json<'a>(&'a self, file: &'a str) -> HoleJson<'a> {
        let (start, end) = self.span.unwrap_or((self.report.start, self.report.end));
        let fillable_with = match &self.fill {
            Fill::One(candidate) => Some(*candidate),
            _ => None,
        };
        HoleJson {
            name: &self.report.name,
            file,
            line: self.line,
            col: self.col,
            start,
            end,
            in_prelude: self.span.is_none(),
            expected: &self.report.expected,
            effects: &self.report.effects,
            in_scope: self.report.bindings.len(),
            bindings: &self.report.bindings,
            candidates: &self.report.candidates,
            fillable_with,
            unfillable_because: self.fill.note(),
        }
    }
}

// Rewrite every unambiguously fillable hole in the user's file, then re-check
// what was written. A failed verification restores the original bytes, so the
// command either leaves a file that still checks or leaves it exactly as found.
fn apply_fills(
    input: &Path,
    name: &str,
    map: &SourceMap<'_>,
    sites: &[Site<'_>],
    json: bool,
    cfg: &Config,
) -> CmdResult {
    let mut edits: Vec<(usize, usize, &str)> = sites
        .iter()
        .filter_map(|site| match (site.span, &site.fill) {
            (Some((start, end)), Fill::One(candidate)) => Some((start, end, *candidate)),
            _ => None,
        })
        .collect();
    // Right to left, so an applied edit cannot move a span not yet applied.
    edits.sort_by_key(|(start, _, _)| Reverse(*start));
    report_fills(sites, json);
    if edits.is_empty() {
        return Ok(());
    }
    let original = fs::read(input).map_err(|e| (Error::Io(e), String::new(), name.to_string()))?;
    let mut edited = map.user().to_string();
    for (start, end, candidate) in edits {
        edited.replace_range(start..end, candidate);
    }
    fs::write(input, &edited).map_err(|e| (Error::Io(e), String::new(), name.to_string()))?;
    verify_fills(input, name, sites, cfg).map_err(|failure| {
        // Best-effort restore: the file is put back before the failure is
        // reported, and a restore that itself fails is reported as the I/O error
        // it is rather than silently left as an edited file.
        match fs::write(input, &original) {
            Ok(()) => {
                eprintln!("fill verification failed; {name} restored unchanged");
                failure
            }
            Err(e) => (Error::Io(e), String::new(), name.to_string()),
        }
    })
}

// Verify what was just written. Every hole filled means the file must pass the
// same strict verdict `prism check` gives; a hole left as written is still a
// hole, so the file is held to the hole-tolerant check the query surface runs.
fn verify_fills(
    input: &Path,
    name: &str,
    sites: &[Site<'_>],
    cfg: &Config,
) -> Result<(), CmdError> {
    let (full, roots, _, _) = resolve_input(input, cfg)?;
    let all_filled = sites.iter().all(|site| matches!(site.fill, Fill::One(_)));
    let verdict = if all_filled {
        check_validated_on_in(&full, &roots, cfg).map(|_| ())
    } else {
        check_allow_holes_on_in(&full, &roots, cfg).map(|_| ())
    };
    verdict.map_err(|e| (e, full, name.to_string()))
}

// The per-hole outcome. The JSON payload already carries it on each object, so
// the summary is printed only for the human-readable form.
fn report_fills(sites: &[Site<'_>], json: bool) {
    if json {
        return;
    }
    for site in sites {
        match &site.fill {
            Fill::One(candidate) => println!("filled ?{} -> {candidate}", site.report.name),
            other => {
                let note = other.note().unwrap_or_default();
                println!("left ?{}: {note}", site.report.name);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{fill_of, user_span, Fill, HoleCandidate, HoleReport};

    fn candidate(name: &str, exact: bool) -> HoleCandidate {
        HoleCandidate {
            name: name.to_string(),
            ty: "Int".to_string(),
            exact,
        }
    }

    fn report_with(candidates: Vec<HoleCandidate>) -> HoleReport {
        HoleReport {
            name: "answer".to_string(),
            start: 120,
            end: 127,
            expected: "Int".to_string(),
            effects: "{}".to_string(),
            bindings: Vec::new(),
            candidates,
        }
    }

    #[test]
    fn exactly_one_exact_candidate_fills() {
        let candidates = [candidate("x", true), candidate("f", false)];
        assert_eq!(fill_of(&candidates), Fill::One("x"));
    }

    #[test]
    fn no_exact_candidate_never_fills() {
        let candidates = [candidate("f", false), candidate("g", false)];
        assert_eq!(fill_of(&candidates), Fill::NoExact);
        assert_eq!(fill_of(&[]), Fill::NoExact);
    }

    #[test]
    fn several_exact_candidates_are_ambiguous() {
        let candidates = [candidate("a", true), candidate("b", true)];
        assert_eq!(fill_of(&candidates), Fill::Ambiguous(vec!["a", "b"]));
    }

    #[test]
    fn spans_are_remapped_out_of_the_prelude() {
        let report = report_with(Vec::new());
        assert_eq!(user_span(&report, 100), Some((20, 27)));
        assert_eq!(user_span(&report, 130), None);
    }
}
