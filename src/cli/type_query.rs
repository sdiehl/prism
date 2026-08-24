//! Type-directed search and bounded typed-hole synthesis.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use serde::Serialize;

use crate::cli::{check_input, glob_pr, is_project, resolve_input, CmdError, CmdResult};
use crate::driver::stdlib_value_schemes;
use crate::error::source::line_col;
use crate::error::{Error, HoleBinding, HoleReport, SourceMap};
use crate::resolve::Root;
use crate::sym::Sym;
use crate::syntax::ast::Program;
use crate::syntax::reflect::parse_unit;
use crate::tc::{application_params, parse_checked_signature, type_subsumes};
use crate::types::{Checked, Type};
use crate::{
    check_allow_holes_on_in, check_modules_on, check_validated_on_in, with_prelude, Config,
    ModuleInterface,
};

const DEFAULT_SEARCH_LIMIT: usize = 50;
const DEFAULT_SYNTH_DEPTH: usize = 2;
const DEFAULT_SYNTH_LIMIT: usize = 10;
const MAX_SEARCH_LIMIT: usize = 500;
const MAX_SYNTH_DEPTH: usize = 6;
const MAX_SYNTH_LIMIT: usize = 100;
const MAX_APPLICATION_ARITY: usize = 3;
const SYNTH_GENERATION_MULTIPLIER: usize = 64;
const MIN_SYNTH_GENERATION_LIMIT: usize = 256;
const MAX_SYNTH_GENERATION_LIMIT: usize = 10_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
enum SearchSource {
    Project,
    Package,
    Stdlib,
}

impl SearchSource {
    const fn label(self) -> &'static str {
        match self {
            Self::Project => "project",
            Self::Package => "package",
            Self::Stdlib => "stdlib",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct SearchHit {
    name: String,
    ty: String,
    source: SearchSource,
    module: String,
}

#[derive(Clone)]
struct Binding {
    name: String,
    ty: Type,
}

#[derive(Serialize)]
struct SynthCandidate {
    expression: String,
}

#[derive(Serialize)]
struct SynthReport {
    hole: String,
    file: String,
    line: u32,
    col: u32,
    expected: String,
    depth: usize,
    candidates: Vec<SynthCandidate>,
}

/// `prism search TYPE [--in PATH] [--limit N] [--json]`.
pub fn search_cmd(
    query: &str,
    input: Option<&Path>,
    limit: usize,
    json: bool,
    cfg: &Config,
) -> CmdResult {
    bounded("search limit", limit, 1, MAX_SEARCH_LIMIT)?;
    let input = check_input(input)?;
    let (full, roots, name, _) = resolve_input(&input, cfg)?;
    let wanted =
        parse_type("search query", query).map_err(|error| (error, full.clone(), name.clone()))?;
    let mut hits = search_universe(&input, &full, &roots, cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?;
    hits.retain(|hit| {
        parse_type(&hit.name, &hit.ty).is_ok_and(|actual| type_subsumes(&actual, &wanted))
    });
    hits.sort_by(|left, right| {
        (&left.source, &left.module, &left.name, &left.ty).cmp(&(
            &right.source,
            &right.module,
            &right.name,
            &right.ty,
        ))
    });
    hits.dedup();
    hits.truncate(limit);
    if json {
        println!(
            "{}",
            serde_json::to_string(&hits).expect("type-search rows are serializable")
        );
    } else if hits.is_empty() {
        println!("no results for {query}");
    } else {
        for hit in hits {
            println!(
                "{} : {}  [{}:{}]",
                hit.name,
                hit.ty,
                hit.source.label(),
                hit.module
            );
        }
    }
    Ok(())
}

/// `prism synth [FILE] --at-hole NAME [--depth N] [--limit N] [--json]`.
pub fn synth_cmd(
    input: Option<&Path>,
    at_hole: &str,
    depth: usize,
    limit: usize,
    json: bool,
    cfg: &Config,
) -> CmdResult {
    bounded("synthesis depth", depth, 0, MAX_SYNTH_DEPTH)?;
    bounded("synthesis limit", limit, 1, MAX_SYNTH_LIMIT)?;
    let input = check_input(input)?;
    let (full, roots, name, _) = resolve_input(&input, cfg)?;
    let checked = check_allow_holes_on_in(&full, &roots, cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?;
    let map = SourceMap::new(&full);
    let requested = at_hole.strip_prefix('?').unwrap_or(at_hole);
    let holes = checked
        .holes
        .iter()
        .filter(|hole| hole.name == requested)
        .collect::<Vec<_>>();
    if holes.is_empty() {
        return Err((
            Error::ResolveCommand(format!("no typed hole `?{requested}` found")),
            full,
            name,
        ));
    }
    let mut reports = Vec::new();
    for hole in holes {
        let candidates = synthesize_hole(&full, &roots, hole, depth, limit, cfg);
        let (line, col) = if hole.start >= map.prelude_len() {
            line_col(map.user(), hole.start - map.prelude_len())
        } else {
            line_col(map.full(), hole.start)
        };
        reports.push(SynthReport {
            hole: hole.name.clone(),
            file: name.clone(),
            line,
            col,
            expected: hole.expected.clone(),
            depth,
            candidates: candidates
                .into_iter()
                .map(|expression| SynthCandidate { expression })
                .collect(),
        });
    }
    if json {
        println!(
            "{}",
            serde_json::to_string(&reports).expect("synthesis reports are serializable")
        );
    } else {
        for report in reports {
            println!(
                "?{} at {}:{}:{} : {}",
                report.hole, report.file, report.line, report.col, report.expected
            );
            if report.candidates.is_empty() {
                println!("  no candidates within depth {depth}");
            } else {
                for candidate in report.candidates {
                    println!("  {}", candidate.expression);
                }
            }
        }
    }
    Ok(())
}

fn bounded(label: &str, value: usize, min: usize, max: usize) -> Result<(), CmdError> {
    if (min..=max).contains(&value) {
        Ok(())
    } else {
        Err((
            Error::ResolveCommand(format!("{label} must be between {min} and {max}")),
            String::new(),
            label.to_string(),
        ))
    }
}

fn parse_type(name: &str, text: &str) -> Result<Type, Error> {
    parse_checked_signature(name, text)
        .map_err(|error| Error::ResolveCommand(format!("invalid type `{text}`: {error}")))
}

fn search_universe(
    input: &Path,
    full: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<Vec<SearchHit>, Error> {
    let mut hits = Vec::new();
    let map = SourceMap::new(full);
    let entry = parse_unit(map.user())?;
    let origins = module_origins(roots);
    if is_project(input) {
        let actual = check_modules_on(full, roots, cfg)?;
        add_root_hits(&mut hits, &entry, &actual.root);
        let imports = origins
            .keys()
            .map(|module| format!("import {module}"))
            .collect::<Vec<_>>()
            .join("\n");
        // Read `interfaces`, not `modules`: an interface served straight from
        // the durable cache has no checked body and never lands in `modules`,
        // but its exports must still be searchable.
        let interfaces = check_modules_on(&with_prelude(&imports), roots, cfg)?.interfaces;
        for (name, interface) in &interfaces {
            let source = origins.get(name).copied().unwrap_or(SearchSource::Package);
            add_interface_hits(&mut hits, name, source, interface);
        }
    } else {
        let checked = check_validated_on_in(full, roots, cfg)?;
        add_root_hits(&mut hits, &entry, &checked);
        add_dependency_env_hits(&mut hits, &checked, &origins);
    }

    for (module, name, ty) in stdlib_value_schemes()? {
        hits.push(SearchHit {
            module,
            name,
            ty: ty.show(),
            source: SearchSource::Stdlib,
        });
    }
    Ok(hits)
}

fn add_root_hits(hits: &mut Vec<SearchHit>, entry: &Program, checked: &Checked) {
    for decl in &entry.fns {
        if let Some(ty) = checked.env.get(&Sym::from(decl.name.as_str())) {
            hits.push(SearchHit {
                name: decl.name.clone(),
                ty: ty.show(),
                source: SearchSource::Project,
                module: "root".to_string(),
            });
        }
    }
}

fn add_dependency_env_hits(
    hits: &mut Vec<SearchHit>,
    checked: &Checked,
    origins: &BTreeMap<String, SearchSource>,
) {
    for (name, ty) in checked.env.iter() {
        let shown = name.to_string();
        let module = origins
            .keys()
            .filter(|module| shown.starts_with(&format!("{module}.")))
            .max_by_key(|module| module.len());
        let Some(module) = module else {
            continue;
        };
        let source = origins[module];
        if source == SearchSource::Stdlib || shown.contains('@') {
            continue;
        }
        hits.push(SearchHit {
            name: shown,
            ty: ty.show(),
            source,
            module: module.clone(),
        });
    }
}

fn add_interface_hits(
    hits: &mut Vec<SearchHit>,
    module: &str,
    source: SearchSource,
    interface: &ModuleInterface,
) {
    hits.extend(
        interface
            .entries
            .iter()
            .filter(|entry| entry.kind == "value")
            .map(|entry| SearchHit {
                name: entry.name.clone(),
                ty: entry.signature.clone(),
                source,
                module: module.to_string(),
            }),
    );
}

fn module_origins(roots: &[Root]) -> BTreeMap<String, SearchSource> {
    let last = roots.len().saturating_sub(1);
    let mut modules = BTreeMap::new();
    for (index, root) in roots.iter().enumerate() {
        let source = if index == 0 {
            SearchSource::Project
        } else if index == last {
            SearchSource::Stdlib
        } else {
            SearchSource::Package
        };
        for module in root_modules(root) {
            modules.entry(module).or_insert(source);
        }
    }
    modules
}

fn root_modules(root: &Root) -> Vec<String> {
    let modules: Vec<String> = match root {
        Root::Dir(base) => glob_pr(base)
            .into_iter()
            .filter_map(|path| module_path(base, &path))
            .collect(),
        Root::Embedded(table) => table.iter().map(|(name, _)| (*name).to_string()).collect(),
        Root::SourceBundle { modules, .. } => modules.keys().cloned().collect(),
    };
    modules
        .into_iter()
        .filter(|module| valid_module_path(module))
        .collect()
}

fn valid_module_path(module: &str) -> bool {
    module.split('.').all(|part| {
        part.chars()
            .next()
            .is_some_and(|first| first.is_ascii_uppercase())
    })
}

fn module_path(base: &Path, path: &Path) -> Option<String> {
    let relative = path.strip_prefix(base).ok()?;
    let mut no_ext = PathBuf::from(relative);
    no_ext.set_extension("");
    let parts = no_ext
        .components()
        .filter_map(|part| match part {
            Component::Normal(name) => name.to_str().map(str::to_string),
            _ => None,
        })
        .collect::<Vec<_>>();
    (!parts.is_empty()).then(|| parts.join("."))
}

fn synthesize_hole(
    source: &str,
    roots: &[Root],
    hole: &HoleReport,
    depth: usize,
    limit: usize,
    cfg: &Config,
) -> Vec<String> {
    let Ok(expected) = parse_type(&hole.name, &hole.expected) else {
        return Vec::new();
    };
    let map = SourceMap::new(source);
    let entry = parse_unit(map.user()).ok();
    let preferred = entry
        .as_ref()
        .map(|entry| {
            entry
                .fns
                .iter()
                .map(|decl| decl.name.clone())
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    let user_start = hole.start.saturating_sub(map.prelude_len());
    let enclosing = entry.as_ref().and_then(|entry| {
        entry
            .fns
            .iter()
            .find(|decl| decl.body.span.start <= user_start && user_start <= decl.body.span.end)
            .map(|decl| decl.name.as_str())
    });
    let bindings = parsed_bindings(&hole.bindings, &preferred, enclosing);
    let generation_limit = limit
        .saturating_mul(SYNTH_GENERATION_MULTIPLIER)
        .clamp(MIN_SYNTH_GENERATION_LIMIT, MAX_SYNTH_GENERATION_LIMIT);
    let generated = synthesize(&expected, &bindings, depth, generation_limit);
    let mut verified = Vec::new();
    for expression in generated {
        let mut probe = source.to_string();
        if hole.end > probe.len() || hole.start > hole.end {
            break;
        }
        probe.replace_range(hole.start..hole.end, &expression);
        if check_allow_holes_on_in(&probe, roots, cfg).is_ok() {
            verified.push(expression);
            if verified.len() == limit {
                break;
            }
        }
    }
    verified
}

fn parsed_bindings(
    bindings: &[HoleBinding],
    preferred: &BTreeSet<String>,
    enclosing: Option<&str>,
) -> Vec<Binding> {
    let mut parsed = bindings
        .iter()
        // A direct recursive call simply moves the same hole around. Other
        // members of a recursion group remain available.
        .filter(|binding| enclosing != Some(binding.name.as_str()))
        .filter_map(|binding| {
            parse_type(&binding.name, &binding.ty)
                .ok()
                .map(|ty| Binding {
                    name: binding.name.clone(),
                    ty,
                })
        })
        .collect::<Vec<_>>();
    parsed.sort_by(|left, right| {
        (!preferred.contains(&left.name), left.name.as_str())
            .cmp(&(!preferred.contains(&right.name), right.name.as_str()))
    });
    parsed
}

fn synthesize(target: &Type, bindings: &[Binding], depth: usize, limit: usize) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for binding in bindings {
        if type_subsumes(&binding.ty, target) {
            push_candidate(&mut out, &mut seen, binding.name.clone(), limit);
        }
    }
    for literal in literals_for(target) {
        push_candidate(&mut out, &mut seen, literal, limit);
    }
    if depth == 0 || out.len() == limit {
        return out;
    }

    for function in bindings {
        let Some(params) = application_params(&function.ty, target) else {
            continue;
        };
        if params.is_empty() || params.len() > MAX_APPLICATION_ARITY {
            continue;
        }
        let choices = params
            .iter()
            .map(|param| synthesize(param, bindings, depth - 1, limit))
            .collect::<Vec<_>>();
        if choices.iter().any(Vec::is_empty) {
            continue;
        }
        let mut applications = vec![Vec::<String>::new()];
        for arguments in choices {
            let mut next = Vec::new();
            for prefix in &applications {
                for argument in &arguments {
                    let mut row = prefix.clone();
                    row.push(argument.clone());
                    next.push(row);
                    if next.len() >= limit {
                        break;
                    }
                }
                if next.len() >= limit {
                    break;
                }
            }
            applications = next;
        }
        for arguments in applications {
            push_candidate(
                &mut out,
                &mut seen,
                format!("{}({})", function.name, arguments.join(", ")),
                limit,
            );
        }
        if out.len() == limit {
            return out;
        }
    }

    if let Some((params, result)) = function_parts(target) {
        if !params.is_empty() && params.len() <= MAX_APPLICATION_ARITY {
            let names = (0..params.len())
                .map(|i| format!("x{i}"))
                .collect::<Vec<_>>();
            let mut nested = bindings.to_vec();
            nested.extend(
                names
                    .iter()
                    .cloned()
                    .zip(params)
                    .map(|(name, ty)| Binding { name, ty }),
            );
            for body in synthesize(&result, &nested, depth - 1, limit) {
                push_candidate(
                    &mut out,
                    &mut seen,
                    format!("\\({}) -> {body}", names.join(", ")),
                    limit,
                );
            }
        }
    }
    out
}

fn function_parts(ty: &Type) -> Option<(Vec<Type>, Type)> {
    let mut current = ty;
    while let Type::Forall(_, body) | Type::RowForall(_, body) = current {
        current = body;
    }
    match current {
        Type::Fun(params, _effects, result) => Some((params.clone(), (**result).clone())),
        _ => None,
    }
}

fn literals_for(target: &Type) -> Vec<String> {
    [
        (Type::Unit, "()"),
        (Type::Int, "0"),
        (Type::Bool, "false"),
        (Type::Float, "0.0"),
        (Type::Char, "'a'"),
        (Type::Str, "\"\""),
    ]
    .into_iter()
    .filter(|(ty, _)| type_subsumes(ty, target))
    .map(|(_, text)| text.to_string())
    .collect()
}

fn push_candidate(
    out: &mut Vec<String>,
    seen: &mut BTreeSet<String>,
    expression: String,
    limit: usize,
) {
    if out.len() < limit && seen.insert(expression.clone()) {
        out.push(expression);
    }
}

#[must_use]
pub const fn default_search_limit() -> usize {
    DEFAULT_SEARCH_LIMIT
}

#[must_use]
pub const fn default_synth_depth() -> usize {
    DEFAULT_SYNTH_DEPTH
}

#[must_use]
pub const fn default_synth_limit() -> usize {
    DEFAULT_SYNTH_LIMIT
}
