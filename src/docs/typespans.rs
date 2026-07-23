//! Versioned source ranges carrying canonical inferred type-and-effect text.
//!
//! `prism dump typespans` is the canonical producer. Documentation tooltips use
//! the same producer-independent browser payload.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

use crate::error::{Error, SourceMap};
use crate::hir::CheckedHir;
use crate::kw;
use crate::lex::{lex_raw, Token};
use crate::names;
use crate::parse::parse;
use crate::sym::Sym;
use crate::syntax::ast::{
    ClassDecl, Core, DataDecl, Decl, Expr, HandlerArm, Pattern, PatternDecl, Program, StableDecl,
    Sugar, SugarArm, Surface, S,
};
use crate::types::coeffect::CoeffectFact;
use crate::types::ty::Kind;
use crate::types::{Checked, CtorInfo, EffOpInfo, Type};

/// Schema tag for the shared type-span payload.
pub const TYPESPANS_FORMAT: &str = "prism-typespans-v1";

// The wired-in scalar type names (all of kind `Type`). They are `Type`
// variants rather than data declarations, so the type-level hover resolves
// them from this list instead of the checked data map.
const PRIM_TYPES: [&str; 8] = [
    kw::TY_INT,
    kw::TY_I64,
    kw::TY_U64,
    kw::TY_BOOL,
    kw::TY_FLOAT,
    kw::TY_CHAR,
    kw::TY_STRING,
    kw::TY_UNIT,
];

type ByteRange = (usize, usize);
type RangeLink = (ByteRange, ByteRange);

/// Which language level a span's rendering describes.
///
/// Value spans (the default, elided from the payload) show an expression or
/// binder type; type spans show a type constructor's kind; hole spans show a
/// typed hole's inferred type. The consumer styles each level distinctly.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Level {
    #[default]
    Value,
    Typelevel,
    Class,
    Typevar,
    Effect,
    Coeffect,
    Hole,
    PatternVar,
    Logic,
}

impl Level {
    // Serde gate: only non-default levels reach the payload, so existing
    // value-only documents are byte-identical under the same format tag.
    #[allow(clippy::trivially_copy_pass_by_ref)] // serde's skip_serializing_if contract
    const fn is_value(&self) -> bool {
        matches!(self, Self::Value)
    }

    /// The payload/attribute tag for a non-value level, matching the serde
    /// rename; empty for value spans (the default, carried implicitly).
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Value => "",
            Self::Typelevel => "typelevel",
            Self::Class => "class",
            Self::Typevar => "typevar",
            Self::Effect => "effect",
            Self::Coeffect => "coeffect",
            Self::Hole => "hole",
            Self::PatternVar => "patternvar",
            Self::Logic => "logic",
        }
    }
}

/// One pointable surface range and its canonical rendered text.
///
/// The text is an expression/binder type (`Int`, `(Int) -> Int ! {IO}`), a type
/// constructor's kind, or a typed hole's inferred type. A pure span shows its
/// type alone; the `!` row appears only when the row is non-empty.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct TypeSpan {
    pub start: usize,
    pub end: usize,
    #[serde(rename = "type")]
    pub rendered: String,
    #[serde(default, skip_serializing_if = "Level::is_value")]
    pub level: Level,
}

/// The versioned, source-ordered type-span document.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct TypeSpans {
    pub format: String,
    pub spans: Vec<TypeSpan>,
}

impl TypeSpans {
    /// Serialize with stable indentation and field order.
    ///
    /// # Errors
    /// Fails only if the derived JSON serializer rejects the document.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Decode and validate a shared type-span payload.
    ///
    /// # Errors
    /// Refuses an unknown format, empty/duplicate ranges, or non-canonical row
    /// order. Crossing ranges are also refused: surface expression ranges may
    /// nest or be disjoint, never overlap partially.
    pub fn from_json(text: &str) -> Result<Self, String> {
        let doc: Self = serde_json::from_str(text).map_err(|error| error.to_string())?;
        if doc.format != TYPESPANS_FORMAT {
            return Err(format!(
                "unsupported typespans format `{}` (expected `{TYPESPANS_FORMAT}`)",
                doc.format
            ));
        }
        let mut prior: Option<&TypeSpan> = None;
        let mut stack: Vec<&TypeSpan> = Vec::new();
        for span in &doc.spans {
            if span.start >= span.end {
                return Err(format!("empty typespan {}..{}", span.start, span.end));
            }
            if let Some(prev) = prior {
                if (prev.start, prev.end) == (span.start, span.end) {
                    return Err(format!("duplicate typespan {}..{}", span.start, span.end));
                }
                let ordered = (prev.start, std::cmp::Reverse(prev.end), &prev.rendered)
                    < (span.start, std::cmp::Reverse(span.end), &span.rendered);
                if !ordered {
                    return Err("typespans are not in canonical source order".into());
                }
            }
            while stack.last().is_some_and(|open| span.start >= open.end) {
                stack.pop();
            }
            if let Some(open) = stack.last() {
                if span.end > open.end {
                    return Err(format!(
                        "crossing typespans {}..{} and {}..{}",
                        open.start, open.end, span.start, span.end
                    ));
                }
            }
            stack.push(span);
            prior = Some(span);
        }
        Ok(doc)
    }
}

fn collect_surface_expr(e: &S<Expr>, spans: &mut BTreeSet<(usize, usize)>) {
    if !e.synth && e.span.start < e.span.end {
        spans.insert((e.span.start, e.span.end));
    }
    e.node
        .each_child(&mut |child| collect_surface_expr(child, spans));
}

struct SurfaceNodes {
    root_names: BTreeSet<String>,
    ranges: BTreeSet<(usize, usize)>,
    binders: Vec<SurfaceBinder>,
    type_decls: Vec<TypeDeclSpans>,
    class_decls: Vec<ClassDeclSpans>,
    // Candidate identifiers in fn/method headers outside default expressions:
    // a capitalized one is a type-constructor or class reference, a lowercase
    // one a type-variable reference in an annotation or `given` clause. All are
    // resolved against the checked maps (and the declaration's scheme) by the
    // caller; unresolved candidates simply produce no span.
    header_refs: Vec<HeaderRef>,
    // `let`/`var`/`where` binder ranges, each paired with its bound
    // expression's range (whose checked rendering is the binder's type).
    let_binders: Vec<((usize, usize), (usize, usize))>,
    // Effect declarations: the declared name's range, and each operation
    // binder's range with its name (the op signature and grade come from the
    // checked op table).
    effect_names: Vec<((usize, usize), String)>,
    effect_ops: Vec<((usize, usize), String)>,
    // Handler and catch left-hand sides are binders rather than expression
    // nodes, so their pointable ranges come from the surface tokens. The
    // semantic join happens later against checked operation and in-arm facts.
    effect_heads: Vec<EffectHeadSpan>,
    clause_binders: Vec<ClauseBinderSpan>,
    pattern_decls: Vec<PatternDeclSpans>,
    pattern_heads: Vec<(ByteRange, String)>,
    stable_decls: Vec<StableDeclSpans>,
    lambda_binders: Vec<LambdaBinderSpan>,
}

struct EffectHeadSpan {
    range: ByteRange,
    lookup: String,
    display: String,
}

struct ClauseBinderSpan {
    range: ByteRange,
    name: String,
    body: ByteRange,
    source: ClauseBinderSource,
}

enum ClauseBinderSource {
    OperationParam { operation: String, index: usize },
    Continuation { operation: String },
    Return,
    CatchParam { operation: String, index: usize },
    Value,
}

struct ClauseHead {
    range: ByteRange,
    binders: Vec<ByteRange>,
}

struct PatternDeclSpans {
    name: String,
    name_range: ByteRange,
    params: Vec<ByteRange>,
    target: Option<(ByteRange, String)>,
    view_binders: Vec<ByteRange>,
    make_binders: Vec<ByteRange>,
}

struct StableDeclSpans {
    name: String,
    name_range: Option<ByteRange>,
    rungs: Vec<StableRungSpans>,
    type_refs: Vec<(ByteRange, String)>,
    // The rung references in the `migrations` rows (`V1 -> V2 = ...`), each paired
    // with the internal rung type it names, so the table hovers like the rungs do.
    migration_refs: Vec<(ByteRange, String)>,
}

struct StableRungSpans {
    canonical: String,
    name_range: Option<ByteRange>,
    base_range: Option<ByteRange>,
    base_canonical: Option<String>,
    fields: Vec<(ByteRange, String)>,
}

struct LambdaBinderSpan {
    lambda: ByteRange,
    binder: ByteRange,
    index: usize,
}

struct HeaderRef {
    range: (usize, usize),
    name: String,
    decl: String,
    upper: bool,
    // Directly after `|` inside a row (`! {FileSystem | e}`): syntactically a
    // row-tail variable, kind `Row`, even when generalization stored it as an
    // existential the scheme no longer names.
    row_tail: bool,
    // Inside a `@ fact` / `@ {fact, fact}` coeffect annotation: the word names
    // a usage fact, not a value or type.
    coeffect: bool,
}

struct SurfaceBinder {
    range: (usize, usize),
    decl: String,
    param: Option<usize>,
}

// The nearest `name` identifier token inside `[lo, hi)`: a binder written
// between its introducing keyword and its bound expression.
fn binder_token(
    tokens: &[(usize, Token, usize)],
    name: &str,
    lo: usize,
    hi: usize,
) -> Option<(usize, usize)> {
    tokens
        .iter()
        .filter(|(start, token, end)| {
            *start >= lo && *end <= hi && matches!(token, Token::Ident(n) if n == name)
        })
        .map(|(start, _, end)| (*start, *end))
        .next_back()
}

// The operation/error head and its parameter binders inside one clause header.
// The parser stores the names but not their pointable ranges; restricting the
// token search to the text before the arm body keeps calls in the body out.
fn clause_head(
    tokens: &[(usize, Token, usize)],
    name: &str,
    upper: bool,
    params: &[String],
    lo: usize,
    hi: usize,
) -> Option<ClauseHead> {
    let (head_at, &(start, _, _)) =
        tokens.iter().enumerate().find(|(_, (start, token, end))| {
            *start >= lo
                && *end <= hi
                && if upper {
                    matches!(token, Token::UIdent(found) if found == name)
                } else {
                    matches!(token, Token::Ident(found) if found == name)
                }
        })?;
    let open_at = (head_at + 1..tokens.len()).find(|&at| {
        let (token_start, token, token_end) = &tokens[at];
        *token_start >= start && *token_end <= hi && matches!(token, Token::LParen)
    })?;
    let mut depth = 0usize;
    let mut next_param = 0usize;
    let mut binders = Vec::new();
    for &(token_start, ref token, token_end) in &tokens[open_at..] {
        if token_start >= hi || token_end > hi {
            break;
        }
        match token {
            Token::LParen => depth += 1,
            Token::RParen if depth == 1 => {
                return Some(ClauseHead {
                    range: (start, token_end),
                    binders,
                });
            }
            Token::RParen => depth = depth.saturating_sub(1),
            Token::Ident(found)
                if depth == 1 && params.get(next_param).is_some_and(|name| name == found) =>
            {
                binders.push((token_start, token_end));
                next_param += 1;
            }
            _ => {}
        }
    }
    None
}

fn collect_handler_arms(
    clause_start: usize,
    arms: &[HandlerArm],
    tokens: &[(usize, Token, usize)],
    effect_heads: &mut Vec<EffectHeadSpan>,
    binders: &mut Vec<ClauseBinderSpan>,
) {
    let mut cursor = clause_start;
    for arm in arms {
        let body = match arm {
            HandlerArm::Return(_, body)
            | HandlerArm::Op(_, _, _, body)
            | HandlerArm::Sugar(
                SugarArm::Once(_, _, body) | SugarArm::Val(_, body) | SugarArm::Never(_, _, body),
            ) => body,
        };
        let body_range = (body.span.start, body.span.end);
        match arm {
            HandlerArm::Return(name, _) => {
                if let Some(range) = binder_token(tokens, name, cursor, body.span.start) {
                    binders.push(ClauseBinderSpan {
                        range,
                        name: name.clone(),
                        body: body_range,
                        source: ClauseBinderSource::Return,
                    });
                }
            }
            HandlerArm::Op(operation, params, continuation, _) => {
                if let Some(head) =
                    clause_head(tokens, operation, false, params, cursor, body.span.start)
                {
                    effect_heads.push(EffectHeadSpan {
                        range: head.range,
                        lookup: operation.clone(),
                        display: operation.clone(),
                    });
                    for (index, (name, range)) in params.iter().zip(head.binders).enumerate() {
                        binders.push(ClauseBinderSpan {
                            range,
                            name: name.clone(),
                            body: body_range,
                            source: ClauseBinderSource::OperationParam {
                                operation: operation.clone(),
                                index,
                            },
                        });
                    }
                    if let Some(range) =
                        binder_token(tokens, continuation, head.range.1, body.span.start)
                    {
                        binders.push(ClauseBinderSpan {
                            range,
                            name: continuation.clone(),
                            body: body_range,
                            source: ClauseBinderSource::Continuation {
                                operation: operation.clone(),
                            },
                        });
                    }
                }
            }
            HandlerArm::Sugar(
                SugarArm::Once(operation, params, _) | SugarArm::Never(operation, params, _),
            ) => {
                if let Some(head) =
                    clause_head(tokens, operation, false, params, cursor, body.span.start)
                {
                    effect_heads.push(EffectHeadSpan {
                        range: head.range,
                        lookup: operation.clone(),
                        display: operation.clone(),
                    });
                    for (index, (name, range)) in params.iter().zip(head.binders).enumerate() {
                        binders.push(ClauseBinderSpan {
                            range,
                            name: name.clone(),
                            body: body_range,
                            source: ClauseBinderSource::OperationParam {
                                operation: operation.clone(),
                                index,
                            },
                        });
                    }
                }
            }
            HandlerArm::Sugar(SugarArm::Val(name, _)) => {
                if let Some(range) = binder_token(tokens, name, cursor, body.span.start) {
                    binders.push(ClauseBinderSpan {
                        range,
                        name: name.clone(),
                        body: body_range,
                        source: ClauseBinderSource::Value,
                    });
                }
            }
        }
        cursor = body.span.end;
    }
}

fn collect_clause_spans(
    e: &S<Expr>,
    tokens: &[(usize, Token, usize)],
    effect_heads: &mut Vec<EffectHeadSpan>,
    binders: &mut Vec<ClauseBinderSpan>,
) {
    match &e.node {
        Expr::Handle(body, arms, _) => {
            collect_handler_arms(body.span.end, arms, tokens, effect_heads, binders);
        }
        Expr::Sugar(Sugar::NamedHandle(_, _, arms)) => {
            collect_handler_arms(e.span.start, arms, tokens, effect_heads, binders);
        }
        Expr::Sugar(Sugar::TryCatch(body, arms)) => {
            let mut cursor = body.span.end;
            for arm in arms {
                let operation = names::throw_op(&arm.name);
                if let Some(head) = clause_head(
                    tokens,
                    &arm.name,
                    true,
                    &arm.binders,
                    cursor,
                    arm.body.span.start,
                ) {
                    effect_heads.push(EffectHeadSpan {
                        range: head.range,
                        lookup: operation.clone(),
                        display: arm.name.clone(),
                    });
                    for (index, (name, range)) in arm.binders.iter().zip(head.binders).enumerate() {
                        binders.push(ClauseBinderSpan {
                            range,
                            name: name.clone(),
                            body: (arm.body.span.start, arm.body.span.end),
                            source: ClauseBinderSource::CatchParam {
                                operation: operation.clone(),
                                index,
                            },
                        });
                    }
                }
                cursor = arm.body.span.end;
            }
        }
        _ => {}
    }
    e.node.each_child(&mut |child| {
        collect_clause_spans(child, tokens, effect_heads, binders);
    });
}

fn lambda_binder_ranges(e: &S<Expr>, tokens: &[(usize, Token, usize)]) -> Vec<ByteRange> {
    let Expr::Lam(params, body) = &e.node else {
        return Vec::new();
    };
    params
        .iter()
        .filter_map(|param| binder_token(tokens, &param.name, e.span.start, body.span.start))
        .collect()
}

fn collect_lambda_binders(
    e: &S<Expr>,
    tokens: &[(usize, Token, usize)],
    out: &mut Vec<LambdaBinderSpan>,
) {
    if let Expr::Lam(_, _) = &e.node {
        for (index, binder) in lambda_binder_ranges(e, tokens).into_iter().enumerate() {
            out.push(LambdaBinderSpan {
                lambda: (e.span.start, e.span.end),
                binder,
                index,
            });
        }
    }
    e.node
        .each_child(&mut |child| collect_lambda_binders(child, tokens, out));
}

fn collect_pattern_decl_spans(
    decl: &PatternDecl,
    tokens: &[(usize, Token, usize)],
) -> Option<PatternDeclSpans> {
    let head = clause_head(
        tokens,
        &decl.name,
        true,
        &decl.params,
        decl.span.start,
        decl.view.span.start,
    )?;
    let name_range = tokens
        .iter()
        .find(|(start, token, end)| {
            *start >= decl.span.start
                && *end <= head.range.1
                && matches!(token, Token::UIdent(name) if name == &decl.name)
        })
        .map(|(start, _, end)| (*start, *end))?;
    let target = tokens
        .iter()
        .position(|(start, token, end)| {
            *start >= head.range.1 && *end <= decl.view.span.start && matches!(token, Token::For)
        })
        .and_then(|at| {
            tokens[at + 1..].iter().find_map(|(start, token, end)| {
                (*end <= decl.view.span.start
                    && matches!(token, Token::UIdent(name) if name == &decl.for_ty))
                .then(|| ((*start, *end), decl.for_ty.clone()))
            })
        });
    Some(PatternDeclSpans {
        name: decl.name.clone(),
        name_range,
        params: head.binders,
        target,
        view_binders: lambda_binder_ranges(&decl.view, tokens),
        make_binders: decl
            .make
            .as_ref()
            .map_or_else(Vec::new, |make| lambda_binder_ranges(make, tokens)),
    })
}

fn collect_pattern_heads(
    pattern: &S<Pattern>,
    names: &BTreeSet<String>,
    tokens: &[(usize, Token, usize)],
    out: &mut Vec<(ByteRange, String)>,
) {
    match &pattern.node {
        Pattern::Ctor(name, patterns) => {
            if names.contains(name) {
                if let Some((start, _, end)) = tokens.iter().find(|(start, token, end)| {
                    *start >= pattern.span.start
                        && *end <= pattern.span.end
                        && matches!(token, Token::UIdent(found) if found == name)
                }) {
                    out.push(((*start, *end), name.clone()));
                }
            }
            for pattern in patterns {
                collect_pattern_heads(pattern, names, tokens, out);
            }
        }
        Pattern::Tuple(patterns) => {
            for pattern in patterns {
                collect_pattern_heads(pattern, names, tokens, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, pattern) in fields {
                collect_pattern_heads(pattern, names, tokens, out);
            }
        }
        Pattern::Wild
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => {}
    }
}

fn collect_pattern_heads_expr(
    e: &S<Expr>,
    names: &BTreeSet<String>,
    tokens: &[(usize, Token, usize)],
    out: &mut Vec<(ByteRange, String)>,
) {
    if let Expr::Match(_, arms) = &e.node {
        for arm in arms {
            collect_pattern_heads(&arm.pat, names, tokens, out);
        }
    }
    e.node.each_child(&mut |child| {
        collect_pattern_heads_expr(child, names, tokens, out);
    });
}

// The internal type name of a rung named `ver`: the bare stable name for the
// current (last) rung, its dotted version tag otherwise. Shared by the rung
// declarations and the migration rows that reference them.
fn rung_canonical(decl: &StableDecl, ver: &str) -> String {
    if decl.rungs.last().is_some_and(|last| last.name == ver) {
        decl.name.clone()
    } else {
        names::stable_rung(&decl.name, ver)
    }
}

fn collect_stable_decl_spans(
    decl: &StableDecl,
    tokens: &[(usize, Token, usize)],
) -> StableDeclSpans {
    let name_range = tokens
        .iter()
        .find(|(start, token, end)| {
            *start >= decl.span.start
                && *end <= decl.span.end
                && matches!(token, Token::UIdent(name) if name == &decl.name)
        })
        .map(|(start, _, end)| (*start, *end));
    let mut rungs = Vec::new();
    let mut type_refs = Vec::new();
    for rung in &decl.rungs {
        let body = tokens
            .iter()
            .filter(|(start, _, end)| *start >= rung.span.start && *end <= rung.span.end)
            .collect::<Vec<_>>();
        let rung_name = body.iter().find_map(|&&(start, ref token, end)| {
            matches!(token, Token::UIdent(name) if name == &rung.name).then_some((start, end))
        });
        let base_range = rung.base.as_ref().and_then(|base| {
            body.iter().enumerate().find_map(|(at, &(_, token, _))| {
                matches!(token, Token::DotDot)
                    .then(|| body.get(at + 1))
                    .flatten()
                    .and_then(|&&(start, ref token, end)| {
                        matches!(token, Token::UIdent(name) if name == base).then_some((start, end))
                    })
            })
        });
        let defaults = rung
            .fields
            .iter()
            .filter_map(|field| field.default.as_ref())
            .map(|default| (default.span.start, default.span.end))
            .collect::<Vec<_>>();
        let mut fields = Vec::new();
        for field in &rung.fields {
            if let Some(range) = body.iter().enumerate().find_map(|(at, token)| {
                let &&(start, ref candidate, end) = token;
                (matches!(candidate, Token::Ident(name) if name == &field.name)
                    && matches!(body.get(at + 1), Some((_, Token::Colon, _))))
                .then_some((start, end))
            }) {
                fields.push((range, field.name.clone()));
            }
        }
        for &&(start, ref token, end) in &body {
            let in_default = defaults.iter().any(|(lo, hi)| start >= *lo && end <= *hi);
            if in_default || Some((start, end)) == rung_name || Some((start, end)) == base_range {
                continue;
            }
            let name = match token {
                Token::UIdent(name) => Some(name.clone()),
                _ => prim_type_name(token).map(str::to_string),
            };
            if let Some(name) = name {
                type_refs.push(((start, end), name));
            }
        }
        let canonical = rung_canonical(decl, &rung.name);
        rungs.push(StableRungSpans {
            canonical,
            name_range: rung_name,
            base_range,
            base_canonical: rung
                .base
                .as_ref()
                .map(|base| names::stable_rung(&decl.name, base)),
            fields,
        });
    }
    let mut migration_refs = Vec::new();
    for mig in &decl.migrations {
        for ver in [mig.from.as_str(), mig.to.as_str()] {
            if let Some(range) = tokens.iter().find_map(|(start, token, end)| {
                (*start >= mig.span.start
                    && *end <= mig.span.end
                    && matches!(token, Token::UIdent(name) if name.as_str() == ver))
                .then_some((*start, *end))
            }) {
                migration_refs.push((range, rung_canonical(decl, ver)));
            }
        }
    }
    StableDeclSpans {
        name: decl.name.clone(),
        name_range,
        rungs,
        type_refs,
        migration_refs,
    }
}

// `let` and `var` binders: the binder identifier's range paired with its bound
// expression's range. The bound expression's checked rendering is the binder's
// type, so the join happens against the resolved value spans.
fn collect_let_binders(e: &S<Expr>, tokens: &[(usize, Token, usize)], out: &mut Vec<RangeLink>) {
    let bound = match &e.node {
        Expr::Let(name, value, _) | Expr::Sugar(Sugar::VarDecl(name, value, _)) => {
            Some((name, value))
        }
        _ => None,
    };
    if let Some((name, value)) = bound {
        if let Some(range) = binder_token(tokens, name, e.span.start, value.span.start) {
            out.push((range, (value.span.start, value.span.end)));
        }
    }
    e.node
        .each_child(&mut |child| collect_let_binders(child, tokens, out));
}

// Lexer-recovered ranges inside one `type` declaration: the declared name, each
// named field binder (constructor name and field position), every capitalized
// identifier in a type position (a constructor reference whose kind the hover
// shows), and every lowercase identifier (a type-parameter binding or
// reference, whose kind comes from the declaration's parameter kinds).
struct TypeDeclSpans {
    name: String,
    params: Vec<String>,
    name_range: Option<(usize, usize)>,
    ctors: Vec<((usize, usize), String)>,
    fields: Vec<((usize, usize), String, usize)>,
    type_refs: Vec<((usize, usize), String)>,
    vars: Vec<((usize, usize), String)>,
}

// Walk one `type` declaration's tokens. The declared name is the first
// `UIdent` matching it; after `=` or `|` at nesting depth zero the next
// `UIdent` is a constructor name (a value, skipped here); inside a
// constructor's braces an `Ident` directly before `:` is a named field binder;
// every other `UIdent` sits in a type position and is a constructor reference.
fn collect_data_spans(decl: &DataDecl, tokens: &[(usize, Token, usize)]) -> TypeDeclSpans {
    let body = tokens
        .iter()
        .filter(|(start, _, end)| *start >= decl.span.start && *end <= decl.span.end)
        .collect::<Vec<_>>();
    let mut out = TypeDeclSpans {
        name: decl.name.clone(),
        params: decl.params.clone(),
        name_range: None,
        ctors: Vec::new(),
        fields: Vec::new(),
        type_refs: Vec::new(),
        vars: Vec::new(),
    };
    let mut depth = 0usize;
    let mut expect_ctor = false;
    let mut ctor: Option<(String, usize)> = None;
    let mut index = 0;
    while index < body.len() {
        let &(start, ref token, end) = body[index];
        match token {
            Token::Eq | Token::Bar if depth == 0 => expect_ctor = true,
            Token::LParen | Token::LBrace | Token::LBracket => depth += 1,
            Token::RParen | Token::RBrace | Token::RBracket => depth = depth.saturating_sub(1),
            Token::UIdent(name) => {
                if out.name_range.is_none() && name == &decl.name {
                    out.name_range = Some((start, end));
                } else if expect_ctor && depth == 0 {
                    out.ctors.push(((start, end), name.clone()));
                    ctor = Some((name.clone(), 0));
                    expect_ctor = false;
                } else {
                    out.type_refs.push(((start, end), name.clone()));
                }
            }
            Token::Ident(name) => {
                // A named field binder is an identifier directly before `:`
                // inside a constructor's braces; any other lowercase
                // identifier in the declaration is a type-parameter binding or
                // reference (header parens, field annotations, kind
                // annotations aside).
                let before_colon = matches!(body.get(index + 1), Some((_, Token::Colon, _)));
                if depth == 1 && before_colon && ctor.is_some() {
                    if let Some((ctor_name, field_index)) = &mut ctor {
                        out.fields
                            .push(((start, end), ctor_name.clone(), *field_index));
                        *field_index += 1;
                    }
                } else if decl.params.iter().any(|p| p == name) {
                    out.vars.push(((start, end), name.clone()));
                }
            }
            _ => {
                // Primitive type names lex as keywords; they are type
                // references like any capitalized identifier.
                if let Some(name) = prim_type_name(token) {
                    out.type_refs.push(((start, end), name.to_string()));
                }
            }
        }
        index += 1;
    }
    out
}

// Lexer-recovered ranges inside one `class` declaration: the class name, the
// parameter binder in the header, and, per method signature, every capitalized
// identifier in a type position (a type-constructor or class reference) and
// every lowercase identifier (a type variable, since a method signature has no
// value-level names). Each variable carries the index of its declaring method
// so its kind can be read off that method's checked type.
struct ClassDeclSpans {
    name: String,
    param: String,
    name_range: Option<(usize, usize)>,
    param_range: Option<(usize, usize)>,
    type_refs: Vec<((usize, usize), String)>,
    vars: Vec<((usize, usize), String, usize)>,
}

// Walk one `class` declaration's tokens. The raw lexer emits no layout tokens,
// so header and body are separated structurally: the class name is the first
// `UIdent` matching it, the parameter binder is the first `Ident` matching the
// parameter (the one inside the header parens, which precedes any `given` or
// method-signature use). A method signature is `name : ty`; the name is an
// `Ident` before `:` at bracket depth zero matching a declared method, and its
// type tokens run until the next such name. Inside a signature a `UIdent` is a
// type/class reference and a lowercase `Ident` a type variable.
fn collect_class_spans(decl: &ClassDecl, tokens: &[(usize, Token, usize)]) -> ClassDeclSpans {
    let body = tokens
        .iter()
        .filter(|(start, _, end)| *start >= decl.span.start && *end <= decl.span.end)
        .collect::<Vec<_>>();
    let mut out = ClassDeclSpans {
        name: decl.name.clone(),
        param: decl.param.clone(),
        name_range: None,
        param_range: None,
        type_refs: Vec::new(),
        vars: Vec::new(),
    };
    let mut depth = 0usize;
    let mut method: Option<usize> = None;
    for index in 0..body.len() {
        let &(start, ref token, end) = body[index];
        match token {
            Token::LParen | Token::LBrace | Token::LBracket => depth += 1,
            Token::RParen | Token::RBrace | Token::RBracket => depth = depth.saturating_sub(1),
            Token::UIdent(name) if out.name_range.is_none() && name == &decl.name => {
                out.name_range = Some((start, end));
            }
            Token::UIdent(name) if method.is_some() => {
                out.type_refs.push(((start, end), name.clone()));
            }
            Token::Ident(name) if out.param_range.is_none() && name == &decl.param => {
                out.param_range = Some((start, end));
            }
            Token::Ident(name)
                if depth == 0
                    && matches!(body.get(index + 1), Some((_, Token::Colon, _)))
                    && decl.methods.iter().any(|(m, _)| m == name) =>
            {
                method = decl.methods.iter().position(|(m, _)| m == name);
            }
            Token::Ident(name) => {
                if let Some(at) = method {
                    out.vars.push(((start, end), name.clone(), at));
                }
            }
            _ => {
                if let (Some(name), Some(_)) = (prim_type_name(token), method) {
                    out.type_refs.push(((start, end), name.to_string()));
                }
            }
        }
    }
    out
}

// Candidate identifier references in a declaration header: every `UIdent`
// (constructor or class reference) and `Ident` (type-variable reference)
// between the header start and the body, excluding default-expression ranges
// (a constructor there is a value the expression walk already covers). Binder
// ranges are excluded by the caller, which knows them.
fn collect_header_refs(
    decl: &Decl<Surface>,
    tokens: &[(usize, Token, usize)],
    refs: &mut Vec<HeaderRef>,
) {
    let defaults: Vec<(usize, usize)> = decl
        .params
        .iter()
        .filter_map(|p| p.default.as_ref())
        .map(|d| (d.span.start, d.span.end))
        .collect();
    let mut after_bar = false;
    // 0 = outside any `@` annotation, 1 = directly after `@` (one fact), 2 =
    // inside `@ { ... }` (a fact list).
    let mut at_depth = 0usize;
    for (start, token, end) in tokens {
        if *start < decl.span.start || *end > decl.body.span.start {
            continue;
        }
        if defaults.iter().any(|(lo, hi)| start >= lo && end <= hi) {
            continue;
        }
        match token {
            Token::At => {
                at_depth = 1;
                after_bar = false;
                continue;
            }
            Token::LBrace if at_depth == 1 => {
                at_depth = 2;
                continue;
            }
            Token::RBrace if at_depth == 2 => {
                at_depth = 0;
                continue;
            }
            Token::Comma if at_depth == 2 => continue,
            _ => {}
        }
        let (name, upper) = match token {
            Token::UIdent(name) => (name.clone(), true),
            Token::Ident(name) => (name.clone(), false),
            _ => {
                if let Some(name) = prim_type_name(token) {
                    (name.to_string(), true)
                } else {
                    after_bar = matches!(token, Token::Bar);
                    continue;
                }
            }
        };
        let coeffect = !upper && at_depth > 0;
        if at_depth == 1 {
            at_depth = 0;
        }
        refs.push(HeaderRef {
            range: (*start, *end),
            name,
            decl: decl.name.clone(),
            upper,
            row_tail: after_bar && !upper && !coeffect,
            coeffect,
        });
        after_bar = false;
    }
}

// The wired-in scalar type name a keyword token spells, if any: primitive type
// names lex as dedicated keywords, not identifiers, so the type-level hover
// recovers their names here.
const fn prim_type_name(token: &Token) -> Option<&'static str> {
    match token {
        Token::KwInt => Some(kw::TY_INT),
        Token::KwI64 => Some(kw::TY_I64),
        Token::KwU64 => Some(kw::TY_U64),
        Token::KwBool => Some(kw::TY_BOOL),
        Token::KwFloat => Some(kw::TY_FLOAT),
        Token::KwChar => Some(kw::TY_CHAR),
        Token::KwString => Some(kw::TY_STRING),
        Token::KwUnit => Some(kw::TY_UNIT),
        _ => None,
    }
}

// Declaration names and parameters do not carry their own AST spans. Recover
// them from the lexer inside the parsed declaration header: the first matching
// identifier is the declaration name, and at parenthesis depth one each
// comma-delimited parameter begins with an optional `borrow` then its binder.
// Annotation/default-expression identifiers are therefore never mistaken for
// binders.
fn collect_decl_binders(
    decl: &Decl<Surface>,
    tokens: &[(usize, Token, usize)],
    binders: &mut Vec<SurfaceBinder>,
) {
    let header = tokens
        .iter()
        .filter(|(start, _, end)| *start >= decl.span.start && *end <= decl.body.span.start)
        .collect::<Vec<_>>();
    let Some((name_at, _, name_end)) = header
        .iter()
        .copied()
        .find(|(_, token, _)| matches!(token, Token::Ident(name) if name == &decl.name))
    else {
        return;
    };
    binders.push(SurfaceBinder {
        range: (*name_at, *name_end),
        decl: decl.name.clone(),
        param: None,
    });
    if decl.params.is_empty() {
        return;
    }

    let mut depth = 0usize;
    let mut next_param = 0usize;
    let mut expecting_binder = false;
    for &&(start, ref token, end) in header.iter().skip_while(|(start, _, _)| *start < *name_end) {
        match token {
            Token::LParen => {
                depth += 1;
                if depth == 1 {
                    expecting_binder = true;
                }
            }
            Token::RParen if depth == 1 => break,
            Token::RParen => depth = depth.saturating_sub(1),
            Token::LBrace | Token::LBracket if depth > 0 => depth += 1,
            Token::RBrace | Token::RBracket if depth > 1 => depth -= 1,
            Token::Comma if depth == 1 => expecting_binder = true,
            Token::Borrow if depth == 1 && expecting_binder => {}
            Token::Ident(name) if depth == 1 && expecting_binder => {
                let Some(param) = decl.params.get(next_param) else {
                    break;
                };
                if name == &param.name {
                    binders.push(SurfaceBinder {
                        range: (start, end),
                        decl: decl.name.clone(),
                        param: Some(next_param),
                    });
                    next_param += 1;
                    expecting_binder = false;
                }
            }
            _ => {}
        }
    }
}

fn surface_nodes(src: &str) -> Result<SurfaceNodes, Error> {
    let surface = parse(src)?.program;
    let (tokens, _) = lex_raw(src)?;
    let user_start = SourceMap::new(src).prelude_len();
    let mut names = BTreeSet::new();
    let mut spans = BTreeSet::new();
    let mut binders = Vec::new();
    let mut type_decls = Vec::new();
    let mut header_refs = Vec::new();
    let mut let_binders = Vec::new();
    let mut effect_heads = Vec::new();
    let mut clause_binders = Vec::new();
    let mut pattern_decls = Vec::new();
    let mut pattern_heads = Vec::new();
    let mut stable_decls = Vec::new();
    let mut lambda_binders = Vec::new();
    let walk_decl = |decl: &Decl<Surface>,
                     binders: &mut Vec<SurfaceBinder>,
                     header_refs: &mut Vec<HeaderRef>,
                     spans: &mut BTreeSet<(usize, usize)>,
                     let_binders: &mut Vec<RangeLink>,
                     effect_heads: &mut Vec<EffectHeadSpan>,
                     clause_binders: &mut Vec<ClauseBinderSpan>| {
        collect_decl_binders(decl, &tokens, binders);
        collect_header_refs(decl, &tokens, header_refs);
        for param in &decl.params {
            if let Some(default) = &param.default {
                collect_surface_expr(default, spans);
                collect_let_binders(default, &tokens, let_binders);
                collect_clause_spans(default, &tokens, effect_heads, clause_binders);
            }
        }
        collect_surface_expr(&decl.body, spans);
        collect_let_binders(&decl.body, &tokens, let_binders);
        collect_clause_spans(&decl.body, &tokens, effect_heads, clause_binders);
        for (name, expr) in &decl.wheres {
            collect_surface_expr(expr, spans);
            collect_let_binders(expr, &tokens, let_binders);
            collect_clause_spans(expr, &tokens, effect_heads, clause_binders);
            // The `where` binder itself: the nearest matching identifier
            // between the body's end and the bound expression.
            if let Some(range) = binder_token(&tokens, name, decl.body.span.end, expr.span.start) {
                let_binders.push((range, (expr.span.start, expr.span.end)));
            }
        }
    };
    for decl in &surface.fns {
        if decl.span.start < user_start {
            continue;
        }
        names.insert(decl.name.clone());
        walk_decl(
            decl,
            &mut binders,
            &mut header_refs,
            &mut spans,
            &mut let_binders,
            &mut effect_heads,
            &mut clause_binders,
        );
    }
    for instance in &surface.instances {
        if instance.span.start < user_start {
            continue;
        }
        for method in &instance.methods {
            walk_decl(
                method,
                &mut binders,
                &mut header_refs,
                &mut spans,
                &mut let_binders,
                &mut effect_heads,
                &mut clause_binders,
            );
        }
    }
    let pattern_names = surface
        .patterns
        .iter()
        .map(|decl| decl.name.clone())
        .collect::<BTreeSet<_>>();
    for decl in &surface.patterns {
        names.insert(names::pat_view(&decl.name));
        collect_surface_expr(&decl.view, &mut spans);
        collect_let_binders(&decl.view, &tokens, &mut let_binders);
        collect_clause_spans(&decl.view, &tokens, &mut effect_heads, &mut clause_binders);
        collect_pattern_heads_expr(&decl.view, &pattern_names, &tokens, &mut pattern_heads);
        collect_lambda_binders(&decl.view, &tokens, &mut lambda_binders);
        if let Some(make) = &decl.make {
            names.insert(names::pat_make(&decl.name));
            collect_surface_expr(make, &mut spans);
            collect_let_binders(make, &tokens, &mut let_binders);
            collect_clause_spans(make, &tokens, &mut effect_heads, &mut clause_binders);
            collect_pattern_heads_expr(make, &pattern_names, &tokens, &mut pattern_heads);
            collect_lambda_binders(make, &tokens, &mut lambda_binders);
        }
        if let Some(found) = collect_pattern_decl_spans(decl, &tokens) {
            pattern_decls.push(found);
        }
    }
    for decl in &surface.stable {
        for pair in decl.rungs.windows(2) {
            names.insert(names::stable_upgrade(
                &decl.name,
                &pair[0].name,
                &pair[1].name,
            ));
            names.insert(names::stable_downgrade(
                &decl.name,
                &pair[1].name,
                &pair[0].name,
            ));
        }
        for rung in &decl.rungs {
            for field in &rung.fields {
                if let Some(default) = &field.default {
                    collect_surface_expr(default, &mut spans);
                    collect_let_binders(default, &tokens, &mut let_binders);
                    collect_clause_spans(default, &tokens, &mut effect_heads, &mut clause_binders);
                    collect_pattern_heads_expr(
                        default,
                        &pattern_names,
                        &tokens,
                        &mut pattern_heads,
                    );
                    collect_lambda_binders(default, &tokens, &mut lambda_binders);
                }
            }
        }
        for converter in &decl.converters {
            let generated = match converter.dir {
                crate::syntax::ast::ConvDir::Upgrade => {
                    names::stable_upgrade(&decl.name, &converter.from, &converter.to)
                }
                crate::syntax::ast::ConvDir::Downgrade => {
                    names::stable_downgrade(&decl.name, &converter.from, &converter.to)
                }
            };
            names.insert(generated);
            for expr in std::iter::once(&converter.base)
                .chain(converter.overrides.iter().map(|(_, expr)| expr))
            {
                collect_surface_expr(expr, &mut spans);
                collect_let_binders(expr, &tokens, &mut let_binders);
                collect_clause_spans(expr, &tokens, &mut effect_heads, &mut clause_binders);
                collect_pattern_heads_expr(expr, &pattern_names, &tokens, &mut pattern_heads);
                collect_lambda_binders(expr, &tokens, &mut lambda_binders);
            }
        }
        stable_decls.push(collect_stable_decl_spans(decl, &tokens));
    }
    for decl in &surface.fns {
        collect_pattern_heads_expr(&decl.body, &pattern_names, &tokens, &mut pattern_heads);
        collect_lambda_binders(&decl.body, &tokens, &mut lambda_binders);
        for param in &decl.params {
            if let Some(default) = &param.default {
                collect_pattern_heads_expr(default, &pattern_names, &tokens, &mut pattern_heads);
                collect_lambda_binders(default, &tokens, &mut lambda_binders);
            }
        }
        for (_, expr) in &decl.wheres {
            collect_pattern_heads_expr(expr, &pattern_names, &tokens, &mut pattern_heads);
            collect_lambda_binders(expr, &tokens, &mut lambda_binders);
        }
    }
    for instance in &surface.instances {
        for method in &instance.methods {
            collect_pattern_heads_expr(&method.body, &pattern_names, &tokens, &mut pattern_heads);
            collect_lambda_binders(&method.body, &tokens, &mut lambda_binders);
        }
    }
    for decl in &surface.types {
        if decl.span.start < user_start {
            continue;
        }
        type_decls.push(collect_data_spans(decl, &tokens));
    }
    let mut class_decls = Vec::new();
    for decl in &surface.classes {
        if decl.span.start < user_start {
            continue;
        }
        class_decls.push(collect_class_spans(decl, &tokens));
    }
    let mut effect_names = Vec::new();
    let mut effect_ops = Vec::new();
    for decl in &surface.effects {
        if decl.span.start < user_start {
            continue;
        }
        // The declared name is its first matching `UIdent`; an operation binder
        // is its declared name directly before `(` (grade words and annotation
        // identifiers never precede a parenthesis there).
        let mut found_effect_name = false;
        let body: Vec<_> = tokens
            .iter()
            .filter(|(start, _, end)| *start >= decl.span.start && *end <= decl.span.end)
            .collect();
        for (at, &&(start, ref token, end)) in body.iter().enumerate() {
            match token {
                Token::UIdent(name) if !found_effect_name && name == &decl.name => {
                    effect_names.push(((start, end), decl.name.clone()));
                    found_effect_name = true;
                }
                Token::Ident(name)
                    if decl.ops.iter().any(|op| &op.name == name)
                        && matches!(body.get(at + 1), Some((_, Token::LParen, _))) =>
                {
                    effect_ops.push(((start, end), name.clone()));
                }
                _ => {}
            }
        }
    }
    Ok(SurfaceNodes {
        root_names: names,
        ranges: spans,
        binders,
        type_decls,
        class_decls,
        header_refs,
        let_binders,
        effect_names,
        effect_ops,
        effect_heads,
        clause_binders,
        pattern_decls,
        pattern_heads,
        stable_decls,
        lambda_binders,
    })
}

// The kind of a bound type variable, read off its scheme: a `RowForall` binder
// is `Row`; otherwise its kind is derived from its widest application in the
// scheme body (`f(a, b)` makes `f : Type -> Type -> Type`), defaulting each
// domain to `Type`. An unapplied variable is `Type`. This is exactly the
// checker's own defaulting, so higher-kinded variables render honestly.
fn var_kind(name: &Sym, ty: &Type) -> Kind {
    fn arity(name: &Sym, ty: &Type, max: &mut usize) {
        match ty {
            Type::App(_, _) => {
                let mut head = ty;
                let mut count = 0usize;
                while let Type::App(inner, arg) = head {
                    arity(name, arg, max);
                    head = inner;
                    count += 1;
                }
                if matches!(head, Type::Var(v) if v == name) {
                    *max = (*max).max(count);
                }
            }
            Type::Forall(_, body) | Type::RowForall(_, body) | Type::OrNull(body) => {
                arity(name, body, max);
            }
            Type::Fun(params, row, result) => {
                for param in params {
                    arity(name, param, max);
                }
                row.for_each_arg(&mut |argument| arity(name, argument, max));
                arity(name, result, max);
            }
            Type::Con(_, arguments) | Type::Tuple(arguments) | Type::UnboxedTuple(arguments) => {
                for argument in arguments {
                    arity(name, argument, max);
                }
            }
            Type::UnboxedRecord(fields) => {
                for (_, field) in fields {
                    arity(name, field, max);
                }
            }
            Type::Row(row) => row.for_each_arg(&mut |argument| arity(name, argument, max)),
            Type::Coeffect(inner, _) => {
                arity(name, inner, max);
            }
            Type::Unit
            | Type::Int
            | Type::I64
            | Type::U64
            | Type::Bool
            | Type::Float
            | Type::Char
            | Type::Str
            | Type::Var(_)
            | Type::Exist(_)
            | Type::Nat(_) => {}
        }
    }
    let mut body = ty;
    while let Type::Forall(bound, next) | Type::RowForall(bound, next) = body {
        if bound == name && matches!(body, Type::RowForall(..)) {
            return Kind::Row;
        }
        body = next;
    }
    let mut max = 0usize;
    arity(name, body, &mut max);
    Kind::arrow(&vec![Kind::Type; max])
}

// The domain count of an arrow kind, the comparison key for "widest use".
fn kind_arity(kind: &Kind) -> usize {
    match kind {
        Kind::Fun(_, rest) => 1 + kind_arity(rest),
        _ => 0,
    }
}

// Whether the scheme binds `name` at all (a `Forall` or `RowForall` binder).
fn scheme_binds(name: &Sym, mut ty: &Type) -> bool {
    while let Type::Forall(bound, next) | Type::RowForall(bound, next) = ty {
        if bound == name {
            return true;
        }
        ty = next;
    }
    false
}

fn function_domains(mut ty: &Type) -> Option<&[Type]> {
    while let Type::Forall(_, body) | Type::RowForall(_, body) = ty {
        ty = body;
    }
    match ty {
        Type::Fun(domains, _, _) => Some(domains),
        _ => None,
    }
}

fn function_result(mut ty: &Type) -> Option<&Type> {
    while let Type::Forall(_, body) | Type::RowForall(_, body) = ty {
        ty = body;
    }
    match ty {
        Type::Fun(_, _, result) => Some(result),
        _ => None,
    }
}

fn checked_decl_type<'a>(checked: &'a Checked, name: &str) -> Option<&'a Type> {
    checked
        .decls
        .iter()
        .find(|decl| decl.name == name)
        .map(|decl| &decl.ty)
        .or_else(|| checked.env.get(&Sym::from(name)))
}

fn pattern_parameter_types(checked: &Checked, name: &str, arity: usize) -> Vec<String> {
    if let Some(make) = checked_decl_type(checked, &names::pat_make(name)) {
        return function_domains(make)
            .unwrap_or_default()
            .iter()
            .map(Type::show)
            .collect();
    }
    let Some(payload) = checked_decl_type(checked, &names::pat_view(name))
        .and_then(function_result)
        .and_then(|result| match result {
            Type::Con(option, args)
                if names::bare_name(option.as_str()) == "Option" && args.len() == 1 =>
            {
                args.first()
            }
            _ => None,
        })
    else {
        return Vec::new();
    };
    if arity == 1 {
        vec![payload.show()]
    } else if let Type::Tuple(types) = payload {
        types.iter().map(Type::show).collect()
    } else {
        Vec::new()
    }
}

fn pattern_tooltip(checked: &Checked, name: &str) -> Option<String> {
    checked_decl_type(checked, &names::pat_make(name))
        .or_else(|| checked_decl_type(checked, &names::pat_view(name)))
        .map(pure_tooltip)
}

fn resolve_pattern_spans(
    surface: &SurfaceNodes,
    checked: &Checked,
    resolved: &mut BTreeMap<ByteRange, (String, Level)>,
    typelevel: &impl Fn(&str) -> Option<(String, Level)>,
    class_of: &impl Fn(&str) -> Option<(String, Level)>,
) {
    for decl in &surface.pattern_decls {
        if let Some(rendered) = pattern_tooltip(checked, &decl.name) {
            resolved
                .entry(decl.name_range)
                .or_insert((rendered, Level::Value));
        }
        let params = pattern_parameter_types(checked, &decl.name, decl.params.len());
        for (range, rendered) in decl.params.iter().zip(&params) {
            resolved
                .entry(*range)
                .or_insert_with(|| (rendered.clone(), Level::PatternVar));
        }
        if let Some((range, target)) = &decl.target {
            if let Some(entry) = typelevel(target).or_else(|| class_of(target)) {
                resolved.entry(*range).or_insert(entry);
            }
        }
        if let Some(view) = checked_decl_type(checked, &names::pat_view(&decl.name)) {
            for (range, ty) in decl
                .view_binders
                .iter()
                .zip(function_domains(view).unwrap_or_default())
            {
                resolved
                    .entry(*range)
                    .or_insert_with(|| (ty.show(), Level::PatternVar));
            }
        }
        if let Some(make) = checked_decl_type(checked, &names::pat_make(&decl.name)) {
            for (range, ty) in decl
                .make_binders
                .iter()
                .zip(function_domains(make).unwrap_or_default())
            {
                resolved
                    .entry(*range)
                    .or_insert_with(|| (ty.show(), Level::PatternVar));
            }
        }
    }
    for (range, name) in &surface.pattern_heads {
        if let Some(rendered) = pattern_tooltip(checked, name) {
            resolved.entry(*range).or_insert((rendered, Level::Value));
        }
    }
}

fn resolve_stable_spans(
    surface: &SurfaceNodes,
    checked: &Checked,
    resolved: &mut BTreeMap<ByteRange, (String, Level)>,
    typelevel: &impl Fn(&str) -> Option<(String, Level)>,
    class_of: &impl Fn(&str) -> Option<(String, Level)>,
) {
    for decl in &surface.stable_decls {
        if let (Some(range), Some(entry)) = (decl.name_range, typelevel(&decl.name)) {
            resolved.entry(range).or_insert(entry);
        }
        for rung in &decl.rungs {
            if let (Some(range), Some(entry)) = (rung.name_range, typelevel(&rung.canonical)) {
                resolved.entry(range).or_insert(entry);
            }
            if let (Some(range), Some(base)) = (rung.base_range, &rung.base_canonical) {
                if let Some(entry) = typelevel(base) {
                    resolved.entry(range).or_insert(entry);
                }
            }
            let ctor = checked.ctors.get(&rung.canonical);
            for (range, field) in &rung.fields {
                let ty = ctor.and_then(|info| {
                    info.fields
                        .iter()
                        .position(|name| name.as_str() == field)
                        .and_then(|index| info.args.get(index))
                });
                if let Some(ty) = ty {
                    resolved
                        .entry(*range)
                        .or_insert_with(|| (ty.show(), Level::Value));
                }
            }
        }
        for (range, name) in &decl.type_refs {
            if let Some(entry) = typelevel(name).or_else(|| class_of(name)) {
                resolved.entry(*range).or_insert(entry);
            }
        }
        for (range, canonical) in &decl.migration_refs {
            if let Some(entry) = typelevel(canonical) {
                resolved.entry(*range).or_insert(entry);
            }
        }
    }
}

// A binder or field is not a computation: its tooltip is the type alone, the
// same empty-row elision expression tooltips use.
fn pure_tooltip(ty: &Type) -> String {
    ty.show()
}

fn collect_checked_expr(
    e: &S<Expr<Core>>,
    surface: &BTreeSet<(usize, usize)>,
    checked: &Checked,
    found: &mut BTreeMap<(usize, usize), BTreeSet<String>>,
) {
    let range = (e.span.start, e.span.end);
    if surface.contains(&range) {
        if let Some(rendered) = checked.facts.tooltip(e.id) {
            found.entry(range).or_default().insert(rendered.to_string());
        }
    }
    e.node
        .each_child(&mut |child| collect_checked_expr(child, surface, checked, found));
}

fn collect_checked_lambda_binders(
    e: &S<Expr<Core>>,
    links: &BTreeMap<ByteRange, Vec<(ByteRange, usize)>>,
    hir: &CheckedHir<'_>,
    found: &mut BTreeMap<ByteRange, BTreeSet<String>>,
) {
    let range = (e.span.start, e.span.end);
    if let Expr::Lam(_, _) = &e.node {
        if let (Some(binders), Some(domains)) = (
            links.get(&range),
            hir.node_type(e.id).and_then(function_domains),
        ) {
            for (binder, index) in binders {
                if let Some(ty) = domains.get(*index) {
                    found.entry(*binder).or_default().insert(ty.show());
                }
            }
        }
    }
    e.node.each_child(&mut |child| {
        collect_checked_lambda_binders(child, links, hir, found);
    });
}

// The rendered type of the first `Var(name)` occurrence in `e`, the same
// checker fact its own value-level tooltip would show. A pattern binder has
// no `NodeId` of its own, so this is the join back to the checked type: an
// unused binder (never named in its arm's body) simply gets no tooltip.
fn find_var_fact(e: &S<Expr<Core>>, name: &str, checked: &Checked) -> Option<String> {
    if let Expr::Var(x) = &e.node {
        if x == name {
            if let Some(rendered) = checked.facts.tooltip(e.id) {
                return Some(rendered.to_string());
            }
        }
    }
    let mut found = None;
    e.node.each_child(&mut |child| {
        if found.is_none() {
            found = find_var_fact(child, name, checked);
        }
    });
    found
}

// Resolve a surface operation spelling against the checked table. Imported
// operations are canonicalized there, so a bare-name match is accepted only
// when it is unique.
fn operation_info<'a>(checked: &'a Checked, operation: &str) -> Option<&'a EffOpInfo> {
    if let Some(info) = checked.eff_ops.get(operation) {
        return Some(info);
    }
    let mut matches = checked
        .eff_ops
        .iter()
        .filter(|(name, _)| names::bare_name(name) == operation)
        .map(|(_, info)| info);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn effect_op_tooltip(display: &str, info: &EffOpInfo) -> String {
    let params = info
        .params
        .iter()
        .map(Type::show)
        .collect::<Vec<_>>()
        .join(", ");
    let grade = if info.grade.is_default() {
        String::new()
    } else {
        format!("{} ", info.grade.word())
    };
    let ret = info.ret.show();
    let ret = ret.strip_suffix("@throw").unwrap_or(&ret);
    format!("{grade}{display}({params}) : {ret}")
}

fn find_var_fact_in_range(
    e: &S<Expr<Core>>,
    range: ByteRange,
    name: &str,
    checked: &Checked,
) -> Option<String> {
    if let Expr::Var(found) = &e.node {
        if found == name && e.span.start >= range.0 && e.span.end <= range.1 {
            if let Some(rendered) = checked.facts.tooltip(e.id) {
                return Some(rendered.to_string());
            }
        }
    }
    let mut found = None;
    e.node.each_child(&mut |child| {
        if found.is_none() {
            found = find_var_fact_in_range(child, range, name, checked);
        }
    });
    found
}

fn clause_var_fact(
    program: &Program<Core>,
    range: ByteRange,
    name: &str,
    checked: &Checked,
) -> Option<String> {
    for decl in &program.fns {
        if let Some(rendered) = find_var_fact_in_range(&decl.body, range, name, checked) {
            return Some(rendered);
        }
    }
    for instance in &program.instances {
        for method in &instance.methods {
            if let Some(rendered) = find_var_fact_in_range(&method.body, range, name, checked) {
                return Some(rendered);
            }
        }
    }
    None
}

fn resolve_effect_spans(
    surface: &SurfaceNodes,
    program: &Program<Core>,
    checked: &Checked,
    resolved: &mut BTreeMap<ByteRange, (String, Level)>,
    effect_of: &impl Fn(&str) -> Option<(String, Level)>,
) {
    for (range, name) in &surface.effect_names {
        if let Some(entry) = effect_of(name) {
            resolved.entry(*range).or_insert(entry);
        }
    }
    for (range, operation) in &surface.effect_ops {
        if let Some(info) = operation_info(checked, operation) {
            resolved
                .entry(*range)
                .or_insert_with(|| (effect_op_tooltip(operation, info), Level::Effect));
        }
    }
    for head in &surface.effect_heads {
        if let Some(info) = operation_info(checked, &head.lookup) {
            resolved
                .entry(head.range)
                .or_insert_with(|| (effect_op_tooltip(&head.display, info), Level::Effect));
        }
    }
    for binder in &surface.clause_binders {
        let occurrence = clause_var_fact(program, binder.body, &binder.name, checked);
        let entry = match &binder.source {
            ClauseBinderSource::OperationParam { operation, index }
            | ClauseBinderSource::CatchParam { operation, index } => occurrence
                .or_else(|| {
                    operation_info(checked, operation)
                        .and_then(|info| info.params.get(*index))
                        .map(Type::show)
                })
                .map(|rendered| (rendered, Level::PatternVar)),
            ClauseBinderSource::Continuation { operation } => occurrence.map(|rendered| {
                let rendered = operation_info(checked, operation).map_or_else(
                    || rendered.clone(),
                    |info| format!("{rendered}; declared resumption: {}", info.grade.word()),
                );
                (rendered, Level::Coeffect)
            }),
            ClauseBinderSource::Return | ClauseBinderSource::Value => {
                occurrence.map(|rendered| (rendered, Level::PatternVar))
            }
        };
        if let Some(entry) = entry {
            resolved.entry(binder.range).or_insert(entry);
        }
    }
}

fn instantiated_ctor_args(info: &CtorInfo, expected: Option<&Type>) -> Vec<Type> {
    let mut args = info.args.clone();
    let Some(Type::Con(name, actuals)) = expected else {
        return args;
    };
    if name != &info.type_name {
        return args;
    }
    for arg in &mut args {
        for ((param, kind), actual) in info.params.iter().zip(&info.param_kinds).zip(actuals) {
            match (kind, actual) {
                (Kind::Row, Type::Row(row)) => *arg = arg.subst_row_var(*param, row),
                _ => *arg = arg.subst_var(*param, actual),
            }
        }
    }
    args
}

fn collect_typed_pattern(
    pattern: &S<Pattern>,
    expected: Option<&Type>,
    body: &S<Expr<Core>>,
    checked: &Checked,
    resolved: &mut BTreeMap<ByteRange, (String, Level)>,
) {
    let range = (pattern.span.start, pattern.span.end);
    match &pattern.node {
        Pattern::Wild => {
            if let Some(ty) = expected {
                resolved
                    .entry(range)
                    .or_insert_with(|| (ty.show(), Level::PatternVar));
            }
        }
        Pattern::Var(name) => {
            let rendered = find_var_fact(body, name, checked).or_else(|| expected.map(Type::show));
            if let Some(rendered) = rendered {
                resolved
                    .entry(range)
                    .or_insert((rendered, Level::PatternVar));
            }
        }
        Pattern::Tuple(patterns) => {
            let types = match expected {
                Some(Type::Tuple(types)) => types.as_slice(),
                _ => &[],
            };
            for (index, pattern) in patterns.iter().enumerate() {
                collect_typed_pattern(pattern, types.get(index), body, checked, resolved);
            }
        }
        Pattern::Ctor(name, patterns) if name == kw::CTOR_THIS => {
            let expected = match expected {
                Some(Type::OrNull(inner)) => Some(inner.as_ref()),
                _ => None,
            };
            if let Some(pattern) = patterns.first() {
                collect_typed_pattern(pattern, expected, body, checked, resolved);
            }
        }
        Pattern::Ctor(name, patterns) => {
            let types = checked
                .ctors
                .get(name)
                .map(|info| instantiated_ctor_args(info, expected))
                .unwrap_or_default();
            for (index, pattern) in patterns.iter().enumerate() {
                collect_typed_pattern(pattern, types.get(index), body, checked, resolved);
            }
        }
        Pattern::Record(name, fields, _) => {
            let info = checked.ctors.get(name);
            let types = info
                .map(|info| instantiated_ctor_args(info, expected))
                .unwrap_or_default();
            for (field, pattern) in fields {
                let expected = info
                    .and_then(|info| info.fields.iter().position(|name| name.as_str() == field))
                    .and_then(|index| types.get(index));
                collect_typed_pattern(pattern, expected, body, checked, resolved);
            }
        }
        Pattern::Int(_) | Pattern::Float(_) | Pattern::Char(_) | Pattern::Bool(_) => {}
    }
}

// Match-arm patterns carry no binder `NodeId`. Join used names to their body
// facts and recover unused variables/wildcards structurally from the zonked
// scrutinee type and constructor field types.
fn collect_pattern_var_binders(
    e: &S<Expr<Core>>,
    hir: &CheckedHir<'_>,
    checked: &Checked,
    resolved: &mut BTreeMap<(usize, usize), (String, Level)>,
) {
    if let Expr::Match(scrutinee, arms) = &e.node {
        let expected = hir.node_type(scrutinee.id);
        for arm in arms {
            collect_typed_pattern(&arm.pat, expected, &arm.body, checked, resolved);
        }
    }
    e.node.each_child(&mut |child| {
        collect_pattern_var_binders(child, hir, checked, resolved);
    });
}

fn into_document(src: &str, resolved: BTreeMap<ByteRange, (String, Level)>) -> TypeSpans {
    let user_start = SourceMap::new(src).prelude_len();
    let mut spans = resolved
        .into_iter()
        .filter_map(|((start, end), (rendered, level))| {
            (start < end && start >= user_start && end <= src.len()).then(|| TypeSpan {
                start: start - user_start,
                end: end - user_start,
                rendered,
                level,
            })
        })
        .collect::<Vec<_>>();
    spans.sort_by(|a, b| {
        (a.start, std::cmp::Reverse(a.end), &a.rendered).cmp(&(
            b.start,
            std::cmp::Reverse(b.end),
            &b.rendered,
        ))
    });
    TypeSpans {
        format: TYPESPANS_FORMAT.to_string(),
        spans,
    }
}

/// Join surface expression ranges to the checker facts recorded on the
/// desugared tree. Only root-file nodes with a unique mapping survive; imported,
/// synthesized, zero-width, and ambiguously desugared nodes are filtered out.
pub(crate) fn extract(
    src: &str,
    program: &Program<Core>,
    checked: &Checked,
) -> Result<TypeSpans, Error> {
    let surface = surface_nodes(src)?;
    let hir = crate::hir::build(checked);
    let mut found: BTreeMap<(usize, usize), BTreeSet<String>> = BTreeMap::new();
    for decl in &program.fns {
        if surface.root_names.contains(&decl.name) {
            collect_checked_expr(&decl.body, &surface.ranges, checked, &mut found);
        }
    }

    let mut lambda_links: BTreeMap<ByteRange, Vec<(ByteRange, usize)>> = BTreeMap::new();
    for binder in &surface.lambda_binders {
        lambda_links
            .entry(binder.lambda)
            .or_default()
            .push((binder.binder, binder.index));
    }
    for decl in &program.fns {
        if surface.root_names.contains(&decl.name) {
            collect_checked_lambda_binders(&decl.body, &lambda_links, &hir, &mut found);
        }
    }
    for instance in &program.instances {
        if instance.module.is_empty() {
            for method in &instance.methods {
                collect_checked_lambda_binders(&method.body, &lambda_links, &hir, &mut found);
            }
        }
    }
    for instance in &program.instances {
        if instance.module.is_empty() {
            for method in &instance.methods {
                collect_checked_expr(&method.body, &surface.ranges, checked, &mut found);
            }
        }
    }

    // Header binders are values too, but unlike expressions they have no
    // `NodeId`. Join their lexer ranges to the checked declaration scheme (or
    // the class-method scheme in the environment). A declaration name denotes
    // the function value; a parameter denotes the corresponding arrow domain.
    for binder in &surface.binders {
        let scheme = checked
            .decls
            .iter()
            .find(|info| info.name == binder.decl)
            .map(|info| &info.ty)
            .or_else(|| checked.env.get(&Sym::from(&binder.decl)));
        let Some(scheme) = scheme else {
            continue;
        };
        let rendered = binder.param.map_or_else(
            || Some(pure_tooltip(scheme)),
            |index| {
                function_domains(scheme)
                    .and_then(|domains| domains.get(index))
                    .map(pure_tooltip)
            },
        );
        if let Some(rendered) = rendered {
            found.entry(binder.range).or_default().insert(rendered);
        }
    }

    // Collapse desugar ambiguity on the expression ranges first: `BTreeSet`
    // merged equivalent desugar nodes, and a genuinely ambiguous range (more
    // than one distinct rendering) is dropped.
    let mut resolved: BTreeMap<(usize, usize), (String, Level)> = found
        .into_iter()
        .filter_map(|(range, rendered)| {
            if rendered.len() != 1 {
                return None;
            }
            Some((range, (rendered.into_iter().next()?, Level::Value)))
        })
        .collect();

    for decl in &program.fns {
        if surface.root_names.contains(&decl.name) {
            collect_pattern_var_binders(&decl.body, &hir, checked, &mut resolved);
        }
    }
    for instance in &program.instances {
        if instance.module.is_empty() {
            for method in &instance.methods {
                collect_pattern_var_binders(&method.body, &hir, checked, &mut resolved);
            }
        }
    }

    // Type-declaration spans. Field binders are values (the field's type);
    // the declared name and every constructor reference in a type position are
    // type-level, rendered with the constructor's kind. Vacant ranges only: a
    // constructor used as a value keeps its value tooltip.
    let kind_of = |name: &str| {
        if PRIM_TYPES.contains(&name) {
            return Some(Kind::Type.show());
        }
        checked
            .data
            .get(name)
            .map(|info| Kind::arrow(&info.param_kinds).show())
    };
    let typelevel =
        |name: &str| kind_of(name).map(|kind| (format!("{name} : {kind}"), Level::Typelevel));
    // A class reference renders its head (with the parameter's kind when it is
    // higher-kinded, derived from the parameter's widest application across the
    // method schemes), its superclasses, and its method names.
    let class_of = |name: &str| {
        checked.classes.get(&Sym::from(name)).map(|info| {
            let kind = info
                .methods
                .iter()
                .map(|(_, ty)| var_kind(&info.param, ty))
                .max_by_key(kind_arity)
                .unwrap_or_default();
            let param = if kind == Kind::Type {
                info.param.to_string()
            } else {
                format!("{} : {}", info.param, kind.show())
            };
            let mut rendered = format!("{name}({param})");
            if !info.supers.is_empty() {
                let supers = info
                    .supers
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(rendered, "; superclasses: {supers}")
                    .expect("writing to a String cannot fail");
            }
            if !info.methods.is_empty() {
                let methods = info
                    .methods
                    .iter()
                    .map(|(method, _)| method.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(rendered, "; methods: {methods}").expect("writing to a String cannot fail");
            }
            (rendered, Level::Class)
        })
    };
    // An effect reference renders the effect and its operation names (each
    // prefixed by its resumption grade when narrower than the default),
    // recovered by grouping the checked op table by declaring effect.
    let effect_of = |name: &str| {
        if crate::tc::is_builtin_effect(name)
            && !checked
                .eff_ops
                .values()
                .any(|info| info.effect_name.to_string() == name)
        {
            return Some((format!("{name}; builtin effect"), Level::Effect));
        }
        let ops = checked
            .eff_ops
            .iter()
            .filter(|(_, info)| info.effect_name.to_string() == name)
            .map(|(op, info)| {
                if info.grade.is_default() {
                    op.clone()
                } else {
                    format!("{} {op}", info.grade.word())
                }
            })
            .collect::<Vec<_>>();
        if ops.is_empty() {
            return None;
        }
        Some((
            format!("{name}; operations: {}", ops.join(", ")),
            Level::Effect,
        ))
    };
    for decl in &surface.type_decls {
        if let (Some(range), Some(entry)) = (decl.name_range, typelevel(&decl.name)) {
            resolved.entry(range).or_insert(entry);
        }
        // A constructor name in its declaration denotes the constructor
        // function: its arguments to the declared type.
        for (range, ctor_name) in &decl.ctors {
            let Some(info) = checked.ctors.get(ctor_name) else {
                continue;
            };
            let result = if decl.params.is_empty() {
                decl.name.clone()
            } else {
                format!("{}({})", decl.name, decl.params.join(", "))
            };
            let rendered = if info.args.is_empty() {
                result
            } else {
                let args = info
                    .args
                    .iter()
                    .map(Type::show)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({args}) -> {result}")
            };
            resolved.entry(*range).or_insert((rendered, Level::Value));
        }
        for (range, ctor_name, index) in &decl.fields {
            let Some(ty) = checked
                .ctors
                .get(ctor_name)
                .and_then(|info| info.args.get(*index))
            else {
                continue;
            };
            resolved
                .entry(*range)
                .or_insert_with(|| (ty.show(), Level::Value));
        }
        for (range, name) in &decl.type_refs {
            if let Some(entry) = typelevel(name).or_else(|| class_of(name)) {
                resolved.entry(*range).or_insert(entry);
            }
        }
        // Type parameters: bindings and references alike render the parameter
        // with its declared kind (`Type` unless annotated `Row`/`Nat`, or an
        // arrow for a higher-kinded parameter).
        let param_kinds = checked.data.get(&decl.name).map(|info| &info.param_kinds);
        for (range, name) in &decl.vars {
            let kind = decl
                .params
                .iter()
                .position(|p| p == name)
                .and_then(|at| param_kinds.and_then(|kinds| kinds.get(at)))
                .cloned()
                .unwrap_or_default();
            resolved
                .entry(*range)
                .or_insert_with(|| (format!("{name} : {}", kind.show()), Level::Typevar));
        }
    }
    // Class-declaration spans. The class name and its superclass references are
    // class-level; the parameter binder and every method-signature type variable
    // are type variables, kinded from their widest use in the checked method
    // types (the class parameter across all methods, a method-local variable
    // within its own method), exactly as the class hover kinds the parameter.
    for decl in &surface.class_decls {
        let info = checked.classes.get(&Sym::from(&decl.name));
        let param_kind = info
            .map(|info| {
                info.methods
                    .iter()
                    .map(|(_, ty)| var_kind(&info.param, ty))
                    .max_by_key(kind_arity)
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        if let (Some(range), Some(entry)) = (decl.name_range, class_of(&decl.name)) {
            resolved.entry(range).or_insert(entry);
        }
        if let Some(range) = decl.param_range {
            resolved.entry(range).or_insert_with(|| {
                (
                    format!("{} : {}", decl.param, param_kind.show()),
                    Level::Typevar,
                )
            });
        }
        for (range, name) in &decl.type_refs {
            if let Some(entry) = typelevel(name).or_else(|| class_of(name)) {
                resolved.entry(*range).or_insert(entry);
            }
        }
        for (range, name, method) in &decl.vars {
            let kind = if name == &decl.param {
                param_kind.clone()
            } else {
                info.and_then(|info| info.methods.get(*method))
                    .map(|(_, ty)| var_kind(&Sym::from(name.as_str()), ty))
                    .unwrap_or_default()
            };
            resolved
                .entry(*range)
                .or_insert_with(|| (format!("{name} : {}", kind.show()), Level::Typevar));
        }
    }

    resolve_pattern_spans(&surface, checked, &mut resolved, &typelevel, &class_of);
    resolve_stable_spans(&surface, checked, &mut resolved, &typelevel, &class_of);
    for reference in &surface.header_refs {
        let entry = if reference.coeffect {
            // A usage fact under `@`: rendered as its canonical lattice word.
            CoeffectFact::parse(&reference.name)
                .map(|fact| (fact.name().to_string(), Level::Coeffect))
        } else if reference.upper {
            typelevel(&reference.name)
                .or_else(|| class_of(&reference.name))
                .or_else(|| effect_of(&reference.name))
        } else if reference.row_tail {
            // A row-tail position is syntactically kind `Row` even when the
            // scheme stored the variable as an unnamed existential.
            Some((
                format!("{} : {}", reference.name, Kind::Row.show()),
                Level::Typevar,
            ))
        } else {
            let name = Sym::from(reference.name.as_str());
            let scheme = checked
                .decls
                .iter()
                .find(|info| info.name == reference.decl)
                .map(|info| &info.ty)
                .or_else(|| checked.env.get(&Sym::from(&reference.decl)));
            scheme
                .filter(|scheme| scheme_binds(&name, scheme))
                .map(|scheme| {
                    (
                        format!("{} : {}", reference.name, var_kind(&name, scheme).show()),
                        Level::Typevar,
                    )
                })
        };
        if let Some(entry) = entry {
            resolved.entry(reference.range).or_insert(entry);
        }
    }

    // `let`/`var`/`where` binders: a binder's type is its bound expression's
    // rendering, so the join is against the already-resolved value spans.
    for (binder, value) in &surface.let_binders {
        if let Some((rendered, Level::Value)) = resolved.get(value).cloned() {
            resolved.entry(*binder).or_insert((rendered, Level::Value));
        }
    }

    resolve_effect_spans(&surface, program, checked, &mut resolved, &effect_of);

    // A typed hole's inferred type wins over any expression fact on the same
    // range: the hole is the thing the reader is asking about.
    for hole in &checked.holes {
        let rendered = if hole.effects == "{}" {
            hole.expected.clone()
        } else {
            format!("{} ! {}", hole.expected, hole.effects)
        };
        resolved.insert((hole.start, hole.end), (rendered, Level::Hole));
    }

    // Logical subexpressions in `logic fn` bodies and `requires`/`ensures` clauses
    // are sort-checked separately and erased before Core, so they have no checked
    // HIR entry. Their tooltips come from re-parsing the surface program and
    // running the logical sort checker in recording mode; they live in source
    // regions disjoint from the runtime body spans, so they never collide with a
    // value span already resolved above.
    if let Ok(parsed) = crate::parse::parse(src) {
        for (start, end, sort) in crate::verify::check::Checker::logic_typespans(&parsed.program) {
            resolved
                .entry((start, end))
                .or_insert_with(|| (sort.smtlib().to_string(), Level::Logic));
        }
    }

    Ok(into_document(src, resolved))
}
