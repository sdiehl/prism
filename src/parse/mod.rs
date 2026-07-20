use std::collections::{BTreeMap, BTreeSet};

use lalrpop_util::ParseError::{
    ExtraToken, InvalidToken, UnrecognizedEof, UnrecognizedToken, User,
};
use marginalia::{Span, TriviaTable};

use crate::error::{LexError, ParseError, SourceMap};
use crate::lex::{lex, lex_raw, Token};
use crate::syntax::ast::{Expr, Item, Program, Vis, S};
use crate::syntax::{ExprParser, ProgramParser};

#[derive(Debug)]
pub struct ParseResult {
    pub program: Program,
    pub trivia: TriviaTable,
}

// Cap on how many expected tokens a syntax error lists before eliding the rest.
const MAX_EXPECTED_SHOWN: usize = 8;

fn from_lex(src: &str, e: &LexError) -> ParseError {
    ParseError::Syntax {
        span: Span::new(e.offset(), e.offset()),
        msg: format!("{e} at {}", SourceMap::new(src).at(e.offset())),
    }
}

/// # Errors
/// Fails on lex or syntax errors.
pub fn parse_expr(src: &str) -> Result<S<Expr>, ParseError> {
    let (tokens, _) = lex_raw(src).map_err(|e| from_lex(src, &e))?;
    ExprParser::new()
        .parse(tokens)
        .map_err(|e| from_lalrpop(src, &e))
}

/// Whether `src` fails to parse as an expression only because it ends early.
///
/// An interactive caller uses this to keep reading more lines. An open string,
/// unfinished interpolation, or a parse that wants more tokens at EOF all count.
#[must_use]
pub fn incomplete(src: &str) -> bool {
    match lex_raw(src) {
        Err(LexError::UnterminatedString { .. } | LexError::UnterminatedHole { .. }) => true,
        Err(_) => false,
        Ok((tokens, _)) => matches!(
            ExprParser::new().parse(tokens),
            Err(lalrpop_util::ParseError::UnrecognizedEof { .. })
        ),
    }
}

/// # Errors
/// Fails on lex or syntax errors.
pub fn parse(src: &str) -> Result<ParseResult, ParseError> {
    let (tokens, trivia) = lex(src).map_err(|e| from_lex(src, &e))?;
    let items = ProgramParser::new()
        .parse(tokens)
        .map_err(|e| from_lalrpop(src, &e))?;
    let mut types = Vec::new();
    let mut effects = Vec::new();
    let mut errors = Vec::new();
    let mut aliases = Vec::new();
    let mut synonyms = Vec::new();
    let mut classes = Vec::new();
    let mut instances = Vec::new();
    let mut canonicals = Vec::new();
    let mut patterns = Vec::new();
    let mut fns = Vec::new();
    let mut logic_fns = Vec::new();
    let mut stable = Vec::new();
    let mut imports = Vec::new();
    let mut exports = BTreeSet::new();
    let mut opaques = BTreeSet::new();
    let mut deprecated = BTreeMap::new();
    // A `deprecated "..."` item attaches to the next declaration, so carry it
    // across the loop step. Set once, consumed by the following named decl.
    let mut pending_dep: Option<(Span, String)> = None;
    for (vis, item) in items {
        if let Item::Deprecated(span, msg) = item {
            if pending_dep.is_some() {
                return Err(ParseError::Syntax {
                    span,
                    msg: "a `deprecated` annotation must be followed by a declaration".into(),
                });
            }
            pending_dep = Some((span, msg));
            continue;
        }
        let name = export_name(&item).map(str::to_owned);
        if let Some((dspan, dmsg)) = pending_dep.take() {
            match &name {
                Some(n) => {
                    deprecated.insert(n.clone(), dmsg);
                }
                None => {
                    return Err(ParseError::Syntax {
                        span: dspan,
                        msg: "a `deprecated` annotation must precede a named declaration".into(),
                    });
                }
            }
        }
        if vis != Vis::Priv {
            if let Some(name) = &name {
                exports.insert(name.clone());
                if vis == Vis::Opaque {
                    opaques.insert(name.clone());
                }
            }
        }
        match item {
            Item::Import(mut i) => {
                // `pub import` re-exports; the parse-time export set stays own-only
                // (re-exports are propagated during resolution).
                i.reexport = vis == Vis::Pub;
                imports.push(i);
            }
            Item::Data(d) => types.push(d),
            Item::Effect(e) => effects.push(e),
            Item::Error(e) => errors.push(e),
            Item::Alias(a) => aliases.push(a),
            Item::Synonym(s) => synonyms.push(s),
            Item::Class(c) => classes.push(c),
            Item::Instance(i) => instances.push(i),
            Item::Canonical(c) => canonicals.push(c),
            Item::Pattern(p) => patterns.push(p),
            Item::Fn(f) => fns.push(f),
            Item::LogicFn(f) => logic_fns.push(f),
            Item::Stable(s) => stable.push(s),
            Item::Deprecated(..) => unreachable!("attached to the next decl above"),
        }
    }
    if let Some((span, _)) = pending_dep {
        return Err(ParseError::Syntax {
            span,
            msg: "a `deprecated` annotation must be followed by a declaration".into(),
        });
    }
    Ok(ParseResult {
        program: Program {
            types,
            effects,
            errors,
            aliases,
            synonyms,
            classes,
            instances,
            stable,
            canonicals,
            patterns,
            fns,
            logic_fns,
            imports,
            exports,
            opaques,
            deprecated,
        },
        trivia,
    })
}

// The name a `pub` item exports. Instances are always global, so `pub` on one
// is a no-op rather than an export.
fn export_name(item: &Item) -> Option<&str> {
    match item {
        Item::Data(d) => Some(&d.name),
        Item::Effect(e) => Some(&e.name),
        Item::Error(e) => Some(&e.name),
        Item::Alias(a) => Some(&a.name),
        Item::Synonym(s) => Some(&s.name),
        Item::Class(c) => Some(&c.name),
        Item::Pattern(p) => Some(&p.name),
        Item::Fn(f) | Item::LogicFn(f) => Some(&f.name),
        Item::Stable(s) => Some(&s.name),
        Item::Instance(_) | Item::Canonical(_) | Item::Import(_) | Item::Deprecated(..) => None,
    }
}

fn expected_name(raw: &str) -> String {
    match raw.trim_matches('"') {
        "v{" => "start of block".into(),
        "v}" => "end of block".into(),
        "v;" => "end of statement".into(),
        "ident" => "identifier".into(),
        "uid" => "uppercase identifier".into(),
        "int" => "integer literal".into(),
        "float" => "float literal".into(),
        "str" | "istart" | "imid" | "iend" => "string literal".into(),
        r"\\" => r"'\'".into(),
        t => format!("'{t}'"),
    }
}

fn expected_list(expected: &[String]) -> String {
    let mut names: Vec<String> = Vec::new();
    for e in expected {
        let n = expected_name(e);
        if !names.contains(&n) {
            names.push(n);
        }
    }
    let tail = if names.len() > MAX_EXPECTED_SHOWN {
        ", ..."
    } else {
        ""
    };
    names.truncate(MAX_EXPECTED_SHOWN);
    format!("{}{tail}", names.join(", "))
}

fn from_lalrpop(
    src: &str,
    e: &lalrpop_util::ParseError<usize, Token, (Span, String)>,
) -> ParseError {
    let map = SourceMap::new(src);
    match e {
        InvalidToken { location } => ParseError::Syntax {
            span: Span::new(*location, *location),
            msg: "invalid token".into(),
        },
        UnrecognizedEof { location, expected } => {
            let mut msg = format!("unexpected end of input at {}", map.at(*location));
            if !expected.is_empty() {
                msg = format!("{msg}, expected {}", expected_list(expected));
            }
            ParseError::Syntax {
                span: Span::new(*location, *location),
                msg,
            }
        }
        UnrecognizedToken { token, expected } => {
            let msg = format!(
                "unexpected {} at {}, expected {}",
                token.1,
                map.at(token.0),
                expected_list(expected)
            );
            ParseError::Syntax {
                span: Span::new(token.0, token.2),
                msg,
            }
        }
        ExtraToken { token } => ParseError::Syntax {
            span: Span::new(token.0, token.2),
            msg: format!("extra token {}", token.1),
        },
        User { error: (span, msg) } => ParseError::Syntax {
            span: *span,
            msg: msg.clone(),
        },
    }
}
