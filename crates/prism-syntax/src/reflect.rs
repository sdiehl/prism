//! `reflect fn f` / `reflect type T`: quoting a declaration's own canonical
//! rendering.
//!
//! The quotation is the formatter's, not a slice of the file, so two spellings
//! of one declaration quote identically and the quotation moves only when the
//! declaration does. It is spliced in as an ordinary string literal before name
//! resolution, over one compilation unit at a time: the rendering is therefore
//! the declaration as its author wrote it rather than as the resolver rewrote
//! it, and a target can only be a declaration of the same file.
//!
//! Nothing survives the pass. A `Sugar::Reflect` reaching a later phase means a
//! compilation entry parsed a unit with [`parse`] instead of [`parse_unit`].

use std::collections::BTreeMap;

use marginalia::TriviaTable;

use crate::ast::{Expr, Program, ReflectKind, SExpr, Span, Sugar};
use crate::error::{ErrKind, Error, TypeError};
use crate::fmt::format_items;
use crate::kw;
use crate::lex::{LexSpanned, Token};
use crate::parse::{parse, ParseResult};

// What a quotation asks for: a declaration form and a name. The pair is what is
// looked up, and so also what a rendering is reused under.
type Target = (ReflectKind, String);

/// Parse a compilation unit: the parser's output with every `reflect` quotation
/// already spliced in.
///
/// [`parse`] stays the pure surface entry, the one the formatter and the syntax
/// dumps need; a phase that feeds the checker wants this one.
///
/// # Errors
/// Fails on lex or syntax errors, or when a quotation names no declaration of
/// the file it appears in.
pub fn parse_unit(src: &str) -> Result<Program, Error> {
    let ParseResult {
        mut program,
        trivia,
    } = parse(src)?;
    splice(src, &trivia, &mut program)?;
    Ok(program)
}

/// Whether `tokens` contain a quotation, and so whether the unit they came from
/// has its own comments in what it computes.
///
/// A splice carries the comments written above its target, so a comment-only
/// edit to a file that quotes itself changes the program's output; a file that
/// does not quote itself has trivia that is not semantic at all. Anything
/// digesting a token stream as a unit's semantic identity has to ask this. The
/// answer lives here because this module is what decides what the form is.
#[must_use]
pub fn quotes_source(tokens: &[LexSpanned]) -> bool {
    tokens.windows(2).any(|w| {
        matches!(&w[0].1, Token::Ident(word) if word == kw::REFLECT)
            && matches!(w[1].1, Token::Fn | Token::Type)
    })
}

/// Replace every `reflect` quotation in one loose expression with the rendering
/// it names, looked up in the unit that expression is typed into.
///
/// The interactive shell evaluates an expression that never passes through the
/// program parser, so it splices here instead; `source`, `trivia`, and `prog`
/// are the session's, which is what its unit is.
///
/// # Errors
/// Fails when a quotation names no declaration of that unit.
pub fn splice_expr(
    source: &str,
    trivia: &TriviaTable,
    prog: &Program,
    e: &mut SExpr,
) -> Result<(), TypeError> {
    let mut targets = Vec::new();
    collect(e, &mut targets);
    if targets.is_empty() {
        return Ok(());
    }
    let quotes = quote_each(source, trivia, prog, &targets)?;
    substitute(e, &quotes);
    Ok(())
}

/// Replace every `reflect` quotation in `prog` with the rendering it names.
///
/// `source` and `trivia` must be the ones `prog` was parsed from: the rendering
/// comes from the formatter, which reads the comments back out of them.
///
/// # Errors
/// Fails when a quotation names no declaration of this file, including one
/// reached through a prepended prelude rather than the author's own text.
pub fn splice(source: &str, trivia: &TriviaTable, prog: &mut Program) -> Result<(), TypeError> {
    let targets = targets(prog);
    if targets.is_empty() {
        return Ok(());
    }
    let quotes = quote_each(source, trivia, prog, &targets)?;
    prog.each_root_expr_mut(&mut |e| substitute(e, &quotes));
    Ok(())
}

// Every quotation the unit asks for, each with the span to blame if it names
// nothing. Written as a mutable walk because that is the walk `substitute` also
// needs; it changes nothing.
fn targets(prog: &mut Program) -> Vec<(Target, Span)> {
    let mut out = Vec::new();
    prog.each_root_expr_mut(&mut |e| collect(e, &mut out));
    out
}

fn collect(e: &mut SExpr, out: &mut Vec<(Target, Span)>) {
    if let Expr::Sugar(Sugar::Reflect(kind, name)) = &e.node {
        out.push(((*kind, name.clone()), e.span));
    }
    e.node.each_child_mut(&mut |c| collect(c, out));
}

fn substitute(e: &mut SExpr, quotes: &BTreeMap<Target, String>) {
    if let Expr::Sugar(Sugar::Reflect(kind, name)) = &e.node {
        if let Some(quote) = quotes.get(&(*kind, name.clone())) {
            e.node = Expr::Str(quote.clone());
            return;
        }
    }
    e.node.each_child_mut(&mut |c| substitute(c, quotes));
}

// Render each distinct target once. A declaration the prepended prelude brought
// in is not the author's own text, so it is no more quotable than a name the
// file never declares: both are the one error.
fn quote_each(
    source: &str,
    trivia: &TriviaTable,
    prog: &Program,
    targets: &[(Target, Span)],
) -> Result<BTreeMap<Target, String>, TypeError> {
    let items = format_items(source, trivia, prog);
    let mut out = BTreeMap::new();
    for (target, span) in targets {
        if out.contains_key(target) {
            continue;
        }
        let (kind, name) = target;
        let start = declared_at(prog, *kind, name).ok_or_else(|| {
            ErrKind::ReflectUnknownTarget {
                decl: kind.as_str().to_string(),
                name: name.clone(),
            }
            .at(*span)
        })?;
        let quote = items.get(&start).ok_or_else(|| {
            let msg = format!(
                "`{name}` is a declaration of this program, but the formatter \
                 printed no item at its span"
            );
            TypeError::InternalInvariant { msg }
        })?;
        out.insert(target.clone(), quote.trim_end().to_string());
    }
    Ok(out)
}

// Where the named declaration starts, or `None` when the file declares no such
// thing in that form. A declaration before `prelude_end` came from the prepended
// prelude rather than the author's file, so it does not count as one.
fn declared_at(prog: &Program, kind: ReflectKind, name: &str) -> Option<usize> {
    let own = |span: Span| (span.start >= prog.prelude_end).then_some(span.start);
    match kind {
        ReflectKind::Fn => prog
            .fns
            .iter()
            .find(|d| d.name == name)
            .and_then(|d| own(d.span)),
        ReflectKind::Type => prog
            .types
            .iter()
            .find(|d| d.name == name)
            .and_then(|d| own(d.span)),
    }
}
