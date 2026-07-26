//! Or-pattern expansion.
//!
//! `A | B => e` is one arm per alternative, `A => e` then `B => e`, and the same
//! for an alternation nested inside a constructor argument, tuple, list, or
//! record field: `Bin(Add | Sub, a, b)` becomes two arms. Alternatives are
//! enumerated leftmost-slowest, which is what a backtracking match would try, so
//! overlapping alternatives keep their source order.
//!
//! Expansion runs at the surface-to-core boundary, before the checker, so
//! exhaustiveness and reachability see exactly the arms the alternation denotes
//! and nothing downstream of desugaring ever meets a [`Pattern::Or`].

use std::borrow::Cow;
use std::collections::BTreeSet;

use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{Arm, Pattern, Spanned, S};

// The most arms one source arm may expand to. Alternation in several argument
// positions multiplies, so the expansion is exponential in the nesting depth; a
// program past this bound is refused with a pointed error instead of compiled
// into an unbounded arm list.
const MAX_OR_EXPANSION: usize = 256;

/// Split every alternation in `arms` into separate arms.
///
/// Returns the arms borrowed when none of them alternates, so the common case
/// pays no clone.
///
/// # Errors
/// Fails when the alternatives of one or-pattern bind different names, or when
/// an arm expands past [`MAX_OR_EXPANSION`] arms.
pub(super) fn expand_arms(arms: &[Arm]) -> Result<Cow<'_, [Arm]>, TypeError> {
    if !arms.iter().any(|a| has_or(&a.pat)) {
        return Ok(Cow::Borrowed(arms));
    }
    let mut out = Vec::with_capacity(arms.len());
    for a in arms {
        check_binders(&a.pat)?;
        for (i, mut pat) in expand(&a.pat)?.into_iter().enumerate() {
            // The whole source pattern is what a diagnostic should underline;
            // an alternative on its own is only half of what the user wrote.
            pat.span = a.pat.span;
            out.push(Arm {
                pat,
                guard: a.guard.clone(),
                body: a.body.clone(),
                alt: i > 0,
            });
        }
    }
    Ok(Cow::Owned(out))
}

fn has_or(p: &S<Pattern>) -> bool {
    match &p.node {
        Pattern::Or(_) => true,
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => subs.iter().any(has_or),
        Pattern::Record(_, fields, _) => fields.iter().any(|(_, q)| has_or(q)),
        Pattern::Wild
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => false,
    }
}

fn binders(p: &S<Pattern>, out: &mut BTreeSet<String>) {
    match &p.node {
        Pattern::Var(x) => {
            out.insert(x.clone());
        }
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => {
            for q in subs {
                binders(q, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, q) in fields {
                binders(q, out);
            }
        }
        // Checked separately; a well-formed alternation binds one set, so
        // reading the first alternative names it.
        Pattern::Or(alts) => {
            if let Some(first) = alts.first() {
                binders(first, out);
            }
        }
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => {}
    }
}

// Every alternation in the pattern binds one name set across its alternatives.
// The arm body is shared by all of them, so a name missing from any alternative
// would be unbound on that path.
fn check_binders(p: &S<Pattern>) -> Result<(), TypeError> {
    match &p.node {
        Pattern::Or(alts) => {
            let mut sets = Vec::with_capacity(alts.len());
            for alt in alts {
                check_binders(alt)?;
                let mut names = BTreeSet::new();
                binders(alt, &mut names);
                sets.push(names);
            }
            let Some(first) = sets.first() else {
                return Ok(());
            };
            for (alt, names) in alts.iter().zip(&sets).skip(1) {
                if names != first {
                    let name = first
                        .symmetric_difference(names)
                        .next()
                        .cloned()
                        .unwrap_or_default();
                    return Err(ErrKind::OrPatternBinders { name }.at(alt.span));
                }
            }
            Ok(())
        }
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => subs.iter().try_for_each(check_binders),
        Pattern::Record(_, fields, _) => fields.iter().try_for_each(|(_, q)| check_binders(q)),
        Pattern::Wild
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => Ok(()),
    }
}

// Rebuild `p` once per combination of its sub-patterns' expansions, varying the
// rightmost position fastest so the leftmost alternation stays the outer loop.
fn product<F>(p: &S<Pattern>, subs: &[S<Pattern>], rebuild: F) -> Result<Vec<S<Pattern>>, TypeError>
where
    F: Fn(Vec<S<Pattern>>) -> Pattern,
{
    let mut rows: Vec<Vec<S<Pattern>>> = vec![Vec::with_capacity(subs.len())];
    for sub in subs {
        let choices = expand(sub)?;
        let mut next = Vec::with_capacity(rows.len() * choices.len());
        for row in &rows {
            for choice in &choices {
                let mut r = row.clone();
                r.push(choice.clone());
                next.push(r);
            }
        }
        if next.len() > MAX_OR_EXPANSION {
            return Err(ErrKind::OrPatternTooLarge {
                limit: MAX_OR_EXPANSION,
            }
            .at(p.span));
        }
        rows = next;
    }
    Ok(rows
        .into_iter()
        .map(|r| Spanned {
            id: p.id,
            synth: p.synth,
            node: rebuild(r),
            span: p.span,
        })
        .collect())
}

// Every alternation-free pattern `p` denotes, in the order a match should try
// them.
fn expand(p: &S<Pattern>) -> Result<Vec<S<Pattern>>, TypeError> {
    match &p.node {
        Pattern::Or(alts) => {
            let mut out = Vec::with_capacity(alts.len());
            for alt in alts {
                out.extend(expand(alt)?);
                if out.len() > MAX_OR_EXPANSION {
                    return Err(ErrKind::OrPatternTooLarge {
                        limit: MAX_OR_EXPANSION,
                    }
                    .at(p.span));
                }
            }
            Ok(out)
        }
        Pattern::Ctor(name, subs) => {
            let name = name.clone();
            product(p, subs, move |r| Pattern::Ctor(name.clone(), r))
        }
        Pattern::Tuple(subs) => product(p, subs, Pattern::Tuple),
        Pattern::Record(name, fields, spread) => {
            let subs: Vec<S<Pattern>> = fields.iter().map(|(_, q)| q.clone()).collect();
            let names: Vec<String> = fields.iter().map(|(f, _)| f.clone()).collect();
            let (name, spread) = (name.clone(), *spread);
            product(p, &subs, move |r| {
                Pattern::Record(name.clone(), names.iter().cloned().zip(r).collect(), spread)
            })
        }
        Pattern::Wild
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => Ok(vec![p.clone()]),
    }
}
