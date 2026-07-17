//! Duplicate-definition detection over the one canonical behavior hash.
//!
//! Two distinct definitions that elaborate to the same content address (what
//! `dump dupes` reports and the store commits) compute the same thing under two
//! names. This module turns that observation into diagnostics: a *clone group* is
//! a set of the user's own definitions sharing a hash, and a *stdlib
//! reimplementation* is a user definition whose hash matches a standard-library
//! function's. Both reuse [`hash_program`], never a second hasher, so a finding
//! is exactly a collision in the same identity regime everything else agrees on.
//!
//! Scope follows the surface lints: only definitions authored in the program's
//! own source are considered (the prepended prelude and any imported module sit
//! before `user_start`), so a build never flags the library it stands on. A user
//! definition that already *is* a standard-library function of the same name and
//! behavior is never a reimplementation, so compiling the standard library itself
//! produces no stdlib findings without any special-casing.

use std::collections::BTreeMap;

use marginalia::Span;

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, Core, Digest, Hashes};
use crate::error::{ErrKind, Error, SourceMap};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::tc::{Checked, Warning, WarningOrigin};

use super::hash_meta;

/// Which duplicate analyses a run wants, derived from the two independent
/// severity knobs (both off means the caller never invokes [`findings`]).
#[derive(Clone, Copy, Debug)]
pub(super) struct Want {
    /// Group the user's own definitions that share a behavior hash.
    pub clone: bool,
    /// Flag a user definition that reimplements a standard-library function.
    pub stdlib: bool,
}

/// One duplicate-definition diagnostic, renderable as a warning or (under strict
/// mode) a hard error. Both faces share one message, drawn from the [`ErrKind`]
/// catalogue, so warn and strict never drift.
pub(super) enum Finding {
    /// Two or more of the user's definitions share a behavior hash. `anchor` is
    /// the definition the diagnostic points at (the earliest in source).
    Clone {
        anchor: Sym,
        span: Span,
        names: Vec<String>,
    },
    /// A user definition realizes the same behavior as a standard-library
    /// function, which should be called instead of reimplemented.
    Stdlib {
        anchor: Sym,
        span: Span,
        name: String,
        stdlib: String,
    },
}

impl Finding {
    const fn span(&self) -> Span {
        match self {
            Self::Clone { span, .. } | Self::Stdlib { span, .. } => *span,
        }
    }

    const fn anchor(&self) -> Sym {
        match self {
            Self::Clone { anchor, .. } | Self::Stdlib { anchor, .. } => *anchor,
        }
    }

    /// Whether this finding is a standard-library reimplementation (governed by
    /// `warn_stdlib_dupes`) rather than an own-clone group (governed by
    /// `warn_dupes`).
    pub(super) const fn is_stdlib(&self) -> bool {
        matches!(self, Self::Stdlib { .. })
    }

    fn kind(&self) -> ErrKind {
        match self {
            Self::Clone { names, .. } => ErrKind::DuplicateBehavior {
                names: names
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", "),
            },
            Self::Stdlib { name, stdlib, .. } => ErrKind::RedundantStdlibDef {
                name: name.clone(),
                stdlib: stdlib.clone(),
            },
        }
    }

    /// The non-fatal face (warn mode). Anchored on the definition so a semantic
    /// cache hit re-locates it in the reformatted source.
    pub(super) fn warning(&self) -> Warning {
        Warning {
            span: self.span(),
            msg: self.kind().to_string(),
            origin: WarningOrigin::Decl(self.anchor()),
        }
    }

    /// The fatal face (strict mode): the same message with its declaration-family
    /// E-code and a source caret.
    pub(super) fn into_error(self) -> Error {
        let span = self.span();
        Error::Type(self.kind().at(span))
    }
}

/// Every duplicate-definition finding for `program`, in source order.
///
/// `core` is the pre-optimizer elaborated Core (the identity surface), and
/// `stdlib_defs` the standard library's per-definition behavior hashes; both are
/// hashed under the same scheme, so a match is a true behavioral collision.
pub(super) fn findings(
    src: &str,
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &Core,
    stdlib_defs: &Hashes,
    want: Want,
) -> Vec<Finding> {
    let user_start = SourceMap::new(src).prelude_len();
    let mut user: Vec<(Sym, Span)> = program
        .fns
        .iter()
        .filter(|d| d.span.start >= user_start)
        .map(|d| (Sym::new(&d.name), d.span))
        .collect();
    user.sort_by_key(|(_, span)| span.start);
    if user.is_empty() {
        return Vec::new();
    }

    let hashes = hash_program(
        core,
        &hash_meta(checked, &borrow_sigs(program), &fip_annots(program)),
    );

    // Reverse index of stdlib behavior hashes to the lexically first name that
    // realizes each, so a reimplementation names one stable suggestion.
    let mut stdlib_by_hash: BTreeMap<&str, &str> = BTreeMap::new();
    if want.stdlib {
        for (name, digest) in stdlib_defs {
            stdlib_by_hash
                .entry(digest.as_str())
                .and_modify(|first| {
                    if name.as_str() < *first {
                        *first = name.as_str();
                    }
                })
                .or_insert_with(|| name.as_str());
        }
    }

    let mut out = Vec::new();
    let mut groups: BTreeMap<&str, Vec<(Sym, Span)>> = BTreeMap::new();
    for (sym, span) in &user {
        let Some(digest) = hashes.get(sym) else {
            continue;
        };
        // A definition that already is the standard library's own function of this
        // exact name and behavior is not a reimplementation of a differently-named
        // one: it is the library itself (self-compile) or a redundant identical
        // redefinition. Never flag it, so compiling the stdlib stays silent.
        let is_stdlib_itself = stdlib_defs.get(sym).map(Digest::as_str) == Some(digest.as_str());
        // Matching a *different* stdlib name is a reimplementation; that message
        // supersedes the plain clone-group one for this definition. `stdlib_by_hash`
        // is empty unless `want.stdlib`, so this branch is skipped when off.
        if !is_stdlib_itself {
            if let Some(stdlib) = stdlib_by_hash.get(digest.as_str()) {
                out.push(Finding::Stdlib {
                    anchor: *sym,
                    span: *span,
                    name: sym.as_str().to_string(),
                    stdlib: (*stdlib).to_string(),
                });
                continue;
            }
        }
        if want.clone {
            groups
                .entry(digest.as_str())
                .or_default()
                .push((*sym, *span));
        }
    }

    // `user` is span-sorted, so each group's first member is its earliest.
    for members in groups.into_values() {
        if members.len() < 2 {
            continue;
        }
        let (anchor, span) = members[0];
        let mut names: Vec<String> = members
            .iter()
            .map(|(n, _)| n.as_str().to_string())
            .collect();
        names.sort();
        out.push(Finding::Clone {
            anchor,
            span,
            names,
        });
    }
    out.sort_by_key(Finding::span_start);
    out
}

impl Finding {
    const fn span_start(&self) -> usize {
        self.span().start
    }
}
