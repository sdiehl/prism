//! The HIR lint: an independent proof-checker at the elaboration boundary.
//!
//! Private construction keeps ordinary code from making a malformed HIR; the
//! lint catches mistakes in checking itself (and, later, in HIR-to-HIR
//! transformations). It is proof checking, not proof search: every judgment
//! re-verifies a stored fact against the environment it claims to be about,
//! and it must never grow into a second inference engine. Whole-program
//! properties (fbip, noalloc, replayability, coherence, tier equivalence)
//! stay with their own validators.
//!
//! Scope grows with the migration: today it verifies the resolution family
//! (the facts `CheckedHir` owns). Each further family migrated onto the HIR
//! brings its judgments here.

use std::fmt;

use super::{CheckedHir, NodeRes};
use crate::sym::Sym;
use crate::types::{Checked, Dict};

/// One lint violation: a stored fact that does not check against the
/// environment. Always a compiler bug, never a user error.
#[derive(Debug)]
pub struct HirViolation {
    pub node: u32,
    pub msg: String,
}

impl fmt::Display for HirViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node {}: {}", self.node, self.msg)
    }
}

/// Record one violation against a node, saturating the index into `u32`.
fn push(out: &mut Vec<HirViolation>, node: usize, msg: String) {
    out.push(HirViolation {
        node: u32::try_from(node).unwrap_or(u32::MAX),
        msg,
    });
}

/// Verify one stored dictionary against the instance and class environment.
///
/// A `Global` must name a real instance; a `Super` must name a real class and
/// project a leading superclass field in bounds; `Tuple` components recurse. A
/// `Param` refers to a hidden dictionary parameter of the enclosing constrained
/// function, whose binder is not in per-node scope, so it is deliberately not
/// judged here (judging it would mean re-deriving the function's dict layout,
/// which is inference, not proof checking).
fn check_dict(checked: &Checked, node: usize, d: &Dict, out: &mut Vec<HirViolation>) {
    match d {
        Dict::Param(_) => {}
        Dict::Global(name, ctx) => {
            if !checked.instances.contains_key(&Sym::from(name)) {
                push(
                    out,
                    node,
                    format!("evidence names unknown instance `{name}`"),
                );
            }
            for c in ctx {
                check_dict(checked, node, c, out);
            }
        }
        Dict::Super(inner, class, idx) => {
            match checked.classes.get(&Sym::from(class)) {
                None => push(
                    out,
                    node,
                    format!("superclass projection names unknown class `{class}`"),
                ),
                Some(info) if *idx >= info.supers.len() => push(
                    out,
                    node,
                    format!(
                        "superclass index {idx} out of bounds for `{class}` ({} supers)",
                        info.supers.len()
                    ),
                ),
                Some(_) => {}
            }
            check_dict(checked, node, inner, out);
        }
        Dict::Tuple(comps) => {
            for c in comps {
                check_dict(checked, node, c, out);
            }
        }
    }
}

/// Verify every stored fact against the environment it claims to be about.
///
/// Resolution facts: named constructors must exist, recorded arities must agree
/// with the constructor's declared shape, field indices must be in bounds.
/// Evidence: every dictionary names real instances and classes with in-bounds
/// superclass projections. The lane and zonked-type families are stored but
/// not judged (both are zonked yet legitimately retain unsolved existentials
/// for under-determined sites). Returns every violation rather than the first,
/// so a bug's blast radius is visible at once.
#[must_use]
pub fn lint_hir(hir: &CheckedHir<'_>) -> Vec<HirViolation> {
    let mut out = Vec::new();
    let mut bad = |node: usize, msg: String| push(&mut out, node, msg);
    let check_step = |step: &(String, usize, usize)| -> Option<String> {
        let (ctor, idx, arity) = step;
        let Some(info) = hir.checked.ctors.get(ctor) else {
            return Some(format!("resolution names unknown constructor `{ctor}`"));
        };
        if info.args.len() != *arity {
            return Some(format!(
                "resolution arity {arity} disagrees with `{ctor}`'s declared arity {}",
                info.args.len()
            ));
        }
        if idx >= arity {
            return Some(format!(
                "field index {idx} out of bounds for `{ctor}` (arity {arity})"
            ));
        }
        None
    };
    for (i, fact) in hir.facts.res.iter().enumerate() {
        match fact {
            None => {}
            Some(NodeRes::Field(ctor, idx, arity)) => {
                if let Some(msg) = check_step(&(ctor.clone(), *idx, *arity)) {
                    bad(i, msg);
                }
            }
            Some(NodeRes::UnboxedField(idx, arity)) => {
                if idx >= arity {
                    bad(
                        i,
                        format!("unboxed field index {idx} out of bounds (arity {arity})"),
                    );
                }
            }
            Some(NodeRes::Paths(chains)) => {
                if chains.is_empty() {
                    bad(i, "update-path resolution with no chains".to_string());
                }
                for chain in chains {
                    if chain.is_empty() {
                        bad(i, "update-path chain with no steps".to_string());
                        continue;
                    }
                    for step in chain {
                        if let Some(msg) = check_step(step) {
                            bad(i, msg);
                        }
                    }
                }
            }
        }
    }
    // Evidence family: every recorded dictionary must resolve against the
    // instance and class environment.
    for (i, fact) in hir.facts.evidence.iter().enumerate() {
        if let Some(dicts) = fact {
            for d in dicts {
                check_dict(hir.checked, i, d, &mut out);
            }
        }
    }
    // The REPL override table carries a re-inferred expression's own evidence
    // against fresh NodeIds; judge it by the same dictionary rules. Match the
    // private field directly (the lint is a child module of `hir`).
    if let Some(table) = &hir.evidence_override {
        for (i, fact) in table.iter().enumerate() {
            if let Some(dicts) = fact {
                for d in dicts {
                    check_dict(hir.checked, i, d, &mut out);
                }
            }
        }
    }
    // The lane (fixed numeric) and ty (zonked node type) families are stored
    // but deliberately not judged. Both are zonked (solved existentials
    // substituted) yet not existential-free: an under-determined numeric or
    // node keeps an unsolved existential that numeric defaulting or the
    // elaborator's own use-site filter (`Elab::local_ty`) resolves downstream.
    // Zonk is substitution of solved variables, not a promise that none
    // remain, so existential-freeness is not an invariant to assert here. The
    // substantive structural facts, resolution and evidence, are checked above.
    out
}
