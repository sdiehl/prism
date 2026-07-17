//! The HIR lint: an independent proof-checker at the elaboration boundary.
//!
//! Private construction keeps ordinary code from making a malformed HIR; the
//! lint catches mistakes in checking itself and in HIR-to-HIR transformations.
//! It is proof checking, not proof search: every judgment
//! re-verifies a stored fact against the environment it claims to be about,
//! and it must never grow into a second inference engine. Whole-program
//! properties (fbip, noalloc, replayability, coherence, tier equivalence)
//! stay with their own validators.
//!
//! It verifies the resolution family owned by `CheckedHir`; other fact families
//! remain with their canonical validators.

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
                    push(&mut out, i, msg);
                }
            }
            Some(NodeRes::UnboxedField(idx, arity)) => {
                if idx >= arity {
                    push(
                        &mut out,
                        i,
                        format!("unboxed field index {idx} out of bounds (arity {arity})"),
                    );
                }
            }
            Some(NodeRes::Paths(chains)) => {
                if chains.is_empty() {
                    push(
                        &mut out,
                        i,
                        "update-path resolution with no chains".to_string(),
                    );
                }
                for chain in chains {
                    if chain.is_empty() {
                        push(&mut out, i, "update-path chain with no steps".to_string());
                        continue;
                    }
                    for step in chain {
                        if let Some(msg) = check_step(step) {
                            push(&mut out, i, msg);
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
    // Handler residual family: the marker and fact tables must agree exactly,
    // and both operation lists are canonical, duplicate-free names from the
    // checked effect environment. The forwarded body uses are necessarily a
    // subset of the complete handler-expression residual.
    let handler_len = hir
        .facts
        .handler_nodes
        .len()
        .max(hir.facts.handler_residual.len());
    for i in 0..handler_len {
        let marked = hir.facts.handler_nodes.get(i).copied().unwrap_or(false);
        let residual = hir.facts.handler_residual.get(i).and_then(Option::as_ref);
        match (marked, residual) {
            (true, None) => {
                push(
                    &mut out,
                    i,
                    "handler node is missing its residual fact".to_string(),
                );
            }
            (false, Some(_)) => {
                push(
                    &mut out,
                    i,
                    "residual fact is attached to a non-handler node".to_string(),
                );
            }
            (_, Some(fact)) => {
                let check_operations = |kind: &str, operations: &[Sym]| -> Option<String> {
                    if !operations
                        .windows(2)
                        .all(|pair| pair[0].as_str() < pair[1].as_str())
                    {
                        return Some(format!(
                            "handler {kind} operations are not canonical and duplicate-free"
                        ));
                    }
                    operations
                        .iter()
                        .find(|operation| !hir.checked.eff_ops.contains_key(operation.as_str()))
                        .map(|operation| {
                            format!("handler {kind} names unknown operation `{operation}`")
                        })
                };
                if let Some(msg) = check_operations("forwarded", fact.forwarded_operations()) {
                    push(&mut out, i, msg);
                }
                if let Some(msg) = check_operations("residual", fact.residual_operations()) {
                    push(&mut out, i, msg);
                }
                let check_effects = |kind: &str, effects: &[Sym]| -> Option<String> {
                    if !effects
                        .windows(2)
                        .all(|pair| pair[0].as_str() < pair[1].as_str())
                    {
                        return Some(format!(
                            "handler {kind} effects are not canonical and duplicate-free"
                        ));
                    }
                    effects
                        .iter()
                        .find(|effect| {
                            !hir.checked
                                .eff_ops
                                .values()
                                .any(|info| info.effect_name == **effect)
                                && !crate::tc::is_builtin_effect(effect.as_str())
                        })
                        .map(|effect| format!("handler {kind} names unknown effect `{effect}`"))
                };
                if let Some(msg) = check_effects("forwarded", fact.forwarded_effects()) {
                    push(&mut out, i, msg);
                }
                if let Some(msg) = check_effects("residual", fact.residual_effects()) {
                    push(&mut out, i, msg);
                }
                if let Some(operation) = fact.forwarded_operations().iter().find(|operation| {
                    if fact.residual_operations().contains(operation) {
                        return false;
                    }
                    let effect = hir
                        .checked
                        .eff_ops
                        .get(operation.as_str())
                        .map(|info| info.effect_name);
                    !effect.is_some_and(|effect| fact.residual_effects().contains(&effect))
                }) {
                    push(
                        &mut out,
                        i,
                        format!(
                            "forwarded operation `{operation}` is absent from the handler residual"
                        ),
                    );
                }
                if let Some(effect) = fact
                    .forwarded_effects()
                    .iter()
                    .find(|effect| !fact.residual_effects().contains(effect))
                {
                    push(
                        &mut out,
                        i,
                        format!("forwarded effect `{effect}` is absent from the handler residual"),
                    );
                }
            }
            (false, None) => {}
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
