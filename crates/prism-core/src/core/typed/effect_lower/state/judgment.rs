//! The clause judgment: how each handler arm uses its continuation, and what
//! that makes the handler.
//!
//! A handler is judged one arm at a time. An arm's class decides which channel
//! its operation threads through and how the handle site lowers it; the
//! handler's class is what its arms agree on. Every verdict is read off the
//! neutral erased clone through the shared shape predicates, so the judgment
//! adds no traversal of its own.

use crate::core::cbpv::HandleOp;
use crate::core::effect_shape::ResumeUse;

use super::uniformity::{folds_op, is_take};
use super::{
    direct_kind, free_comp_vars, is_fold, is_id_transformer, is_state_transformer, passes_return,
    unit_source, FoldAKind, Latent, Sym, TypedBinder, TypedComp, TypedCompKind, TypedHandleOp,
};

/// How one clause uses its continuation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ClauseClass {
    /// Resumes once, in tail position, without performing its own operation
    /// again: a direct call that returns into the performer. It leaves the
    /// accumulator alone where one is threaded through it, so what it resumes
    /// with classifies it as a folding clause's tail does, where that is
    /// something the classifier reads.
    Direct(Option<FoldAKind>),
    /// A state transformer `\(acc) -> ..` that resumes once with the next
    /// accumulator.
    Fold(FoldAKind),
    /// A parameter-passing clause that re-emits and resumes on one branch and
    /// drops the continuation on the other.
    Take,
    /// Resumes once, in tail position, and performs its own operation again: a
    /// source that threads into the outer evidence.
    Forward,
    /// Never resumes: the performer's continuation is discarded and the handle
    /// site answers with the arm's own value.
    Abort,
    /// Needs the continuation as a value: it resumes more than once, lets the
    /// resumption escape, or resumes from inside a thunk. No parameter carries
    /// that, so the operation is reified into a cell and the clause is handed
    /// the queue standing for the rest of the performer.
    Reified,
}

/// What a whole handler is, once every arm is judged.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HandleClass {
    /// Every arm folds and the return clause is a state transformer;
    /// `transforms` when that transformer is not the identity, so the loop's
    /// answer is the producer's value rather than the accumulator. One arm may
    /// instead stop the fold: `abort` names it, and its clause answers with the
    /// handle's own result rather than the next accumulator.
    Fold {
        transforms: bool,
        abort: Option<Sym>,
    },
    /// One take arm.
    Take,
    /// One forwarding arm with an identity return clause.
    Forward,
    /// Direct and abort arms only, with at most one abort.
    Direct { abort: Option<Sym> },
    /// At least one arm needs its continuation as a value, so the whole handler
    /// drives cells: every arm is answered from the same queue, and an arm that
    /// would have threaded a parameter resumes through the queue instead.
    Reified,
}

/// A handler judged per arm.
#[derive(Debug)]
pub struct HandleJudgment {
    pub class: HandleClass,
    /// Each arm's operation and class, in arm order.
    pub arms: Vec<(Sym, ClauseClass)>,
}

/// Judge one arm from the neutral classifier's verdict on its erased clone.
///
/// # Errors
///
/// Why the arm cannot be threaded, naming the arm.
pub(super) fn judge(
    arm: &TypedHandleOp,
    erased: &HandleOp,
    resume: ResumeUse,
    latent: &Latent,
    widen: bool,
    reify: bool,
) -> Result<ClauseClass, String> {
    if let Some(kind) = is_fold(erased, resume, widen) {
        return Ok(ClauseClass::Fold(kind));
    }
    if is_take(arm, latent) {
        return Ok(ClauseClass::Take);
    }
    if resume.tail {
        return Ok(if folds_op(arm.body(), arm.name(), latent) {
            ClauseClass::Forward
        } else {
            ClauseClass::Direct(direct_kind(erased, resume, widen))
        });
    }
    let resumes = free_comp_vars(arm.body()).contains(&arm.resume().name());
    if !resumes {
        return Ok(ClauseClass::Abort);
    }
    if reify {
        return Ok(ClauseClass::Reified);
    }
    let how = if resume.multishot {
        "more than once or lets it escape"
    } else if resume.in_thunk {
        "inside a thunk"
    } else {
        "off the tail"
    };
    Err(format!("`{}` resumes {how}", arm.name().as_str()))
}

/// Classify every arm of a handle on its own, before the handler's class is
/// decided from them.
///
/// # Errors
/// The refusing arm shape, in the words the tier explainer shows.
pub(super) fn judge_arms(
    h: &TypedComp,
    latent: &Latent,
    widen: bool,
    reify: bool,
) -> Result<Vec<(Sym, ClauseClass)>, String> {
    let TypedCompKind::Handle { ops: clauses, .. } = h.kind() else {
        return Err("not a handle".into());
    };
    // One erased clone per handle, so every clause-shape question is answered
    // from one neutral representation.
    let erased = clauses.clone().erase();
    let arms: Vec<(Sym, ClauseClass)> = clauses
        .arms()
        .iter()
        .zip(erased.iter_with_use())
        .map(|(arm, (clause, resume))| {
            Ok((
                arm.name(),
                judge(arm, clause, resume, latent, widen, reify)?,
            ))
        })
        .collect::<Result<_, String>>()?;
    if arms.is_empty() {
        return Err("a handler with no arm".into());
    }
    Ok(arms)
}

/// Judge a handle expression, or say why its arms do not agree on a class this
/// engine lowers.
///
/// # Errors
/// The refusing arm or handler shape, in the words the tier explainer shows.
pub fn judge_handle(
    h: &TypedComp,
    latent: &Latent,
    widen: bool,
    reify: bool,
) -> Result<HandleJudgment, String> {
    let TypedCompKind::Handle {
        ops: clauses,
        return_binder,
        return_body,
        ..
    } = h.kind()
    else {
        return Err("not a handle".into());
    };
    let arms = judge_arms(h, latent, widen, reify)?;
    // One reified arm makes the whole handler reified: the queue answers every
    // arm of it, so an arm that could have threaded a parameter on its own has
    // no say in the handler's class.
    if arms.iter().any(|(_, class)| *class == ClauseClass::Reified) {
        return Ok(HandleJudgment {
            class: HandleClass::Reified,
            arms,
        });
    }
    let named = || {
        arms.iter()
            .map(|(op, _)| format!("`{}`", op.as_str()))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let rb = return_body.as_deref().map(|b| b.clone().erase());
    let rv = return_binder.as_ref().map(TypedBinder::name);
    // An arm that stops the fold answers the handle directly, so it is a fold
    // handler's arm as much as a folding one is: both are transformers over the
    // accumulator, and only the answer differs.
    let stops: Vec<Sym> = arms
        .iter()
        .filter(|(_, class)| *class == ClauseClass::Abort)
        .map(|(op, _)| *op)
        .collect();
    let folds = arms
        .iter()
        .filter(|(_, class)| matches!(class, ClauseClass::Fold(_)))
        .count();
    let class = if folds > 0 && (widen || stops.is_empty()) && folds + stops.len() == arms.len() {
        // A fold's return clause is a state transformer. The identity
        // transformer is the writer special case; a get-style `\s -> r` is the
        // general one, applied to the final accumulator.
        if !rb.as_ref().is_some_and(is_state_transformer) {
            return Err(format!(
                "a fold of {} whose return clause is not a state transformer",
                named()
            ));
        }
        // The stopping arm is unwrapped once at the handle site, which has room
        // for one payload, and it must answer the accumulator it is handed.
        let abort = match stops.as_slice() {
            [] => None,
            [op] => Some(*op),
            _ => return Err(format!("a fold of {} with two stopping arms", named())),
        };
        if let Some(op) = abort.filter(|op| {
            !clauses
                .arms()
                .iter()
                .find(|arm| arm.name() == *op)
                .is_some_and(|arm| is_state_transformer(&arm.body().clone().erase()))
        }) {
            return Err(format!(
                "a fold stopped by `{}`, whose arm is not a state transformer",
                op.as_str()
            ));
        }
        HandleClass::Fold {
            transforms: !rb.as_ref().is_some_and(is_id_transformer),
            abort,
        }
    } else if let [(_, ClauseClass::Take)] = arms.as_slice() {
        HandleClass::Take
    } else if let [(_, ClauseClass::Forward)] = arms.as_slice() {
        // A re-emitting forwarder threads the accumulator straight into the
        // outer evidence, so its return clause must pass the source's final
        // value through unchanged.
        if !passes_return(
            rv,
            rb.as_ref(),
            widen && unit_source(return_binder.as_ref()),
        ) {
            return Err(if rb.is_none() {
                format!("a forwarder of {} with no return clause", named())
            } else {
                format!(
                    "a forwarder of {} whose return clause is not the identity",
                    named()
                )
            });
        }
        HandleClass::Forward
    } else if arms
        .iter()
        .all(|(_, class)| matches!(class, ClauseClass::Direct(_) | ClauseClass::Abort))
    {
        // One abort per handler: the handle site unwraps one done payload.
        let mut aborts = arms
            .iter()
            .filter(|(_, class)| *class == ClauseClass::Abort)
            .map(|(op, _)| *op);
        let abort = aborts.next();
        if aborts.next().is_some() {
            return Err(format!("a handler of {} with two aborting arms", named()));
        }
        HandleClass::Direct { abort }
    } else {
        let shapes: Vec<String> = arms
            .iter()
            .map(|(op, class)| format!("`{}` {class:?}", op.as_str()))
            .collect();
        return Err(format!(
            "arms of one handler disagree: {}",
            shapes.join(", ")
        ));
    };
    Ok(HandleJudgment { class, arms })
}
