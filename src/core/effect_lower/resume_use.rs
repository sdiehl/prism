//! The canonical resume-usage classification of a handler clause.
//!
//! How a clause uses its resumption decides which effect-lowering tier may
//! fire: the evidence path needs a sole tail `resume(v)`, variable erasure
//! must know whether a resumption can run more than once, and the analysis
//! pass must know whether a resumption escapes into a thunk that outlives the
//! clause. Each of those facts used to be re-derived by its consumer with a
//! private scan of the clause body; this module is now the single home. The
//! facts are computed once, when a `CheckedHandler` is constructed (and
//! recomputed whenever a Core-to-Core pass rebuilds one), and every consumer
//! reads the stored value, so a stale classification is unrepresentable: the
//! constructor is the only writer.
//!
//! The classification is a cost fact, not a semantic one: it selects among
//! observationally identical lowerings. It therefore never enters the content
//! hash, the Core JSON, or the store codec, all of which encode the clause
//! fields explicitly and reconstruct handlers through `CheckedHandler::new`.

use std::collections::BTreeSet;

use crate::sym::Sym;

use super::super::cbpv::{Comp, HandleOp, Value};
use super::diagnostics::DriftLog;
use super::evidence::{resume_set, strip_resume};
use super::walk::{each_subcomp, each_value, thunks_in_value};

/// How a handler clause uses its resumption.
///
/// Three independent facts, each the exact predicate one lowering consumer
/// keys on; storing them separately (not as a lattice) keeps every consumer's
/// behavior identical to the scan it replaced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResumeUse {
    /// The clause's only use of the resumption is a single tail `resume(v)`:
    /// the eligibility test for the evidence fast path (the same matcher that
    /// performs the strip rewrite, so the two can never disagree).
    pub tail: bool,
    /// The resumption escapes into a value or is called more than once, so the
    /// clause may resume repeatedly: variable erasure must keep `var` cells
    /// out of its scope. This gate is not a textual occurrence count: a
    /// `resume` captured once into a closure that is later applied twice,
    /// stored in a constructor and re-applied, or rebound to an alias is
    /// invoked more than once while occurring exactly once, so counting
    /// occurrences alone fails open (erasure would install a shared cell where
    /// pure State demands per-resumption copies). A clause is single-shot only
    /// when every occurrence of its `resume` is the head of a direct `force`
    /// outside any nested thunk, and there is at most one such head; any other
    /// occurrence is an escape. The parameter-passing answer lambda a clause
    /// returns (`get(u,k) => \s -> k(s)(s)` reaches Core as
    /// `Return(Thunk(Lam(..)))`) is peeled before scanning: the handler
    /// protocol applies each answer function it threads exactly once, so a
    /// `resume` under that wrapper alone is not a capture. Occurrences under
    /// any other thunk are: nothing pins how many times such a closure is
    /// forced.
    pub multishot: bool,
    /// The resumption occurs free inside a thunk, which may be forced later:
    /// the analysis pass treats such a handler as letting open effects escape.
    pub in_thunk: bool,
}

/// Classify one clause. The sole writer of [`ResumeUse`]; called by
/// `CheckedHandler::new` and `CheckedHandler::rebuild`.
pub(crate) fn classify(op: &HandleOp) -> ResumeUse {
    let aliases = resume_set(op.resume);
    // Tail eligibility is the strip matcher itself, run for its verdict only.
    // The quiet drift log keeps classification silent; the evidence tier's own
    // strip call (which builds the rewrite it actually uses) still reports.
    let tail = strip_resume(&op.body, &aliases, &DriftLog::new(true)).is_some();
    // The multishot scan runs on the clause body with its parameter-passing
    // wrappers peeled, exactly as variable erasure historically scanned it.
    let mut body = &op.body;
    loop {
        match body {
            Comp::Lam(_, inner) => body = inner,
            Comp::Return(Value::Thunk(t)) => match t.as_ref() {
                Comp::Lam(_, inner) => body = inner,
                _ => break,
            },
            _ => break,
        }
    }
    let mut calls = 0usize;
    let mut escapes = false;
    scan_resume(body, &aliases, &mut calls, &mut escapes);
    ResumeUse {
        tail,
        multishot: escapes || calls > 1,
        in_thunk: in_thunk(&op.body, op.resume),
    }
}

// Classify every occurrence of a resume alias in `c`: a `Force` head is a
// direct call (counted); a pure rename `Bind(Return(alias), x, n)` extends the
// alias set over `n` (elaboration ANF-normalizes `k(s)(s)` into exactly this
// shape, one rename per application); any other value occurrence, including
// inside a nested thunk, a constructor, or a tuple, is an escape. `each_value`
// visits the values `c` holds directly and `val_uses` descends into them
// (thunks included); sub-computations recurse. The two are disjoint, so no
// occurrence is missed or double-counted.
fn scan_resume(c: &Comp, ks: &BTreeSet<Sym>, calls: &mut usize, escapes: &mut bool) {
    match c {
        Comp::Force(Value::Var(y)) if ks.contains(y) => {
            *calls += 1;
            return;
        }
        Comp::Bind(m, x, n) => {
            if let Comp::Return(Value::Var(y)) = m.as_ref() {
                if ks.contains(y) {
                    let mut inner = ks.clone();
                    inner.insert(*x);
                    scan_resume(n, &inner, calls, escapes);
                    return;
                }
            }
            scan_resume(m, ks, calls, escapes);
            // `x` rebound to a non-alias shadows any alias of the same name.
            if ks.contains(x) {
                let mut inner = ks.clone();
                inner.remove(x);
                scan_resume(n, &inner, calls, escapes);
            } else {
                scan_resume(n, ks, calls, escapes);
            }
            return;
        }
        _ => {}
    }
    each_value(c, &mut |v| {
        if ks.iter().any(|k| val_uses(v, *k) > 0) {
            *escapes = true;
        }
    });
    each_subcomp(c, &mut |sc| scan_resume(sc, ks, calls, escapes));
}

// Whether the resumption occurs free inside any thunk of the clause body: the
// escape the analysis pass keys on (a captured continuation may be forced
// after the handler frame is gone).
fn in_thunk(c: &Comp, resume: Sym) -> bool {
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= crate::core::fv::comp(t).contains(&resume);
        }
    });
    each_subcomp(c, &mut |sc| found |= in_thunk(sc, resume));
    found
}

/// Count occurrences of `Value::Var(x)` inside a value, descending into
/// thunks. The single home for value-level use counting, shared with variable
/// erasure.
pub(super) fn val_uses(v: &Value, x: Sym) -> usize {
    match v {
        Value::Var(y) => usize::from(*y == x),
        Value::Thunk(c) => var_uses(c, x),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().map(|f| val_uses(f, x)).sum(),
        _ => 0,
    }
}

/// Count occurrences of `Value::Var(x)` in a computation (including in
/// thunks). Values (and the thunks they hold, via [`val_uses`]) are counted by
/// `each_value`; sub-computations by `each_subcomp`. The two are disjoint, so
/// no occurrence is double-counted.
pub(super) fn var_uses(c: &Comp, x: Sym) -> usize {
    let mut n = 0;
    each_value(c, &mut |v| n += val_uses(v, x));
    each_subcomp(c, &mut |sc| n += var_uses(sc, x));
    n
}
