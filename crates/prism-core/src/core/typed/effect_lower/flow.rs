//! Typed interprocedural thunk-effect flow.
//!
//! A stream combinator returns a thunk whose body performs effects only once
//! forced, so the free-monad escape analysis would push the whole program into
//! monadic mode. Instead the active evidence is threaded to each thunk at its
//! force site, which needs, for every function, the op signature of the thunk
//! it returns (`ret`) and of each thunk-valued parameter (`param`). `ret` reads
//! only the latent map, but a parameter's signature flows from its call sites,
//! whose arguments may themselves be parameters, so the two are solved
//! together as one fixpoint.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use super::super::{
    CoreQuantifier, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue,
    TypedValueKind,
};
use super::latent::{latent, Latent, MaskOp};
use super::peel;
use super::walk::each_value;
use crate::types::ty::EffRow;

/// The op set a thunk performs when forced (mask-aware, like `latent`).
pub type Sig = BTreeSet<MaskOp>;
/// Signatures of the thunk-valued variables in scope.
pub type Loc = BTreeMap<Sym, Sig>;

#[derive(Debug)]
pub struct ThunkFlow {
    pub ret: BTreeMap<Sym, Sig>,
    pub param: BTreeMap<Sym, Vec<Sig>>,
}

#[must_use]
pub fn analyze(fns: &[TypedCoreFn], lat: &Latent) -> ThunkFlow {
    let mut flow = ThunkFlow {
        ret: fns.iter().map(|f| (f.name(), Sig::new())).collect(),
        param: fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect(),
    };
    loop {
        let mut upd: BTreeMap<Sym, Vec<Sig>> = fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect();
        let mut ret = BTreeMap::new();
        for f in fns {
            let loc = param_loc(f, &flow);
            ret.insert(f.name(), props(f.body(), &loc, lat, &flow, &mut upd));
        }
        // `ret`/`upd` are rebuilt each pass from the same function list, so
        // they carry the same key sets as `flow.ret`/`flow.param`. BTreeMaps
        // with equal keys iterate in the same order, so zipping their values
        // aligns each function's accumulated signature with its freshly
        // computed one without a fallible lookup.
        let mut changed = false;
        for (slot, new) in flow.ret.values_mut().zip(ret.values()) {
            changed |= merge(slot, new);
        }
        for (ps, new) in flow.param.values_mut().zip(upd.values()) {
            for (slot, new) in ps.iter_mut().zip(new) {
                changed |= merge(slot, new);
            }
        }
        if !changed {
            break;
        }
    }
    flow
}

fn merge(into: &mut Sig, from: &Sig) -> bool {
    let before = into.len();
    into.extend(from.iter().copied());
    into.len() != before
}

/// The op signature of a value: a lambda thunk performs the ops latent in its
/// body; a variable carries whatever signature flowed to it.
///
/// Anything else reports nothing here and is rejected by the trackability guard
/// before lowering commits.
#[must_use]
pub fn value_sig(v: &TypedValue, loc: &Loc, lat: &Latent) -> Sig {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => body_sig(c, lat),
        TypedValueKind::Var { name, .. } => loc.get(name).cloned().unwrap_or_default(),
        _ => Sig::new(),
    }
}

/// The op signature of the computation a thunk suspends: what forcing it (and,
/// for a lambda thunk, applying the result) can still perform.
///
/// The same answer [`value_sig`] gives for the value that thunk stands in,
/// asked of a caller that holds the body rather than the value.
#[must_use]
pub fn body_sig(c: &TypedComp, lat: &Latent) -> Sig {
    let body = match c.kind() {
        TypedCompKind::Lam(_, b) => b.as_ref(),
        _ => c,
    };
    let mut s = Sig::new();
    latent(body, lat, &mut s);
    s
}

/// The thunk signatures a declaration's body starts from: one entry per
/// thunk-valued parameter, carrying what flowed into that slot.
///
/// Seeding a scope any other way would let the two solvers and the rewrite
/// disagree about what a parameter performs.
pub fn param_loc(f: &TypedCoreFn, flow: &ThunkFlow) -> Loc {
    f.params()
        .iter()
        .map(TypedBinder::name)
        .zip(flow.param.get(&f.name()).into_iter().flatten().cloned())
        .collect()
}

/// Whether any effectful thunk escapes into a position the rewrite cannot
/// thread evidence to.
///
/// Those positions are: buried in a constructor or tuple (extracted later by a
/// `case` the flow does not follow), or handed to a dynamic application or
/// effect op (whose callee is not a statically known function).
///
/// When this holds the program is not evidence-eligible and falls back to the
/// free monad.
#[must_use]
pub fn escapes(fns: &[TypedCoreFn], lat: &Latent, flow: &ThunkFlow) -> bool {
    !escaping_fns(fns, lat, flow).is_empty()
}

/// The functions whose body lets an effectful thunk escape untrackably (the
/// per-function witnesses of [`escapes`]). Local monadification seeds its
/// monadic region from these.
pub fn escaping_fns(fns: &[TypedCoreFn], lat: &Latent, flow: &ThunkFlow) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| esc(f.body(), &param_loc(f, flow), lat, flow))
        .map(TypedCoreFn::name)
        .collect()
}

// An effectful thunk buried inside a constructor or tuple (a top-level thunk
// value is not buried: it is tracked wherever it flows).
fn buried(v: &TypedValue, loc: &Loc, lat: &Latent) -> bool {
    match &peel(v).kind {
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => fields.iter().any(|f| {
            declared_thunk_escape(f) || !value_sig(f, loc, lat).is_empty() || buried(f, loc, lat)
        }),
        TypedValueKind::UnboxedRecord(fields) => fields.iter().any(|(_, f)| {
            declared_thunk_escape(f) || !value_sig(f, loc, lat).is_empty() || buried(f, loc, lat)
        }),
        _ => false,
    }
}

// A callback hidden in data can later be recovered only through a pattern, and
// the flow analysis intentionally does not invent a signature for pattern
// fields. Its stored witness is therefore authoritative even when the concrete
// lambda performs less: a pure thunk widened to `! {Log}` still has to be
// called at the `Log` convention after extraction. Representation wrappers are
// evidence for that widening, so inspect their targets before following their
// operands. A free open row stays opaque for the same reason: it stands for
// effects chosen elsewhere. Only a row the stored function itself quantifies
// is transparent, because each force site instantiates it in the open.
fn declared_thunk_escape(value: &TypedValue) -> bool {
    effectful_thunk_type(value.ty())
        || match value.kind() {
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::NewtypeRepr { value: inner, .. } => declared_thunk_escape(inner),
            _ => false,
        }
}

fn effectful_thunk_type(ty: &CoreType) -> bool {
    let CoreType::Thunk(outer) = ty else {
        return false;
    };
    if row_claims_effects(outer.effects(), &[]) {
        return true;
    }
    let CoreType::Function(function) = outer.result() else {
        return false;
    };
    row_claims_effects(function.body().effects(), function.quantifiers())
}

// Whether a stored thunk's row is a claim the flow must honor. A concrete
// label is a declared widening: the extracted thunk must be called at that
// convention even when the lambda inside performs less. A free variable or an
// existential stands for effects someone else chose, so it is the same
// unknown claim. A row variable the function itself quantifies is neither: it
// is polymorphism the caller instantiates, visible at every use site.
fn row_claims_effects(row: &EffRow, quantifiers: &[CoreQuantifier]) -> bool {
    match row {
        EffRow::Empty => false,
        EffRow::Extend(..) | EffRow::Exist(_) => true,
        EffRow::Var(v) => !quantifiers
            .iter()
            .any(|q| matches!(q, CoreQuantifier::Row(r) if r == v)),
    }
}

fn esc(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match c.kind() {
        TypedCompKind::Return(v) => buried(v, loc, lat) || in_thunk(v, loc, lat, flow),
        TypedCompKind::Call { args, .. } => args
            .iter()
            .any(|a| buried(a, loc, lat) || in_thunk(a, loc, lat, flow)),
        TypedCompKind::App { args, .. } | TypedCompKind::Do { args, .. } => args.iter().any(|a| {
            declared_thunk_escape(a) || !value_sig(a, loc, lat).is_empty() || buried(a, loc, lat)
        }),
        TypedCompKind::Bind(m, x, n) => {
            esc(m, loc, lat, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), result_sig(m, loc, lat, flow));
                esc(n, &loc2, lat, flow)
            }
        }
        TypedCompKind::If(_, t, e) => esc(t, loc, lat, flow) || esc(e, loc, lat, flow),
        TypedCompKind::Case(_, arms) => arms.iter().any(|(_, b)| esc(b, loc, lat, flow)),
        TypedCompKind::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(p.name(), Sig::new());
            }
            esc(b, &loc2, lat, flow)
        }
        TypedCompKind::Mask(_, b) => esc(b, loc, lat, flow),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            esc(body, loc, lat, flow)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| esc(rb, loc, lat, flow))
                || ops.arms().iter().any(|op| esc(op.body(), loc, lat, flow))
        }
        _ => {
            let mut found = false;
            each_value(c, &mut |v| found |= in_thunk(v, loc, lat, flow));
            found
        }
    }
}

// Recurse into a thunk's own body looking for escapes there.
fn in_thunk(v: &TypedValue, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            if let TypedCompKind::Lam(ps, b) = c.kind() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(p.name(), Sig::new());
                }
                esc(b, &loc2, lat, flow)
            } else {
                esc(c, loc, lat, flow)
            }
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            fields.iter().any(|f| in_thunk(f, loc, lat, flow))
        }
        TypedValueKind::UnboxedRecord(fields) => {
            fields.iter().any(|(_, f)| in_thunk(f, loc, lat, flow))
        }
        _ => false,
    }
}

/// The signature of the thunk a computation returns, in a context where `loc`
/// gives the signatures of the thunk-valued variables in scope.
///
/// Read-only twin of `props`'s result path, used by the rewrite to track
/// let-bound thunks.
#[must_use]
pub fn result_sig(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Sig {
    match c.kind() {
        TypedCompKind::Return(v) => value_sig(v, loc, lat),
        TypedCompKind::Call { callee, .. } => flow.ret.get(callee).cloned().unwrap_or_default(),
        TypedCompKind::Bind(m, x, n) => {
            let rm = result_sig(m, loc, lat, flow);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            result_sig(n, &loc2, lat, flow)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = result_sig(t, loc, lat, flow);
            merge(&mut s, &result_sig(e, loc, lat, flow));
            s
        }
        TypedCompKind::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &result_sig(b, loc, lat, flow));
            }
            s
        }
        _ => Sig::new(),
    }
}

// Full traversal: thread the local thunk-signature environment, record the
// signature each call site demands of its callee's parameters, and return the
// signature of the value this computation ultimately returns.
fn props(
    c: &TypedComp,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) -> Sig {
    match c.kind() {
        TypedCompKind::Return(v) => {
            visit_value(v, loc, lat, flow, upd);
            value_sig(v, loc, lat)
        }
        TypedCompKind::Call { callee, args, .. } => {
            for (i, a) in args.iter().enumerate() {
                visit_value(a, loc, lat, flow, upd);
                if let Some(slots) = upd.get_mut(callee) {
                    if let Some(slot) = slots.get_mut(i) {
                        merge(slot, &value_sig(a, loc, lat));
                    }
                }
            }
            flow.ret.get(callee).cloned().unwrap_or_default()
        }
        TypedCompKind::Bind(m, x, n) => {
            let rm = props(m, loc, lat, flow, upd);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            props(n, &loc2, lat, flow, upd)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = props(t, loc, lat, flow, upd);
            merge(&mut s, &props(e, loc, lat, flow, upd));
            s
        }
        TypedCompKind::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &props(b, loc, lat, flow, upd));
            }
            s
        }
        TypedCompKind::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(p.name(), Sig::new());
            }
            props(b, &loc2, lat, flow, upd);
            Sig::new()
        }
        TypedCompKind::App { callee, args, .. } => {
            props(callee, loc, lat, flow, upd);
            for a in args {
                visit_value(a, loc, lat, flow, upd);
            }
            Sig::new()
        }
        TypedCompKind::Mask(_, b) => props(b, loc, lat, flow, upd),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            props(body, loc, lat, flow, upd);
            if let Some(rb) = return_body {
                props(rb, loc, lat, flow, upd);
            }
            for op in ops.arms() {
                props(op.body(), loc, lat, flow, upd);
            }
            Sig::new()
        }
        _ => {
            each_value(c, &mut |v| visit_value(v, loc, lat, flow, upd));
            Sig::new()
        }
    }
}

fn visit_value(
    v: &TypedValue,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            if let TypedCompKind::Lam(ps, b) = c.kind() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(p.name(), Sig::new());
                }
                props(b, &loc2, lat, flow, upd);
            } else {
                props(c, loc, lat, flow, upd);
            }
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for f in fields {
                visit_value(f, loc, lat, flow, upd);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, f) in fields {
                visit_value(f, loc, lat, flow, upd);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::core::typed::{CompSig, CoreFnSig};
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::*;

    fn callback(row: EffRow) -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(CoreType::Source(Type::Unit), row),
            ))),
            EffRow::Empty,
        )))
    }

    // A row variable bound by the stored function's own quantifiers: the
    // caller chooses the row at each instantiation, so the thunk claims no
    // effects of its own.
    fn poly_callback(row: EffRow) -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                vec![CoreQuantifier::Row(Sym::new("e"))],
                Vec::new(),
                CompSig::new(CoreType::Source(Type::Unit), row),
            ))),
            EffRow::Empty,
        )))
    }

    #[test]
    fn stored_thunk_witnesses_make_dynamic_uses_opaque() {
        assert!(!effectful_thunk_type(&callback(EffRow::Empty)));
        assert!(effectful_thunk_type(&callback(EffRow::singleton("Log"))));
        assert!(effectful_thunk_type(&callback(EffRow::Var(Sym::new("e")))));
        assert!(!effectful_thunk_type(&poly_callback(EffRow::Var(
            Sym::new("e")
        ))));
        assert!(effectful_thunk_type(&CoreType::Thunk(Box::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Log"))
        ))));

        let local = TypedValue::new(
            callback(EffRow::Empty),
            TypedValueKind::Var {
                name: Sym::new("quiet"),
                instantiation: Vec::new(),
            },
        );
        let widened = TypedValue::new(
            callback(EffRow::singleton("Log")),
            TypedValueKind::Reinterpret(Box::new(local)),
        );
        assert!(declared_thunk_escape(&widened));
    }
}
