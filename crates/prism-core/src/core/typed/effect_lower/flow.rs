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

use super::super::verify::VerifyEnv;
use super::super::{
    CoreQuantifier, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue,
    TypedValueKind,
};
use super::latent::{latent, latent_map, Latent, MaskOp};
use super::peel;
use super::walk::each_value;
use crate::types::ty::EffRow;

/// The op set a thunk performs when forced (mask-aware, like `latent`).
pub type Sig = BTreeSet<MaskOp>;
/// Signatures of the thunk-valued variables in scope.
pub type Loc = BTreeMap<Sym, Sig>;

/// The operations a type names, by the effect a row spells to name them.
///
/// The flow follows a thunk from where it is built to where it is forced. A
/// thunk buried in data leaves that path, and the value that comes back out of
/// a pattern carries no flowed signature. Its own type still says what forcing
/// it performs, so under the widened convention the type is the second source
/// of an answer and the force site reads the convention off the value.
///
/// Empty when the route is not consolidated: threading then reaches only
/// where the flow does, so a type-directed answer would promise a convention
/// nothing installs.
#[derive(Debug, Clone, Default)]
pub struct Carriers {
    by_effect: BTreeMap<Sym, BTreeSet<Sym>>,
}

impl Carriers {
    /// No type-directed answer: what every engine but the widened one asks for.
    #[must_use]
    pub fn none() -> Self {
        Self::default()
    }

    /// Every operation the environment declares, keyed by its effect.
    #[must_use]
    pub fn of(env: &VerifyEnv) -> Self {
        let mut by_effect: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
        for (op, sig) in env.operations() {
            by_effect.entry(sig.effect().name).or_default().insert(*op);
        }
        Self { by_effect }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.by_effect.is_empty()
    }

    /// The operations `ty` declares a value of that type performs when forced.
    ///
    /// Only the outermost arrow is read. A collection of carriers is not itself
    /// a carrier: threading evidence into one would ask a parameter that is not
    /// a thunk to take a clause, and what it holds is reached through a pattern,
    /// whose binder carries the buried arrow as its own type.
    #[must_use]
    pub fn sig(&self, ty: &CoreType) -> Sig {
        let CoreType::Thunk(outer) = ty else {
            return Sig::new();
        };
        if self.by_effect.is_empty() {
            return Sig::new();
        }
        let mut s = self.row(outer.effects());
        if let CoreType::Function(function) = outer.result() {
            merge(&mut s, &self.row(function.body().effects()));
        }
        s
    }

    fn row(&self, row: &EffRow) -> Sig {
        row.labels()
            .into_iter()
            .filter_map(|label| self.by_effect.get(&label.name))
            .flatten()
            .map(|id| MaskOp { id: *id, depth: 0 })
            .collect()
    }
}

#[derive(Debug)]
pub struct ThunkFlow {
    pub ret: BTreeMap<Sym, Sig>,
    pub param: BTreeMap<Sym, Vec<Sig>>,
    /// The type-directed answer this flow also honors.
    pub carriers: Carriers,
}

#[must_use]
pub fn analyze(fns: &[TypedCoreFn], lat: &Latent) -> ThunkFlow {
    analyze_with(fns, lat, false, &Carriers::none())
}

/// The flow that also sees evidence carried through lambda-bound locals.
///
/// A returned or passed lambda counts what its body forces from the parameters
/// and locals in scope, not only what its own body performs.
///
/// The state rewrite threads evidence through exactly those positions, so its
/// call-site and return signatures must come from this flow; the other tiers
/// keep the latent-only answer.
#[must_use]
pub fn analyze_in(fns: &[TypedCoreFn], lat: &Latent, carriers: &Carriers) -> ThunkFlow {
    analyze_with(fns, lat, true, carriers)
}

/// The latent map and flow the state engine reads together.
///
/// What a function performs through the thunks its parameters carry is latent
/// in it, since a call that hands it such a thunk performs those operations.
/// What a parameter carries is the flow's answer and what a call performs is
/// the latent map's, so the two are solved to one fixpoint.
#[must_use]
pub fn deep_latent(fns: &[TypedCoreFn], carriers: &Carriers) -> (Latent, ThunkFlow) {
    let by_name: BTreeMap<Sym, &TypedCoreFn> = fns.iter().map(|f| (f.name(), f)).collect();
    let mut lat = latent_map(fns);
    loop {
        let flow = analyze_in(fns, &lat, carriers);
        let seed: Latent = by_name.keys().map(|k| (*k, Sig::new())).collect();
        let next = prism_common::fixpoint::least_fixpoint(seed, |name, cur| {
            let f = by_name[name];
            let mut s = Sig::new();
            latent(f.body(), cur, &mut s);
            performed(f.body(), &param_loc(f, &flow), cur, &flow, &mut s);
            s
        });
        if next == lat {
            return (lat, flow);
        }
        lat = next;
    }
}

fn analyze_with(fns: &[TypedCoreFn], lat: &Latent, deep: bool, carriers: &Carriers) -> ThunkFlow {
    let mut flow = ThunkFlow {
        ret: fns.iter().map(|f| (f.name(), Sig::new())).collect(),
        param: fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect(),
        carriers: carriers.clone(),
    };
    loop {
        let mut upd: BTreeMap<Sym, Vec<Sig>> = fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect();
        let mut ret = BTreeMap::new();
        for f in fns {
            let loc = param_loc(f, &flow);
            ret.insert(f.name(), props(f.body(), &loc, lat, &flow, deep, &mut upd));
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

/// The functions whose body lets an effectful thunk escape untrackably (the
/// per-function witnesses of [`escape_reason`]). Local monadification seeds its
/// monadic region from these.
pub fn escaping_fns(fns: &[TypedCoreFn], lat: &Latent, flow: &ThunkFlow) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| esc(f.body(), &param_loc(f, flow), lat, flow).is_some())
        .map(TypedCoreFn::name)
        .collect()
}

/// The first function that lets an effectful thunk escape into a position the
/// rewrite cannot thread evidence to, and the shape that let it.
///
/// Those positions are: buried in a constructor or tuple, extracted later by a
/// `case` the flow does not follow, or handed to a dynamic application or an
/// effect operation, whose callee is not a statically known function. A program
/// with one cannot be threaded by value.
///
/// The shape travels with the name because a decline that says only that
/// something escaped is one undifferentiated wall, and these shapes want
/// different answers.
#[must_use]
pub fn escape_reason(
    fns: &[TypedCoreFn],
    lat: &Latent,
    flow: &ThunkFlow,
    widen: bool,
) -> Option<(Sym, &'static str)> {
    // Under the widened convention a thunk's own type says which evidence it
    // takes, so a position the flow cannot follow is no longer a position the
    // rewrite cannot reach: the force site reads the convention off the value.
    if widen {
        return None;
    }
    fns.iter()
        .find_map(|f| esc(f.body(), &param_loc(f, flow), lat, flow).map(|why| (f.name(), why)))
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

fn esc(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Option<&'static str> {
    match c.kind() {
        TypedCompKind::Return(v) => buried(v, loc, lat)
            .then_some("returns a thunk buried in data")
            .or_else(|| in_thunk(v, loc, lat, flow)),
        TypedCompKind::Call { args, .. } => args.iter().find_map(|a| {
            buried(a, loc, lat)
                .then_some("passes a thunk buried in data")
                .or_else(|| in_thunk(a, loc, lat, flow))
        }),
        TypedCompKind::App { args, .. } | TypedCompKind::Do { args, .. } => {
            args.iter().find_map(|a| {
                (declared_thunk_escape(a) || !value_sig(a, loc, lat).is_empty())
                    .then_some("hands an effectful thunk to a call it cannot follow")
                    .or_else(|| {
                        buried(a, loc, lat).then_some("hands a thunk buried in data to a call")
                    })
            })
        }
        TypedCompKind::Bind(m, x, n) => esc(m, loc, lat, flow).or_else(|| {
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), result_sig(m, loc, lat, flow));
            esc(n, &loc2, lat, flow)
        }),
        TypedCompKind::If(_, t, e) => esc(t, loc, lat, flow).or_else(|| esc(e, loc, lat, flow)),
        TypedCompKind::Case(_, arms) => arms.iter().find_map(|(_, b)| esc(b, loc, lat, flow)),
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
        } => esc(body, loc, lat, flow)
            .or_else(|| return_body.as_ref().and_then(|rb| esc(rb, loc, lat, flow)))
            .or_else(|| {
                ops.arms()
                    .iter()
                    .find_map(|op| esc(op.body(), loc, lat, flow))
            }),
        _ => {
            let mut found = None;
            each_value(c, &mut |v| {
                found = found.or_else(|| in_thunk(v, loc, lat, flow));
            });
            found
        }
    }
}

// Recurse into a thunk's own body looking for escapes there.
fn in_thunk(v: &TypedValue, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Option<&'static str> {
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
            fields.iter().find_map(|f| in_thunk(f, loc, lat, flow))
        }
        TypedValueKind::UnboxedRecord(fields) => {
            fields.iter().find_map(|(_, f)| in_thunk(f, loc, lat, flow))
        }
        _ => None,
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

/// [`value_sig`] for a scope that also holds threaded locals.
///
/// A lambda thunk performs, besides what its body performs directly, whatever
/// the thunk-valued locals it closes over perform when it forces them. The
/// latent map cannot see those forces, so the state rewrite, which threads
/// evidence through exactly such locals, reads signatures through this pair.
#[must_use]
pub fn value_sig_in(v: &TypedValue, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Sig {
    let v = bridged(v);
    // A newtype's field read back out of it is recovered from data the flow
    // does not follow, as a pattern recovers one: only the field's type says
    // what forcing it performs. Wrapping a value into the newtype hands over
    // data, which is forced by nothing, whatever the lambda inside performs.
    if matches!(&v.kind, TypedValueKind::NewtypeRepr { .. }) {
        return flow.carriers.sig(v.ty());
    }
    let v = peel(v);
    match &v.kind {
        TypedValueKind::Thunk(c) => {
            let mut s = body_sig(c, lat);
            let (body, loc2) = match c.kind() {
                TypedCompKind::Lam(ps, b) => {
                    let mut loc2 = loc.clone();
                    for p in ps {
                        loc2.remove(&p.name());
                    }
                    (b.as_ref(), loc2)
                }
                _ => (c.as_ref(), loc.clone()),
            };
            performed(body, &loc2, lat, flow, &mut s);
            s
        }
        // A name the flow reached has a flowed signature, and that answer is
        // the one every engine threads to. A name it did not reach, because a
        // pattern recovered it from data the flow does not follow, has only
        // its own type to say what forcing it performs.
        TypedValueKind::Var { name, .. } => loc
            .get(name)
            .cloned()
            .unwrap_or_else(|| flow.carriers.sig(v.ty())),
        _ => Sig::new(),
    }
}

// The value under a lowered bridge: a name read at another representation
// still performs what the flow reached it with.
fn bridged(mut v: &TypedValue) -> &TypedValue {
    while let TypedValueKind::LoweredRepr { value, .. } = &v.kind {
        v = value;
    }
    v
}

/// [`result_sig`] read through [`value_sig_in`].
#[must_use]
pub fn result_sig_in(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Sig {
    match c.kind() {
        TypedCompKind::Return(v) => value_sig_in(v, loc, lat, flow),
        TypedCompKind::Call { callee, .. } => flow.ret.get(callee).cloned().unwrap_or_default(),
        // What an application answers with, the flow never followed: a
        // continuation answering with the next step's thunk hands it over
        // as data does, so only its type says what forcing it performs.
        TypedCompKind::App { .. } => flow.carriers.sig(c.sig().result()),
        TypedCompKind::Bind(m, x, n) => {
            let rm = result_sig_in(m, loc, lat, flow);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            result_sig_in(n, &loc2, lat, flow)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = result_sig_in(t, loc, lat, flow);
            merge(&mut s, &result_sig_in(e, loc, lat, flow));
            s
        }
        TypedCompKind::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &result_sig_in(b, loc, lat, flow));
            }
            s
        }
        _ => Sig::new(),
    }
}

/// What a computation performs through the thunk-valued locals in scope.
///
/// Each force of one adds that local's signature. Ops performed directly are
/// the latent map's business; handlers and masks shape the answer as they
/// shape [`latent`]'s.
pub fn performed(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow, out: &mut Sig) {
    match c.kind() {
        TypedCompKind::App { callee, .. } => {
            if let TypedCompKind::Force(v) = callee.kind() {
                merge(out, &value_sig_in(v, loc, lat, flow));
            }
        }
        TypedCompKind::Bind(m, x, n) => {
            performed(m, loc, lat, flow, out);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), result_sig_in(m, loc, lat, flow));
            performed(n, &loc2, lat, flow, out);
        }
        TypedCompKind::If(_, t, e) => {
            performed(t, loc, lat, flow, out);
            performed(e, loc, lat, flow, out);
        }
        TypedCompKind::Case(_, arms) => {
            for (_, b) in arms {
                performed(b, loc, lat, flow, out);
            }
        }
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            let mut inner = Sig::new();
            performed(body, loc, lat, flow, &mut inner);
            let handled = |id: Sym| ops.arms().iter().any(|op| op.name() == id);
            out.extend(
                inner
                    .into_iter()
                    .filter_map(|m| match (handled(m.id), m.depth) {
                        (true, 0) => None,
                        (true, depth) => Some(MaskOp {
                            id: m.id,
                            depth: depth - 1,
                        }),
                        (false, _) => Some(m),
                    }),
            );
            if let Some(r) = return_body {
                performed(r, loc, lat, flow, out);
            }
        }
        TypedCompKind::Mask(ops, body) => {
            let mut inner = Sig::new();
            performed(body, loc, lat, flow, &mut inner);
            out.extend(inner.into_iter().map(|m| MaskOp {
                id: m.id,
                depth: m.depth + u32::from(ops.contains(&m.id)),
            }));
        }
        _ => {}
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
    deep: bool,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) -> Sig {
    let sig = |v: &TypedValue, loc: &Loc| {
        if deep {
            value_sig_in(v, loc, lat, flow)
        } else {
            value_sig(v, loc, lat)
        }
    };
    match c.kind() {
        TypedCompKind::Return(v) => {
            visit_value(v, loc, lat, flow, deep, upd);
            sig(v, loc)
        }
        TypedCompKind::Call { callee, args, .. } => {
            for (i, a) in args.iter().enumerate() {
                visit_value(a, loc, lat, flow, deep, upd);
                if let Some(slots) = upd.get_mut(callee) {
                    if let Some(slot) = slots.get_mut(i) {
                        merge(slot, &sig(a, loc));
                    }
                }
            }
            flow.ret.get(callee).cloned().unwrap_or_default()
        }
        TypedCompKind::Bind(m, x, n) => {
            let rm = props(m, loc, lat, flow, deep, upd);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            props(n, &loc2, lat, flow, deep, upd)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = props(t, loc, lat, flow, deep, upd);
            merge(&mut s, &props(e, loc, lat, flow, deep, upd));
            s
        }
        TypedCompKind::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &props(b, loc, lat, flow, deep, upd));
            }
            s
        }
        TypedCompKind::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(p.name(), Sig::new());
            }
            props(b, &loc2, lat, flow, deep, upd);
            Sig::new()
        }
        TypedCompKind::App { callee, args, .. } => {
            props(callee, loc, lat, flow, deep, upd);
            for a in args {
                visit_value(a, loc, lat, flow, deep, upd);
            }
            Sig::new()
        }
        TypedCompKind::Mask(_, b) => props(b, loc, lat, flow, deep, upd),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            props(body, loc, lat, flow, deep, upd);
            if let Some(rb) = return_body {
                props(rb, loc, lat, flow, deep, upd);
            }
            for op in ops.arms() {
                props(op.body(), loc, lat, flow, deep, upd);
            }
            Sig::new()
        }
        _ => {
            each_value(c, &mut |v| visit_value(v, loc, lat, flow, deep, upd));
            Sig::new()
        }
    }
}

fn visit_value(
    v: &TypedValue,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    deep: bool,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            if let TypedCompKind::Lam(ps, b) = c.kind() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(p.name(), Sig::new());
                }
                props(b, &loc2, lat, flow, deep, upd);
            } else {
                props(c, loc, lat, flow, deep, upd);
            }
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for f in fields {
                visit_value(f, loc, lat, flow, deep, upd);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, f) in fields {
                visit_value(f, loc, lat, flow, deep, upd);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::super::latent::latent_map;
    use crate::core::typed::{CompSig, CoreFnSig, TypedBinder, TypedCoreFn};
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

    fn unit_comp(row: EffRow, kind: TypedCompKind) -> TypedComp {
        TypedComp::new(CompSig::new(CoreType::Source(Type::Unit), row), kind)
    }

    // `wrap(s) = \() -> s()` performs nothing of its own, so the latent-only
    // flow reports its result as carrying nothing. The state rewrite threads
    // evidence through `s`, and the deep flow sees that the returned lambda
    // forwards whatever `s` carries.
    #[test]
    fn deep_flow_carries_evidence_forwarded_through_a_returned_lambda() {
        let op = Sym::new("tick");
        let clock = EffRow::singleton("Clock");
        let cb = callback(clock.clone());
        let fun = match &cb {
            CoreType::Thunk(sig) => sig.result().clone(),
            _ => unreachable!(),
        };
        let s = Sym::new("s");
        let forced = TypedComp::new(
            CompSig::new(fun.clone(), EffRow::Empty),
            TypedCompKind::Force(TypedValue::new(
                cb.clone(),
                TypedValueKind::Var {
                    name: s,
                    instantiation: Vec::new(),
                },
            )),
        );
        let forwarding = TypedComp::new(
            CompSig::new(fun.clone(), EffRow::Empty),
            TypedCompKind::Lam(
                Vec::new(),
                Box::new(unit_comp(
                    clock.clone(),
                    TypedCompKind::App {
                        callee: Box::new(forced),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
            ),
        );
        let wrap = TypedCoreFn::new(
            Sym::new("wrap"),
            vec![TypedBinder::new(s, cb.clone())],
            TypedComp::new(
                CompSig::new(cb.clone(), EffRow::Empty),
                TypedCompKind::Return(TypedValue::new(
                    cb.clone(),
                    TypedValueKind::Thunk(Box::new(forwarding)),
                )),
            ),
            CoreFnSig::new(
                Vec::new(),
                vec![cb.clone()],
                CompSig::new(cb.clone(), EffRow::Empty),
            ),
            0,
        );
        let performing = TypedComp::new(
            CompSig::new(fun, EffRow::Empty),
            TypedCompKind::Lam(
                Vec::new(),
                Box::new(unit_comp(
                    clock,
                    TypedCompKind::Do {
                        operation: op,
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
            ),
        );
        let main = TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            TypedComp::new(
                CompSig::new(cb.clone(), EffRow::Empty),
                TypedCompKind::Call {
                    callee: Sym::new("wrap"),
                    instantiation: Vec::new(),
                    args: vec![TypedValue::new(
                        cb.clone(),
                        TypedValueKind::Thunk(Box::new(performing)),
                    )],
                },
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(cb, EffRow::Empty)),
            0,
        );
        let fns = [wrap, main];
        let lat = latent_map(&fns);
        let carries = |sig: &Sig| sig.iter().any(|m| m.id == op);

        let shallow = analyze(&fns, &lat);
        assert!(carries(&shallow.param[&Sym::new("wrap")][0]));
        assert!(!carries(&shallow.ret[&Sym::new("wrap")]));
        assert!(!carries(&shallow.ret[&Sym::new("main")]));

        let deep = analyze_in(&fns, &lat, &Carriers::none());
        assert!(carries(&deep.param[&Sym::new("wrap")][0]));
        assert!(carries(&deep.ret[&Sym::new("wrap")]));
        assert!(carries(&deep.ret[&Sym::new("main")]));
    }
}
