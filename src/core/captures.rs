//! Closure-capture facts for `dump captures`: a read-only, diagnostic analysis
//! over elaborated Core.
//!
//! For every lambda and thunk it records what the closure closes over (a source
//! value, a top-level code reference) and what scoped effect operations it
//! performs (a `var` cell's get/set, a named handler instance's private op), then
//! classifies each fact as portable, nonportable, or unknown for a hypothetical
//! move across a suspend boundary. It reads the same term the content hasher and
//! interpreter observe and changes no compilation output.
//!
//! The classification is conservative: a false "nonportable" or "unknown" only
//! costs a diagnostic, but a false "portable" would license an unsound move, so
//! nothing is called portable unless it provably is. Value data defers to the
//! suspend codec's own encodability judgment ([`portable_value_type`]); a
//! top-level function is portable because it travels as a content-addressed code
//! reference; a `var` cell and a named handler instance are nonportable because
//! their backing scope ends before a moved computation could resume.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::cbpv::{Comp, CoreFn, Value};
use crate::core::fv;
use crate::core::traverse::Visit;
use crate::eval::kont::portable_value_type;
use crate::names;
use crate::sym::Sym;
use crate::types::ty::Type;

// Column labels for the closure form and each capture kind. One home for the
// vocabulary the dump renders, so a label never drifts between the enum and the
// text projection.
const FORM_LAM: &str = "lambda";
const FORM_THUNK: &str = "thunk";
const KIND_VALUE: &str = "value";
const KIND_CODE: &str = "code";
const KIND_MUTABLE_CELL: &str = "mutable-cell";
const KIND_HANDLER_INSTANCE: &str = "handler-instance";
const KIND_CAPABILITY: &str = "capability";

// Portability status words and the fixed reason strings. Reasons that name a
// subject (a cell, an instance) are templated at render time from the fact's
// name; the rest are constants so the vocabulary has a single home.
const STATUS_PORTABLE: &str = "portable";
const STATUS_NONPORTABLE: &str = "nonportable";
const STATUS_UNKNOWN: &str = "unknown";
const WHY_CODE_REF: &str = "content-addressed top-level definition";
const WHY_NO_TYPE: &str = "no type recovered for this capture at the core boundary";
const WHY_FN_VALUE: &str = "captured function value; its own captures are not analyzed here";
const WHY_ABSTRACT: &str = "type carries no portable-value certificate";
const WHY_AMBIENT_OP: &str = "effect operation whose discharging handler scope is undecidable here";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosureForm {
    Lam,
    Thunk,
}

impl ClosureForm {
    const fn label(self) -> &'static str {
        match self {
            Self::Lam => FORM_LAM,
            Self::Thunk => FORM_THUNK,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureKind {
    Value,
    Code,
    MutableCell,
    HandlerInstance,
    Capability,
}

impl CaptureKind {
    const fn label(self) -> &'static str {
        match self {
            Self::Value => KIND_VALUE,
            Self::Code => KIND_CODE,
            Self::MutableCell => KIND_MUTABLE_CELL,
            Self::HandlerInstance => KIND_HANDLER_INSTANCE,
            Self::Capability => KIND_CAPABILITY,
        }
    }
}

// A nonportable reason that names its subject; the subject is the fact's `name`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonPortable {
    MutableCell,
    HandlerInstance,
}

impl NonPortable {
    fn reason(self, subject: &str) -> String {
        match self {
            Self::MutableCell => {
                format!("mutable cell `{subject}` is dropped when its block ends")
            }
            Self::HandlerInstance => {
                format!("handler instance `{subject}` is out of scope once its `with` block ends")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Portability {
    Portable,
    NonPortable(NonPortable),
    Unknown(&'static str),
}

/// One captured binding or performed scoped operation of one closure.
#[derive(Clone, Debug)]
pub struct CaptureFact {
    /// Enclosing top-level definition.
    pub def: Sym,
    /// Deterministic pre-order ordinal of the closure within its definition,
    /// counting only closures that carry at least one reported fact. Core drops
    /// source spans, so a definition and this ordinal name the closure site.
    pub site: usize,
    pub form: ClosureForm,
    /// The captured binding, or the subject (cell/instance/op) of a scoped op.
    pub name: Sym,
    /// The type where the checker knows it (a top-level definition's type, or an
    /// enclosing definition's parameter type); `None` for a deeper local binder.
    pub ty: Option<Type>,
    pub kind: CaptureKind,
    pub port: Portability,
}

/// The capture facts of `user_fns`, deterministically ordered.
///
/// `code_names` is the set of the program's own top-level definitions: a call to
/// one from inside a closure is a portable, content-addressed code reference.
/// `decl_ty` maps a name to its checked type, used to type a code reference and,
/// via the enclosing function's arrow, its parameters.
#[must_use]
pub fn facts(
    user_fns: &[&CoreFn],
    code_names: &BTreeSet<Sym>,
    decl_ty: &BTreeMap<Sym, Type>,
) -> Vec<CaptureFact> {
    let mut out = Vec::new();
    for f in user_fns {
        let params = param_types(decl_ty.get(&f.name), &f.params[f.dict_arity..]);
        let mut walk = Walk {
            def: f.name,
            params: &params,
            code_names,
            decl_ty,
            site: 0,
            out: &mut out,
        };
        walk.visit_comp(&f.body);
    }
    out.sort_by(|a, b| {
        (a.def.as_str(), a.site, a.name.as_str(), a.kind.label()).cmp(&(
            b.def.as_str(),
            b.site,
            b.name.as_str(),
            b.kind.label(),
        ))
    });
    out
}

/// Render capture facts as the deterministic `dump captures` text. The facts are
/// the data; this is a projection of them.
#[must_use]
pub fn render(facts: &[CaptureFact]) -> String {
    let mut out = String::new();
    let mut i = 0;
    while i < facts.len() {
        let head = &facts[i];
        let mut j = i;
        while j < facts.len() && facts[j].def == head.def && facts[j].site == head.site {
            j += 1;
        }
        let group = &facts[i..j];
        writeln!(
            out,
            "closure {} in {} ({})",
            head.site,
            head.def.as_str(),
            head.form.label()
        )
        .unwrap();
        let name_w = group
            .iter()
            .map(|f| f.name.as_str().len())
            .max()
            .unwrap_or(0);
        let ty_w = group.iter().map(|f| show_ty(f).len()).max().unwrap_or(0);
        let kind_w = group
            .iter()
            .map(|f| f.kind.label().len())
            .max()
            .unwrap_or(0);
        for f in group {
            let reason = why(f);
            let tail = if reason.is_empty() {
                String::new()
            } else {
                format!("  {reason}")
            };
            writeln!(
                out,
                "  {name:<name_w$} : {ty:<ty_w$}  {kind:<kind_w$}  {status}{tail}",
                name = f.name.as_str(),
                ty = show_ty(f),
                kind = f.kind.label(),
                status = status(&f.port),
            )
            .unwrap();
        }
        i = j;
    }
    if out.is_empty() {
        out.push_str("no captures\n");
    }
    out
}

fn show_ty(f: &CaptureFact) -> String {
    f.ty.as_ref().map_or_else(|| "?".to_string(), Type::show)
}

const fn status(p: &Portability) -> &'static str {
    match p {
        Portability::Portable => STATUS_PORTABLE,
        Portability::NonPortable(_) => STATUS_NONPORTABLE,
        Portability::Unknown(_) => STATUS_UNKNOWN,
    }
}

fn why(f: &CaptureFact) -> String {
    match f.port {
        Portability::Portable => match f.kind {
            CaptureKind::Code => WHY_CODE_REF.to_string(),
            _ => String::new(),
        },
        Portability::NonPortable(r) => r.reason(f.name.as_str()),
        Portability::Unknown(r) => r.to_string(),
    }
}

// Peel a definition's checked type down to its parameter types and zip them onto
// the (dictionary-stripped) core parameter names. A missing type, or an arity
// the arrow does not cover, simply leaves those parameters untyped.
fn param_types(ty: Option<&Type>, params: &[Sym]) -> BTreeMap<Sym, Type> {
    let mut env = BTreeMap::new();
    let Some(mut ty) = ty else { return env };
    while let Type::Forall(_, b) | Type::RowForall(_, b) = ty {
        ty = b;
    }
    if let Type::Fun(args, _, _) = ty {
        for (p, a) in params.iter().zip(args) {
            env.insert(*p, a.clone());
        }
    }
    env
}

// Visitor that records each closure's facts in pre-order, then descends to find
// nested closures (which receive later ordinals). Only closures with at least one
// reported fact consume an ordinal, so the numbering does not expose the count of
// compiler-synthesized handler thunks.
struct Walk<'a> {
    def: Sym,
    params: &'a BTreeMap<Sym, Type>,
    code_names: &'a BTreeSet<Sym>,
    decl_ty: &'a BTreeMap<Sym, Type>,
    site: usize,
    out: &'a mut Vec<CaptureFact>,
}

impl Walk<'_> {
    fn record(&mut self, form: ClosureForm, binders: &[Sym], body: &Comp) {
        let mut group: Vec<(Sym, Option<Type>, CaptureKind, Portability)> = Vec::new();
        // Value captures: the closure's free variables, minus its own binders,
        // minus compiler scratch (resume/state binders, elaboration temporaries),
        // all of which carry an unforgeable sigil.
        for name in fv::comp_without(body, binders) {
            if names::is_synthesized(name.as_str()) {
                continue;
            }
            group.push(self.classify_value(name));
        }
        // Code references: the program's own definitions this closure calls
        // directly. A top-level function is never a free value variable (a bare
        // reference eta-expands to a call), so calls are the surface where a
        // content-addressed code capture shows.
        let mut calls = BTreeSet::new();
        direct_calls(body, self.code_names, &mut calls);
        for name in calls {
            group.push((
                name,
                self.decl_ty.get(&name).cloned(),
                CaptureKind::Code,
                Portability::Portable,
            ));
        }
        // Scoped operations the closure performs whose handler is outside it.
        for op in escaping_ops(body) {
            group.push(classify_op(op));
        }
        if group.is_empty() {
            return;
        }
        let site = self.site;
        self.site += 1;
        for (name, ty, kind, port) in group {
            self.out.push(CaptureFact {
                def: self.def,
                site,
                form,
                name,
                ty,
                kind,
                port,
            });
        }
    }

    fn classify_value(&self, name: Sym) -> (Sym, Option<Type>, CaptureKind, Portability) {
        if self.code_names.contains(&name) {
            let ty = self.decl_ty.get(&name).cloned();
            return (name, ty, CaptureKind::Code, Portability::Portable);
        }
        let ty = self.params.get(&name).cloned();
        let port = match &ty {
            Some(t) if portable_value_type(t) => Portability::Portable,
            Some(Type::Fun(..)) => Portability::Unknown(WHY_FN_VALUE),
            Some(_) => Portability::Unknown(WHY_ABSTRACT),
            None => Portability::Unknown(WHY_NO_TYPE),
        };
        (name, ty, CaptureKind::Value, port)
    }
}

impl Visit for Walk<'_> {
    fn visit_comp(&mut self, c: &Comp) {
        if let Comp::Lam(ps, body) = c {
            self.record(ClosureForm::Lam, ps, body);
        }
        self.descend_comp(c);
    }

    fn visit_value(&mut self, v: &Value) {
        // A source lambda elaborates to a thunk wrapping a `Lam`; record it once,
        // at the inner `Lam` (reached by the descent below), so the two layers of
        // one closure are not reported twice. A thunk of a non-lambda computation
        // is a genuine suspended value and is recorded here.
        if let Value::Thunk(body) = v {
            if !matches!(**body, Comp::Lam(..)) {
                self.record(ClosureForm::Thunk, &[], body);
            }
        }
        self.descend_value(v);
    }
}

// Classify one performed operation by the shape of its op name, deferring to the
// canonical `names` inverses so a mangling change cannot silently reclassify it.
// A `var` cell's get/set is checked first because it shares the three-part shape
// of a named instance op.
fn classify_op(op: Sym) -> (Sym, Option<Type>, CaptureKind, Portability) {
    let s = op.as_str();
    if let Some((cell, _)) = names::parse_var_get(s).or_else(|| names::parse_var_set(s)) {
        return (
            Sym::new(cell),
            None,
            CaptureKind::MutableCell,
            Portability::NonPortable(NonPortable::MutableCell),
        );
    }
    if let Some((_, inst)) = names::parse_named_op(s) {
        return (
            Sym::new(inst),
            None,
            CaptureKind::HandlerInstance,
            Portability::NonPortable(NonPortable::HandlerInstance),
        );
    }
    (
        op,
        None,
        CaptureKind::Capability,
        Portability::Unknown(WHY_AMBIENT_OP),
    )
}

// The program's own definitions this closure body calls directly, not descending
// into nested closures (each nested closure reports its own calls). A call to a
// name in `own` is a portable code reference. Only `Comp` positions are walked: a
// top-level function reference is only ever a `Call` head or (used first-class) an
// eta-thunk, never a bare `Value`, so operand values need no descent.
fn direct_calls(c: &Comp, own: &BTreeSet<Sym>, acc: &mut BTreeSet<Sym>) {
    match c {
        Comp::Call(f, _) => {
            if own.contains(f) {
                acc.insert(*f);
            }
        }
        Comp::Bind(a, _, b) => {
            direct_calls(a, own, acc);
            direct_calls(b, own, acc);
        }
        Comp::App(f, _) => direct_calls(f, own, acc),
        Comp::If(_, t, e) => {
            direct_calls(t, own, acc);
            direct_calls(e, own, acc);
        }
        Comp::Mask(_, b) => direct_calls(b, own, acc),
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                direct_calls(b, own, acc);
            }
        }
        Comp::WithReuse { body, .. } => direct_calls(body, own, acc),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            direct_calls(body, own, acc);
            if let Some(rb) = return_body {
                direct_calls(rb, own, acc);
            }
            for o in ops {
                direct_calls(&o.body, own, acc);
            }
        }
        // A nested closure (`Lam`) is a separate site and is not descended into;
        // every remaining computation holds its operands as values, which cannot
        // be a direct call head, so none is walked.
        _ => {}
    }
}

// The operations a closure body performs whose discharging handler lies outside
// the body. A `Do(op)` counts unless an enclosing `Handle` within the body lists
// `op`; masking is ignored (it only hides handlers, so treating a masked op as
// escaping stays conservative). Deduplicated and deterministically ordered.
fn escaping_ops(body: &Comp) -> Vec<Sym> {
    let mut acc = BTreeSet::new();
    let mut handled: Vec<Sym> = Vec::new();
    collect_ops(body, &mut handled, &mut acc);
    acc.into_iter().collect()
}

fn collect_ops(c: &Comp, handled: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
    match c {
        Comp::Do(op, args) => {
            if !handled.contains(op) {
                acc.insert(*op);
            }
            for a in args {
                collect_ops_value(a, handled, acc);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            let names: Vec<Sym> = ops.iter().map(|o| o.name).collect();
            let depth = handled.len();
            handled.extend(&names);
            collect_ops(body, handled, acc);
            if let Some(rb) = return_body {
                collect_ops(rb, handled, acc);
            }
            handled.truncate(depth);
            // An op-clause body runs against the outer handlers, not this one, so
            // its own performed ops are not discharged by these arms.
            for o in ops {
                collect_ops(&o.body, handled, acc);
            }
        }
        _ => descend_ops(c, handled, acc),
    }
}

// Structural recursion into every subterm, collecting nested closures' ops too
// (a closure that forces an inner thunk needs the inner thunk's handlers in
// scope, so counting them for the outer closure stays conservative).
fn descend_ops(c: &Comp, handled: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::UnboxedProject(v, _)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::Reuse(_, v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => collect_ops_value(v, handled, acc),
        Comp::RefSet(a, b) | Comp::Prim(_, a, b) | Comp::InitAt(a, b) => {
            collect_ops_value(a, handled, acc);
            collect_ops_value(b, handled, acc);
        }
        Comp::Bind(a, _, b) => {
            collect_ops(a, handled, acc);
            collect_ops(b, handled, acc);
        }
        Comp::App(f, args) => {
            collect_ops(f, handled, acc);
            for a in args {
                collect_ops_value(a, handled, acc);
            }
        }
        Comp::If(v, t, e) => {
            collect_ops_value(v, handled, acc);
            collect_ops(t, handled, acc);
            collect_ops(e, handled, acc);
        }
        Comp::Call(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for a in args {
                collect_ops_value(a, handled, acc);
            }
        }
        Comp::Lam(_, b) | Comp::Mask(_, b) => collect_ops(b, handled, acc),
        Comp::Case(v, arms) => {
            collect_ops_value(v, handled, acc);
            for (_, b) in arms {
                collect_ops(b, handled, acc);
            }
        }
        Comp::WithReuse { freed, body, .. } => {
            collect_ops_value(freed, handled, acc);
            collect_ops(body, handled, acc);
        }
        Comp::Do(..) | Comp::Handle { .. } => unreachable!("handled in collect_ops"),
    }
}

fn collect_ops_value(v: &Value, handled: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
    match v {
        Value::Thunk(c) => collect_ops(c, handled, acc),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                collect_ops_value(f, handled, acc);
            }
        }
        _ => {}
    }
}
