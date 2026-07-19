//! `stable`-block desugaring.
//!
//! A `stable T { .. }` block declares a serializable type's frozen version
//! history. It desugars, before deriving, into:
//!
//! - one record `DataDecl` per rung: the newest rung under the bare name `T`
//!   (the type a program builds and matches), each shipped predecessor under the
//!   dotted tag `T.Vk` (`names::stable_rung`), every rung `deriving (Eq, Show,
//!   Serialize, Stable, Arbitrary)` so the codec and the roundtrip law fall out;
//! - a synonym `T.Vn = T` so the current rung is reachable by its version tag;
//! - the adjacent version ladder as plain functions (`names::stable_upgrade` /
//!   `stable_downgrade`): a purely additive step is generated (the new field is
//!   defaulted on the way up, dropped and recorded as `Loss` on the way down); a
//!   type mutation takes its two directions from the block's hand-written
//!   converters. Only adjacent converters exist; spanning composes them.
//!
//! Each shipped rung carries a committed shape-digest golden (`frozen "<hex>"`);
//! a rung whose recomputed digest no longer matches is the frozen-format compile
//! error, reseated with `prism wire --accept`.
//!
//! The grammar has no multi-parameter `Migrate(lo, hi)` class syntax, so the
//! ladder is plain functions rather than instances. Version-dispatched decode
//! (walking an older frame up by its frame version) is the wire codec's concern:
//! this pass emits the ladder the codec composes, and
//! `names::stable_decode_ladder` names its reserved entry point.

use std::collections::BTreeSet;

use marginalia::Span;

use super::{call, evar, sp, spat};
use crate::core::{contract_digest, Hashes};
use crate::error::{ErrKind, TypeError};
use crate::names;
use crate::names::{
    DECODE_METHOD, FAIL_OP, WIRE_COMPOSE_DOWNGRADE, WIRE_DECODE_VALUE_WITH_DIGEST,
    WIRE_ENCODE_VALUE_WITH_DIGEST, WIRE_IS_EMPTY, WIRE_OPEN_VALUE_ANY,
};
use crate::stable_lock::{
    edge_hash, route_hash, EdgeLock, FamilyLock, RouteLock, RungShape, MODE_AUTO, MODE_DEFAULT,
    MODE_MANUAL,
};
use crate::sym::Sym;
use crate::syntax::ast::{
    Arm, BinOp, ConvDir, Converter, Ctor, DataDecl, Decl, Expr, Fip, Migration, MigrationDir,
    MigrationRoute, Param, Pattern, Program, Rung, StableDecl, SynonymDecl, Total, Ty, S,
};
use crate::types::{ARBITRARY_CLASS, EQ_CLASS, SERIALIZE_CLASS, SHOW_CLASS, STABLE_CLASS};

// The codec and frozen witness are the point of a `stable` block, so every rung
// derives them; a missing class is a "you need `import Wire`" error below.
const RUNG_REQUIRED: &[&str] = &[SERIALIZE_CLASS, STABLE_CLASS];

// Added to the bundle only when the class is in scope, so a `stable` block does
// not force a program to import the property-test modules just to get equality
// and rendering. `Arbitrary` in scope is what makes the roundtrip law testable.
const RUNG_OPTIONAL: &[&str] = &[EQ_CLASS, SHOW_CLASS, ARBITRARY_CLASS];

// The `Loss` type a downgrade reports dropped fields through. Its canonical name
// (`Wire.Loss`) is resolved from the imported types, since this pass runs after
// name resolution and emits references the resolver never sees.
const LOSS_TYPE: &str = "Loss";

// The `Bytes` type a generated frame function encodes to and decodes from. Like
// `Loss`, its canonical name (`Wire.Bytes`) is resolved from the imported types,
// since this pass runs after name resolution and emits references the resolver
// never sees.
const BYTES_TYPE: &str = "Bytes";

// The resolved `Loss` type and its constructor, threaded into the downgrade
// builders. Both are the same canonical name; a program that reaches here has
// imported `Wire`, so the lookup succeeds (a bare fallback keeps the error, if
// any, on the missing import rather than a panic).
struct LossRef {
    ty: Ty,
    ctor: String,
}

/// Expand every `stable` block into ordinary types, functions, and synonyms, and
/// gate each shipped rung against its committed shape golden.
///
/// # Errors
/// Fails on a malformed block (a mismatched extension base, a type mutation with
/// no hand-written converter) or a frozen rung whose shape digest drifted.
pub(super) fn expand_stable(prog: &mut Program) -> Result<(), TypeError> {
    let blocks = std::mem::take(&mut prog.stable);
    let in_scope: std::collections::BTreeSet<&str> = prog
        .classes
        .iter()
        .map(|c| names::bare_name(&c.name))
        .collect();
    // Each imported function's bare name mapped to its canonical `Module.fn`, so a
    // generated frame helper's reference to a wire library function is already the
    // canonical name the resolver would have produced (this pass runs after name
    // resolution). The `stable` block's own generated functions never collide with
    // these, so building it once up front is sound. Mirrors `derive.rs`'s `lib`.
    let wire_canon: std::collections::BTreeMap<String, String> = prog
        .fns
        .iter()
        .map(|f| (names::bare_name(&f.name).to_string(), f.name.clone()))
        .collect();
    let libf = |n: &str| {
        wire_canon
            .get(n)
            .map_or_else(|| n.to_string(), std::string::ToString::to_string)
    };
    let bytes_ty = canon_ty(prog, BYTES_TYPE);
    for sd in &blocks {
        if let Some(missing) = RUNG_REQUIRED.iter().find(|c| !in_scope.contains(**c)) {
            return Err(ErrKind::StableNeedsClass {
                name: sd.name.clone(),
                class: (*missing).to_string(),
            }
            .at(sd.span));
        }
        let derives = rung_derives(&in_scope);
        let loss = loss_ref(prog);
        let rungs = resolve_rungs(sd)?;
        let mut datas = Vec::new();
        for (idx, r) in rungs.iter().enumerate() {
            let data = rung_data(sd, idx, r, &derives);
            check_frozen(sd, &sd.rungs[idx], &data)?;
            datas.push(data);
        }
        // The current rung is the bare type; expose it under its version tag too.
        let last = rungs.last().expect("a stable block has at least one rung");
        prog.synonyms.push(SynonymDecl {
            name: names::stable_rung(&sd.name, &last.ver),
            params: Vec::new(),
            ty: Ty::Con(sd.name.clone(), Vec::new()),
            span: sd.span,
        });
        validate_migrations(sd, &rungs)?;
        let fns = ladder_fns(sd, &rungs, &loss)?;
        let routes = family_route_fns(sd, &rungs, &loss, &libf);
        let frames = frame_fns(sd, &rungs, &bytes_ty, &libf);
        prog.types.extend(datas);
        prog.fns.extend(fns);
        prog.fns.extend(routes);
        prog.fns.extend(frames);
    }
    Ok(())
}

/// The committed shape-digest golden of each shipped (non-current) rung of a
/// stable block, as `(version, digest)` pairs. The `prism wire --accept` path
/// seeds these into the source; `expand_stable` recomputes and gates them. Both
/// go through `rung_data`/`rung_digest`, so a seeded badge and its later check
/// agree. The current rung is omitted: it is the editable head, never sealed.
///
/// # Errors
/// Fails on a malformed block (the same errors `resolve_rungs` reports).
pub(crate) fn stable_rung_digests(sd: &StableDecl) -> Result<Vec<(String, String)>, TypeError> {
    let rungs = resolve_rungs(sd)?;
    let total = rungs.len();
    let mut out = Vec::new();
    for (idx, r) in rungs.iter().enumerate() {
        if idx + 1 == total {
            continue;
        }
        out.push((r.ver.clone(), rung_digest(&rung_data(sd, idx, r, &[]))));
    }
    Ok(out)
}

// Resolve the canonical `Loss` type and constructor from the imported types.
fn loss_ref(prog: &Program) -> LossRef {
    let canon = prog
        .types
        .iter()
        .find(|d| names::bare_name(&d.name) == LOSS_TYPE)
        .map_or(LOSS_TYPE, |d| d.name.as_str())
        .to_string();
    LossRef {
        ty: Ty::Con(canon.clone(), Vec::new()),
        ctor: canon,
    }
}

// Resolve an imported nullary type to its canonical name (a bare fallback keeps a
// missing import as the reported error rather than a panic), the same lookup
// `loss_ref` does for `Loss`.
fn canon_ty(prog: &Program, bare_name: &str) -> Ty {
    let canon = prog
        .types
        .iter()
        .find(|d| names::bare_name(&d.name) == bare_name)
        .map_or(bare_name, |d| d.name.as_str())
        .to_string();
    Ty::Con(canon, Vec::new())
}

// One rung with its version tag and its fully-resolved field list (the extension
// chain folded in), plus which of its own fields are genuinely new (carrying a
// default) versus a type mutation of an inherited field.
struct RungInfo {
    ver: String,
    span: Span,
    fields: Vec<(String, Ty)>,
    // Field name -> its default expression, for the fields this rung newly adds.
    new: Vec<(String, S<Expr>)>,
    // Field name -> its overriding expression is *not* here (types only): the
    // names of inherited fields this rung retypes, i.e. the type-mutation set.
    mutated: Vec<String>,
}

// Fold each rung's `..base` extension into a full field list, and classify this
// rung's own declared fields as new (appended) or a type mutation (retyping an
// inherited field).
fn resolve_rungs(sd: &StableDecl) -> Result<Vec<RungInfo>, TypeError> {
    let mut out: Vec<RungInfo> = Vec::new();
    for r in &sd.rungs {
        let mut fields: Vec<(String, Ty)> = match &r.base {
            None => Vec::new(),
            Some(base) => {
                let prev = out.last().filter(|p| &p.ver == base).ok_or_else(|| {
                    ErrKind::RungExtendsNonAdjacent {
                        rung: r.name.clone(),
                        base: base.clone(),
                        block: sd.name.clone(),
                    }
                    .at(r.span)
                })?;
                prev.fields.clone()
            }
        };
        // The first rung's fields are the initial format, not additive: nothing
        // upgrades into them, so they need no defaults. Only a field genuinely
        // added by an extension rung must default (the generated upgrade fills it).
        let is_ext = r.base.is_some();
        let mut new = Vec::new();
        let mut mutated = Vec::new();
        for f in &r.fields {
            if let Some(slot) = fields.iter_mut().find(|(n, _)| n == &f.name) {
                slot.1 = f.ty.clone();
                mutated.push(f.name.clone());
            } else {
                fields.push((f.name.clone(), f.ty.clone()));
                if is_ext {
                    let def = f.default.clone().ok_or_else(|| {
                        ErrKind::RungFieldNeedsDefault {
                            field: f.name.clone(),
                            rung: r.name.clone(),
                            field_ty: crate::fmt::decl::fmt_ty(&f.ty),
                        }
                        .at(r.span)
                    })?;
                    new.push((f.name.clone(), def));
                }
            }
        }
        out.push(RungInfo {
            ver: r.name.clone(),
            span: r.span,
            fields,
            new,
            mutated,
        });
    }
    Ok(out)
}

// The internal type (and constructor) name of rung `idx`: the bare stable name for
// the newest rung, the dotted version tag for a shipped predecessor.
fn rung_type(sd: &StableDecl, idx: usize, total: usize) -> String {
    if idx + 1 == total {
        sd.name.clone()
    } else {
        names::stable_rung(&sd.name, &sd.rungs[idx].name)
    }
}

// The classes a rung derives: the required codec pair plus whichever optional
// conveniences are in scope.
fn rung_derives(in_scope: &std::collections::BTreeSet<&str>) -> Vec<String> {
    RUNG_REQUIRED
        .iter()
        .chain(RUNG_OPTIONAL.iter().filter(|c| in_scope.contains(**c)))
        .map(|c| (*c).to_string())
        .collect()
}

// The record `DataDecl` for one rung, deriving the resolved bundle.
fn rung_data(sd: &StableDecl, idx: usize, r: &RungInfo, derives: &[String]) -> DataDecl {
    let name = rung_type(sd, idx, sd.rungs.len());
    let ctor = Ctor {
        name: name.clone(),
        args: r.fields.iter().map(|(_, t)| t.clone()).collect(),
        fields: Some(r.fields.clone()),
    };
    DataDecl {
        name,
        params: Vec::new(),
        param_kinds: Vec::new(),
        ctors: vec![ctor],
        deriving: derives.iter().map(|c| (c.clone(), r.span)).collect(),
        newtype: false,
        span: r.span,
    }
}

// The surface (dotted) name of a rung, used in diagnostics regardless of whether
// the rung is the current bare type internally.
fn rung_display(sd: &StableDecl, ver: &str) -> String {
    names::stable_rung(&sd.name, ver)
}

// Gate a rung against its committed shape golden. A rung with no badge has never
// shipped, so it is not checked; a badge that no longer matches the recomputed
// digest is the frozen-format error.
fn check_frozen(sd: &StableDecl, r: &Rung, data: &DataDecl) -> Result<(), TypeError> {
    let Some(committed) = &r.frozen else {
        return Ok(());
    };
    let digest = rung_digest(data);
    if &digest == committed {
        return Ok(());
    }
    let display = rung_display(sd, &r.name);
    Err(ErrKind::FrozenShapeChanged {
        display,
        rung: r.name.clone(),
    }
    .at(r.span))
}

// The committed shape-digest prefix of a rung's record type, in the exact scheme
// (`prism-core-hash-v1`) and truncation the stdlib goldens use.
pub(crate) fn rung_digest(data: &DataDecl) -> String {
    contract_digest(data)
}

fn mdecl(name: String, param: &str, param_ty: Ty, ret: Ty, body: S<Expr>, span: Span) -> Decl {
    Decl {
        name,
        params: vec![Param {
            name: param.to_string(),
            ty: Some(param_ty),
            borrow: false,
            default: None,
        }],
        ret: Some(ret),
        eff: None,
        constraints: Vec::new(),
        body,
        wheres: Vec::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        decreases: None,
        konst: false,
        test: false,
        total: Total::No,
        fip: Fip::No,
        replayable: false,
        no_alloc: false,
        span,
    }
}

// `RecordCreate` of `ctor` from a per-field value builder.
fn record(ctor: &str, fields: &[(String, Ty)], val: impl Fn(&str) -> S<Expr>, z: Span) -> S<Expr> {
    let fs = fields.iter().map(|(n, _)| (n.clone(), val(n))).collect();
    sp(Expr::RecordCreate(ctor.to_string(), fs), z)
}

// `Loss([f0, f1, ..])` from the dropped field names.
fn loss(loss: &LossRef, names_dropped: &[String], z: Span) -> S<Expr> {
    let items = names_dropped
        .iter()
        .map(|n| sp(Expr::Str(n.clone()), z))
        .collect();
    call(evar(&loss.ctor, z), vec![sp(Expr::List(items), z)], z)
}

// How one direction of an adjacent edge is implemented. A migration table row
// selects `Auto` (derive) or `Given` (a hand-supplied function); an edge with no
// governing row keeps the historical `Default` (derive when additive, else demand
// an inline converter).
enum EdgeImpl<'a> {
    Default,
    Auto,
    Given(&'a S<Expr>),
}

// The upgrade and downgrade implementation an adjacent edge takes, read off its
// migration row (if any). A `version(...)` row can leave one direction `auto`.
fn edge_impls<'a>(sd: &'a StableDecl, from: &str, to: &str) -> (EdgeImpl<'a>, EdgeImpl<'a>) {
    match edge_row(sd, from, to) {
        None => (EdgeImpl::Default, EdgeImpl::Default),
        Some(Migration {
            route: MigrationRoute::Auto,
            ..
        }) => (EdgeImpl::Auto, EdgeImpl::Auto),
        Some(Migration {
            route: MigrationRoute::Version(v),
            ..
        }) => (dir_impl(&v.upgrade), dir_impl(&v.downgrade)),
    }
}

const fn dir_impl(dir: &MigrationDir) -> EdgeImpl<'_> {
    match dir {
        MigrationDir::Auto => EdgeImpl::Auto,
        MigrationDir::Expr(e) => EdgeImpl::Given(e),
    }
}

// The migration row that governs the adjacent edge `from -> to`, if the table
// declares one.
fn edge_row<'a>(sd: &'a StableDecl, from: &str, to: &str) -> Option<&'a Migration> {
    sd.migrations.iter().find(|m| m.from == from && m.to == to)
}

// The whole adjacent ladder for one stable block. Each edge's two directions come
// from its migration row (derived or hand-supplied), falling back to the inline
// converter form when the table is silent about it.
fn ladder_fns(sd: &StableDecl, rungs: &[RungInfo], loss: &LossRef) -> Result<Vec<Decl>, TypeError> {
    let mut out = Vec::new();
    let total = rungs.len();
    for k in 0..total.saturating_sub(1) {
        let lo = &rungs[k];
        let hi = &rungs[k + 1];
        let lo_ty = Ty::Con(rung_type(sd, k, total), Vec::new());
        let hi_ty = Ty::Con(rung_type(sd, k + 1, total), Vec::new());
        let hi_ctor = rung_type(sd, k + 1, total);
        let lo_ctor = rung_type(sd, k, total);
        let (up, down) = edge_impls(sd, &lo.ver, &hi.ver);
        out.push(match up {
            EdgeImpl::Default | EdgeImpl::Auto if hi.mutated.is_empty() => {
                gen_upgrade(sd, lo, hi, &lo_ty, &hi_ty, &hi_ctor)
            }
            EdgeImpl::Default => mut_upgrade(sd, lo, hi, &lo_ty, &hi_ty, &hi_ctor)?,
            EdgeImpl::Auto => return Err(auto_undecidable(sd, lo, hi)),
            EdgeImpl::Given(e) => wrap_upgrade(sd, e, lo, hi, &lo_ty, &hi_ty),
        });
        out.push(match down {
            EdgeImpl::Default | EdgeImpl::Auto if hi.mutated.is_empty() => {
                gen_downgrade(sd, lo, hi, &lo_ty, &hi_ty, &lo_ctor, loss)
            }
            EdgeImpl::Default => mut_downgrade(sd, lo, hi, &lo_ty, &hi_ty, &lo_ctor, loss)?,
            EdgeImpl::Auto => return Err(auto_undecidable(sd, lo, hi)),
            EdgeImpl::Given(e) => wrap_downgrade(sd, e, lo, hi, &lo_ty, &hi_ty, loss),
        });
    }
    Ok(out)
}

// The parameter binder and body of the function a hand-supplied direction
// elaborates to. A single-parameter lambda is inlined so its binder carries the
// edge's rung type directly (the type checker then flows record fields through
// it, and the rung type is one the resolver never had to name); any other
// expression is applied to a fresh binder. Inline and named forms thus reach the
// same ordinary function shape.
fn edge_fn_body(e: &S<Expr>, param: &str) -> (String, S<Expr>) {
    if let Expr::Lam(ps, body) = &e.node {
        if let [only] = ps.as_slice() {
            return (only.name.clone(), (**body).clone());
        }
    }
    (
        param.to_string(),
        call(e.clone(), vec![evar(param, e.span)], e.span),
    )
}

// Wrap a hand-supplied upgrade under the exact edge interface. The binder carries
// `T.Vfrom` and the result is checked as `T.Vto` by the ordinary type checker; a
// wrong endpoint, extra effect, or wrong result is reported against this
// signature.
fn wrap_upgrade(
    sd: &StableDecl,
    e: &S<Expr>,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
) -> Decl {
    let z = e.span;
    let (param, body) = edge_fn_body(e, &names::stable_param(&lo.ver));
    mdecl(
        names::stable_upgrade(&sd.name, &lo.ver, &hi.ver),
        &param,
        lo_ty.clone(),
        hi_ty.clone(),
        body,
        z,
    )
}

// Wrap a hand-supplied downgrade under the exact edge interface `T.Vto ->
// (T.Vfrom, Wire.Loss)`. A downgrade that omits the loss, reverses the endpoints,
// or adds an effect fails the ordinary check against this signature.
fn wrap_downgrade(
    sd: &StableDecl,
    e: &S<Expr>,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
    lref: &LossRef,
) -> Decl {
    let z = e.span;
    let (param, body) = edge_fn_body(e, &names::stable_param(&hi.ver));
    mdecl(
        names::stable_downgrade(&sd.name, &hi.ver, &lo.ver),
        &param,
        hi_ty.clone(),
        Ty::Tuple(vec![lo_ty.clone(), lref.ty.clone()]),
        body,
        z,
    )
}

// The dedicated error for an `auto` row the compiler cannot derive: a type change
// (and, by extension, a rename, split, or merge, which surface as one). It names
// the fields that need judgment and proposes the smallest valid repair, never a
// guessed correspondence.
fn auto_undecidable(sd: &StableDecl, lo: &RungInfo, hi: &RungInfo) -> TypeError {
    let fields = hi
        .mutated
        .iter()
        .map(|f| format!("`{f}`"))
        .collect::<Vec<_>>()
        .join(", ");
    let repair = format!(
        "supply the migration explicitly:\n    \
         {from} -> {to} = version(upgrade = <fn>, downgrade = <fn>)\n  \
         a rename, split, merge, or type change is never guessed",
        from = lo.ver,
        to = hi.ver,
    );
    ErrKind::StableAutoUndecidable {
        block: sd.name.clone(),
        from: lo.ver.clone(),
        to: hi.ver.clone(),
        problem: "change a field type".to_string(),
        fields,
        repair,
    }
    .at(hi.span)
}

// Generated total upgrade for a purely additive step: copy every inherited field,
// default each new one.
fn gen_upgrade(
    sd: &StableDecl,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
    hi_ctor: &str,
) -> Decl {
    let z = hi.span;
    let x = names::stable_param(&lo.ver);
    let body = record(
        hi_ctor,
        &hi.fields,
        |f| match hi.new.iter().find(|(n, _)| n == f) {
            Some((_, def)) => def.clone(),
            None => sp(Expr::FieldAccess(Box::new(evar(&x, z)), f.to_string()), z),
        },
        z,
    );
    mdecl(
        names::stable_upgrade(&sd.name, &lo.ver, &hi.ver),
        &x,
        lo_ty.clone(),
        hi_ty.clone(),
        body,
        z,
    )
}

// Generated partial downgrade for an additive step: keep every older field, report
// the dropped new ones as `Loss`.
fn gen_downgrade(
    sd: &StableDecl,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
    lo_ctor: &str,
    lref: &LossRef,
) -> Decl {
    let z = hi.span;
    let x = names::stable_param(&hi.ver);
    let kept = record(
        lo_ctor,
        &lo.fields,
        |f| sp(Expr::FieldAccess(Box::new(evar(&x, z)), f.to_string()), z),
        z,
    );
    let dropped: Vec<String> = hi.new.iter().map(|(n, _)| n.clone()).collect();
    let body = sp(Expr::Tuple(vec![kept, loss(lref, &dropped, z)]), z);
    mdecl(
        names::stable_downgrade(&sd.name, &hi.ver, &lo.ver),
        &x,
        hi_ty.clone(),
        Ty::Tuple(vec![lo_ty.clone(), lref.ty.clone()]),
        body,
        z,
    )
}

// Find the hand-written converter for a step, or report the missing direction.
fn find_conv<'a>(
    sd: &'a StableDecl,
    dir: ConvDir,
    from: &str,
    to: &str,
) -> Result<&'a Converter, TypeError> {
    sd.converters
        .iter()
        .find(|c| c.dir == dir && c.from == from && c.to == to)
        .ok_or_else(|| {
            let word = match dir {
                ConvDir::Upgrade => crate::kw::UPGRADE,
                ConvDir::Downgrade => crate::kw::DOWNGRADE,
            };
            ErrKind::RungNeedsConverter {
                to: to.to_string(),
                from: from.to_string(),
                block: sd.name.clone(),
                dir: word.to_string(),
            }
            .at(sd.span)
        })
}

// Build the target record from a converter body: each field is its override when
// the body names one, else it is read from the source rung value.
fn conv_record(c: &Converter, ctor: &str, fields: &[(String, Ty)], z: Span) -> S<Expr> {
    record(
        ctor,
        fields,
        |f| match c.overrides.iter().find(|(n, _)| n == f) {
            Some((_, e)) => e.clone(),
            None => sp(
                Expr::FieldAccess(Box::new(c.base.clone()), f.to_string()),
                z,
            ),
        },
        z,
    )
}

// Hand-written upgrade across a type mutation.
fn mut_upgrade(
    sd: &StableDecl,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
    hi_ctor: &str,
) -> Result<Decl, TypeError> {
    let c = find_conv(sd, ConvDir::Upgrade, &lo.ver, &hi.ver)?;
    let z = c.span;
    let x = names::stable_param(&lo.ver);
    let body = conv_record(c, hi_ctor, &hi.fields, z);
    Ok(mdecl(
        names::stable_upgrade(&sd.name, &lo.ver, &hi.ver),
        &x,
        lo_ty.clone(),
        hi_ty.clone(),
        body,
        z,
    ))
}

// Hand-written downgrade across a type mutation, reporting the block's declared
// `drop_loss` fields.
fn mut_downgrade(
    sd: &StableDecl,
    lo: &RungInfo,
    hi: &RungInfo,
    lo_ty: &Ty,
    hi_ty: &Ty,
    lo_ctor: &str,
    lref: &LossRef,
) -> Result<Decl, TypeError> {
    let c = find_conv(sd, ConvDir::Downgrade, &hi.ver, &lo.ver)?;
    let z = c.span;
    let x = names::stable_param(&hi.ver);
    let kept = conv_record(c, lo_ctor, &lo.fields, z);
    let body = sp(Expr::Tuple(vec![kept, loss(lref, &c.drop_loss, z)]), z);
    Ok(mdecl(
        names::stable_downgrade(&sd.name, &hi.ver, &lo.ver),
        &x,
        hi_ty.clone(),
        Ty::Tuple(vec![lo_ty.clone(), lref.ty.clone()]),
        body,
        z,
    ))
}

// The binders the generated frame functions bind. Underscore-prefixed like the
// derived codec's binders, so a rung's own field never shadows one.
const FRAME_PARAM: &str = "_x";
const FRAME_BYTES: &str = "_bs";
const FRAME_DIGEST: &str = "_dig";
const FRAME_BODY: &str = "_body";
const FRAME_VALUE: &str = "_v";
const FRAME_REST: &str = "_rest";

// The compiler-known contract digest of rung `idx`: its record type's shape digest
// in the exact scheme and truncation the frozen goldens use. The current rung is
// the editable head, never sealed, but its digest is still computed here so the
// frame it encodes and the ladder that decodes it agree on one value.
fn frame_digest(sd: &StableDecl, idx: usize, r: &RungInfo) -> String {
    rung_digest(&rung_data(sd, idx, r, &[]))
}

// The three per-block frame helpers for the current rung: `wire_encode_T` /
// `wire_decode_T` wrap and unwrap a current-rung value under its compiler-known
// digest (so user code stops hand-threading a magic string), and `decode_ladder_T`
// dispatches an older frame up to the current type by its digest.
fn frame_fns(
    sd: &StableDecl,
    rungs: &[RungInfo],
    bytes_ty: &Ty,
    libf: &impl Fn(&str) -> String,
) -> Vec<Decl> {
    let total = rungs.len();
    let ty = Ty::Con(sd.name.clone(), Vec::new());
    let cur = frame_digest(sd, total - 1, &rungs[total - 1]);
    vec![
        wire_encode_fn(sd, &ty, bytes_ty, &cur, libf),
        wire_decode_fn(sd, &ty, bytes_ty, &cur, libf),
        decode_ladder_fn(sd, rungs, &ty, bytes_ty, libf),
    ]
}

// `wire_encode_T(x) = wire_encode_value_with_digest("<current digest>", x)`.
fn wire_encode_fn(
    sd: &StableDecl,
    ty: &Ty,
    bytes_ty: &Ty,
    digest: &str,
    libf: &impl Fn(&str) -> String,
) -> Decl {
    let z = sd.span;
    let body = call(
        evar(&libf(WIRE_ENCODE_VALUE_WITH_DIGEST), z),
        vec![sp(Expr::Str(digest.to_string()), z), evar(FRAME_PARAM, z)],
        z,
    );
    mdecl(
        names::stable_wire_encode(&sd.name),
        FRAME_PARAM,
        ty.clone(),
        bytes_ty.clone(),
        body,
        z,
    )
}

// `wire_decode_T(bs) = wire_decode_value_with_digest(bs, "<current digest>")`. The
// `! {Fail}` row is inferred from that callee, so the signature carries no `eff`.
fn wire_decode_fn(
    sd: &StableDecl,
    ty: &Ty,
    bytes_ty: &Ty,
    digest: &str,
    libf: &impl Fn(&str) -> String,
) -> Decl {
    let z = sd.span;
    let body = call(
        evar(&libf(WIRE_DECODE_VALUE_WITH_DIGEST), z),
        vec![evar(FRAME_BYTES, z), sp(Expr::Str(digest.to_string()), z)],
        z,
    );
    mdecl(
        names::stable_wire_decode(&sd.name),
        FRAME_BYTES,
        bytes_ty.clone(),
        ty.clone(),
        body,
        z,
    )
}

// `decode_ladder_T(bs)`: open the frame without knowing its digest, then dispatch
// on that digest to the matching frozen rung, decode the body as that rung's type,
// reject trailing bytes, and walk the adjacent upgrades up to the current type. An
// unknown digest, a malformed body, and trailing bytes all fail through `Fail`, the
// same channel the frame helpers use.
fn decode_ladder_fn(
    sd: &StableDecl,
    rungs: &[RungInfo],
    ty: &Ty,
    bytes_ty: &Ty,
    libf: &impl Fn(&str) -> String,
) -> Decl {
    let z = sd.span;
    let total = rungs.len();
    // Fold the rungs into an if/elif chain from the innermost `else fail()` out, so
    // each `dig == "<rung k>"` guards decoding the body as rung k and lifting it.
    let mut chain = call(evar(FAIL_OP, z), vec![], z);
    for k in (0..total).rev() {
        let digest = frame_digest(sd, k, &rungs[k]);
        let cond = sp(
            Expr::Bin(
                BinOp::Eq,
                Box::new(evar(FRAME_DIGEST, z)),
                Box::new(sp(Expr::Str(digest), z)),
            ),
            z,
        );
        let arm = ladder_arm(sd, rungs, k, libf, z);
        chain = sp(Expr::If(Box::new(cond), Box::new(arm), Box::new(chain)), z);
    }
    let open = call(
        evar(&libf(WIRE_OPEN_VALUE_ANY), z),
        vec![evar(FRAME_BYTES, z)],
        z,
    );
    let arm = Arm {
        pat: spat(
            Pattern::Tuple(vec![
                spat(Pattern::Var(FRAME_DIGEST.to_string()), z),
                spat(Pattern::Var(FRAME_BODY.to_string()), z),
            ]),
            z,
        ),
        guard: None,
        body: chain,
    };
    let body = sp(Expr::Match(Box::new(open), vec![arm]), z);
    mdecl(
        names::stable_decode_ladder(&sd.name),
        FRAME_BYTES,
        bytes_ty.clone(),
        ty.clone(),
        body,
        z,
    )
}

// One rung's decode arm: `match decode(_body) of (_v, _rest) => if empty(_rest)
// then <upgrade _v to current> else fail()`. The decoded value's type is pinned to
// rung k by how `_v` is used (fed to rung k's upgrade, or returned as the current
// type), which selects the right `Serialize` instance.
fn ladder_arm(
    sd: &StableDecl,
    rungs: &[RungInfo],
    k: usize,
    libf: &impl Fn(&str) -> String,
    z: Span,
) -> S<Expr> {
    let lifted = lift_to_current(sd, rungs, k, evar(FRAME_VALUE, z), z);
    let ok = sp(
        Expr::If(
            Box::new(call(
                evar(&libf(WIRE_IS_EMPTY), z),
                vec![evar(FRAME_REST, z)],
                z,
            )),
            Box::new(lifted),
            Box::new(call(evar(FAIL_OP, z), vec![], z)),
        ),
        z,
    );
    let dec = call(evar(DECODE_METHOD, z), vec![evar(FRAME_BODY, z)], z);
    let arm = Arm {
        pat: spat(
            Pattern::Tuple(vec![
                spat(Pattern::Var(FRAME_VALUE.to_string()), z),
                spat(Pattern::Var(FRAME_REST.to_string()), z),
            ]),
            z,
        ),
        guard: None,
        body: ok,
    };
    sp(Expr::Match(Box::new(dec), vec![arm]), z)
}

// Chain the adjacent upgrades from rung k up to the current type. The current rung
// is already the current type, so its chain is the value unchanged.
fn lift_to_current(
    sd: &StableDecl,
    rungs: &[RungInfo],
    k: usize,
    val: S<Expr>,
    z: Span,
) -> S<Expr> {
    let mut e = val;
    for j in k..rungs.len() - 1 {
        let up = names::stable_upgrade(&sd.name, &rungs[j].ver, &rungs[j + 1].ver);
        e = call(evar(&up, z), vec![e], z);
    }
    e
}

/// The predecessor rungs whose route to the current rung the migration table
/// promises, so the family-qualified `T.Vk.upgrade`/`.downgrade` are offered for
/// exactly these. An omitted route is not promised; a block with no table offers
/// no family members. Shared with the resolver, which needs the same set to map a
/// use site before desugar has expanded the block.
pub(crate) fn routes_to_current(sd: &StableDecl) -> BTreeSet<String> {
    let Some(cur) = sd.rungs.last() else {
        return BTreeSet::new();
    };
    sd.migrations
        .iter()
        .filter(|m| m.to == cur.name && m.from != cur.name)
        .map(|m| m.from.clone())
        .filter(|from| sd.rungs.iter().any(|r| &r.name == from))
        .collect()
}

// One adjacent edge's descriptive route mode, read off its migration row. Mode is
// recorded for review only; it never enters the compared identity, so an `auto`
// row and a handwritten converter that elaborate to the same Core stay equal.
fn edge_mode(sd: &StableDecl, from: &str, to: &str) -> &'static str {
    match edge_row(sd, from, to) {
        None => MODE_DEFAULT,
        Some(Migration {
            route: MigrationRoute::Auto,
            ..
        }) => MODE_AUTO,
        Some(Migration {
            route: MigrationRoute::Version(_),
            ..
        }) => MODE_MANUAL,
    }
}

// The downgrade loss paths a locked edge reports, for the drift diagnostic. An
// additive edge drops its newly added fields; the labels already ride inside the
// downgrade function's Core, so this is only their human-readable projection. A
// non-additive edge's loss is whatever its hand-written converter reports and is
// left to that converter's own hash.
fn edge_loss(hi: &RungInfo) -> Vec<String> {
    if hi.mutated.is_empty() {
        hi.new.iter().map(|(n, _)| n.clone()).collect()
    } else {
        Vec::new()
    }
}

// The canonical semantic hash of a generated converter, looked up by its
// compiler-owned name in the per-definition Core hashes. Present by construction
// once the family elaborates (the identity surface carries every top-level
// definition), so an absent entry is an internal invariant violation reported
// against the edge rather than a silent empty identity.
fn component_hash(
    sd: &StableDecl,
    from: &str,
    to: &str,
    fn_name: &str,
    defs: &Hashes,
) -> Result<String, TypeError> {
    defs.get(&Sym::new(fn_name))
        .map(|d| d.as_str().to_string())
        .ok_or_else(|| {
            ErrKind::StableMigrationBadEdge {
                block: sd.name.clone(),
                from: from.to_string(),
                to: to.to_string(),
                reason: format!("generated converter `{fn_name}` was not elaborated"),
            }
            .at(sd.span)
        })
}

/// The locked migration identity of one stable family, or `None` when the block
/// declares no `migrations` table (an unlockable, therefore unchecked, family).
///
/// The rung shape digests are structural; each adjacent edge's component hashes
/// are read from the per-definition Core hashes `defs`, so an `auto` edge and a
/// handwritten converter that elaborate to the same Core receive the same
/// identity. Longer routes commit their ordered adjacent edge identities without
/// rehashing composed bodies. This is the one home for the family's rung, edge,
/// and route logic; the driver only orchestrates parse, elaborate, hash, and
/// compare around it. The returned span is the block's, for the drift diagnostic.
///
/// # Errors
/// Fails on a malformed block (the same errors `resolve_rungs` reports) or an
/// internal absence of a generated converter from `defs`.
pub(crate) fn family_lock(
    sd: &StableDecl,
    defs: &Hashes,
) -> Result<Option<(FamilyLock, Span)>, TypeError> {
    if sd.migrations.is_empty() {
        return Ok(None);
    }
    let rungs = resolve_rungs(sd)?;
    let total = rungs.len();
    let shapes: Vec<RungShape> = rungs
        .iter()
        .enumerate()
        .map(|(idx, r)| RungShape {
            ver: r.ver.clone(),
            shape: rung_digest(&rung_data(sd, idx, r, &[])),
        })
        .collect();
    let mut edges = Vec::new();
    for k in 0..total.saturating_sub(1) {
        let lo = &rungs[k];
        let hi = &rungs[k + 1];
        let up_name = names::stable_upgrade(&sd.name, &lo.ver, &hi.ver);
        let down_name = names::stable_downgrade(&sd.name, &hi.ver, &lo.ver);
        let upgrade = component_hash(sd, &lo.ver, &hi.ver, &up_name, defs)?;
        let downgrade = component_hash(sd, &lo.ver, &hi.ver, &down_name, defs)?;
        let edge = edge_hash(
            &sd.name,
            &shapes[k].shape,
            &shapes[k + 1].shape,
            &upgrade,
            &downgrade,
        );
        edges.push(EdgeLock {
            from: lo.ver.clone(),
            to: hi.ver.clone(),
            mode: edge_mode(sd, &lo.ver, &hi.ver).to_string(),
            upgrade,
            downgrade,
            edge,
            loss: edge_loss(hi),
        });
    }
    let promised = routes_to_current(sd);
    let mut routes = Vec::new();
    for (k, r) in rungs.iter().enumerate() {
        // A route is recorded only when it spans more than one edge; an adjacent
        // promised predecessor's identity is already its edge above.
        if k + 2 >= total || !promised.contains(&r.ver) {
            continue;
        }
        let ordered: Vec<String> = edges[k..total - 1].iter().map(|e| e.edge.clone()).collect();
        let route = route_hash(
            &sd.name,
            &shapes[k].shape,
            &shapes[total - 1].shape,
            &ordered,
        );
        routes.push(RouteLock {
            from: r.ver.clone(),
            to: rungs[total - 1].ver.clone(),
            mode: edge_mode(sd, &r.ver, &rungs[total - 1].ver).to_string(),
            edges: ordered,
            route,
        });
    }
    Ok(Some((
        FamilyLock {
            rungs: shapes,
            edges,
            routes,
        },
        sd.span,
    )))
}

// The composed family routes for one block: for each predecessor rung the table
// promises a current route for, an `upgrade` that composes the adjacent upgrades
// and a `downgrade` that composes the adjacent downgrades, unioning their loss.
// These are the bodies behind `T.Vk.upgrade`/`.downgrade`.
fn family_route_fns(
    sd: &StableDecl,
    rungs: &[RungInfo],
    loss: &LossRef,
    libf: &impl Fn(&str) -> String,
) -> Vec<Decl> {
    let promised = routes_to_current(sd);
    let total = rungs.len();
    let cur_ty = Ty::Con(sd.name.clone(), Vec::new());
    let mut out = Vec::new();
    for (k, r) in rungs.iter().enumerate() {
        if k + 1 == total || !promised.contains(&r.ver) {
            continue;
        }
        let vk_ty = Ty::Con(rung_type(sd, k, total), Vec::new());
        out.push(family_upgrade(sd, rungs, k, &vk_ty, &cur_ty));
        out.push(family_downgrade(sd, rungs, k, &vk_ty, &cur_ty, loss, libf));
    }
    out
}

// The composed upgrade `T.Vk -> T` reachable as `T.Vk.upgrade`: the adjacent
// upgrades from rung k up to the current type.
fn family_upgrade(sd: &StableDecl, rungs: &[RungInfo], k: usize, vk_ty: &Ty, cur_ty: &Ty) -> Decl {
    let z = rungs[k].span;
    let x = names::stable_param(&rungs[k].ver);
    let body = lift_to_current(sd, rungs, k, evar(&x, z), z);
    mdecl(
        names::stable_route_upgrade(&sd.name, &rungs[k].ver),
        &x,
        vk_ty.clone(),
        cur_ty.clone(),
        body,
        z,
    )
}

// The composed downgrade `T -> (T.Vk, Wire.Loss)` reachable as `T.Vk.downgrade`:
// the adjacent downgrades from the current rung down to rung k, with their losses
// unioned into one.
fn family_downgrade(
    sd: &StableDecl,
    rungs: &[RungInfo],
    k: usize,
    vk_ty: &Ty,
    cur_ty: &Ty,
    lref: &LossRef,
    libf: &impl Fn(&str) -> String,
) -> Decl {
    let z = rungs[k].span;
    let cur = rungs.len() - 1;
    let x = names::stable_param(&rungs[cur].ver);
    let body = lower_to_rung(sd, rungs, k, evar(&x, z), libf, z);
    mdecl(
        names::stable_route_downgrade(&sd.name, &rungs[k].ver),
        &x,
        cur_ty.clone(),
        Ty::Tuple(vec![vk_ty.clone(), lref.ty.clone()]),
        body,
        z,
    )
}

// Fold the adjacent downgrades from the current rung down to rung k into one
// downgrade applied to `val`. Each `compose_downgrade` step runs the higher
// downgrade, then the lower one, unioning the two losses; a single step is the
// adjacent downgrade applied directly.
fn lower_to_rung(
    sd: &StableDecl,
    rungs: &[RungInfo],
    k: usize,
    val: S<Expr>,
    libf: &impl Fn(&str) -> String,
    z: Span,
) -> S<Expr> {
    let cur = rungs.len() - 1;
    let step = |hi: usize| {
        evar(
            &names::stable_downgrade(&sd.name, &rungs[hi].ver, &rungs[hi - 1].ver),
            z,
        )
    };
    let mut chain = step(cur);
    let mut hi = cur - 1;
    while hi > k {
        chain = call(
            evar(&libf(WIRE_COMPOSE_DOWNGRADE), z),
            vec![chain, step(hi)],
            z,
        );
        hi -= 1;
    }
    call(chain, vec![val], z)
}

// Reject a migration row that names an unknown rung, runs backward, or overrides a
// non-adjacent edge with a `version(...)` (a direct long route is a distinct edge,
// not part of the adjacent ladder). Non-adjacent `auto` rows are allowed: they
// promise the composed route without emitting a pairwise converter.
fn validate_migrations(sd: &StableDecl, rungs: &[RungInfo]) -> Result<(), TypeError> {
    let index = |ver: &str| rungs.iter().position(|r| r.ver == ver);
    for m in &sd.migrations {
        let bad = |reason: &str| {
            ErrKind::StableMigrationBadEdge {
                block: sd.name.clone(),
                from: m.from.clone(),
                to: m.to.clone(),
                reason: reason.to_string(),
            }
            .at(m.span)
        };
        let (Some(from), Some(to)) = (index(&m.from), index(&m.to)) else {
            return Err(bad("names a rung this block does not declare"));
        };
        if from >= to {
            return Err(bad("must run from an older rung to a newer one"));
        }
        if matches!(m.route, MigrationRoute::Version(_)) && to != from + 1 {
            return Err(bad(
                "version(...) overrides an adjacent edge; a non-adjacent route is `auto`",
            ));
        }
    }
    Ok(())
}
