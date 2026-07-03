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
//! The multi-parameter `Migrate(lo, hi)` class the design reserves needs grammar
//! that does not exist yet, so the ladder is plain functions here, not instances;
//! the seam is left for that class to fill. The version-dispatched decode (walking
//! an older frame up by its frame version) is the wire codec's concern: this pass
//! emits the ladder the codec composes, and `names::stable_decode_ladder` names
//! the entry point reserved for it.

use marginalia::Span;

use super::{call, evar, sp};
use crate::core::{shape_digests, HASH_PREFIX_HEX};
use crate::error::TypeError;
use crate::names;
use crate::syntax::ast::{
    ConvDir, Converter, Ctor, DataDecl, Decl, Expr, Fip, Param, Program, Rung, StableDecl,
    SynonymDecl, Ty, S,
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
    let in_scope: std::collections::BTreeSet<&str> =
        prog.classes.iter().map(|c| bare(&c.name)).collect();
    for sd in &blocks {
        if let Some(missing) = RUNG_REQUIRED.iter().find(|c| !in_scope.contains(**c)) {
            return Err(TypeError::Other {
                span: sd.span,
                msg: format!(
                    "`stable {}` needs the `{missing}` class in scope; add `import Wire (..)`",
                    sd.name
                ),
            });
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
        let fns = ladder_fns(sd, &rungs, &loss)?;
        prog.types.extend(datas);
        prog.fns.extend(fns);
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
        .find(|d| bare(&d.name) == LOSS_TYPE)
        .map_or(LOSS_TYPE, |d| d.name.as_str())
        .to_string();
    LossRef {
        ty: Ty::Con(canon.clone(), Vec::new()),
        ctor: canon,
    }
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
                let prev = out.last().filter(|p| &p.ver == base).ok_or_else(|| TypeError::Other {
                    span: r.span,
                    msg: format!(
                        "rung `{}` extends `..{base}`, which is not the rung directly above it in `stable {}`",
                        r.name, sd.name
                    ),
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
                    let def = f.default.clone().ok_or_else(|| TypeError::Other {
                        span: r.span,
                        msg: format!(
                            "new field `{}` in rung `{}` needs a default (`{} : {} = <expr>`) so the upgrade can fill it",
                            f.name,
                            r.name,
                            f.name,
                            crate::fmt::decl::fmt_ty(&f.ty)
                        ),
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

// The bare tail of a canonical class name (`Wire.Serialize` -> `Serialize`).
fn bare(name: &str) -> &str {
    name.rsplit_once(['.', '@']).map_or(name, |(_, n)| n)
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
    Err(TypeError::Other {
        span: r.span,
        msg: format!(
            "frozen format `{display}` changed shape\n  \
             its committed shape digest no longer matches. A shipped stable version is\n  \
             immutable: add a new rung (`V = {{ ..{}, ... }}`) instead of editing `{}`.\n  \
             If this rung never shipped, run `prism wire --accept {display}` to reseat it.",
            r.name, r.name
        ),
    })
}

// The committed shape-digest prefix of a rung's record type, in the exact scheme
// (`prism-core-hash-v1`) and truncation the stdlib goldens use.
pub(crate) fn rung_digest(data: &DataDecl) -> String {
    let shapes = shape_digests(std::slice::from_ref(data), &[]);
    shapes[&data.name][..HASH_PREFIX_HEX].to_string()
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
        konst: false,
        fip: Fip::No,
        replayable: false,
        no_alloc: false,
        no_alloc_bs: false,
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

// The whole adjacent ladder for one stable block.
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
        if hi.mutated.is_empty() {
            out.push(gen_upgrade(sd, lo, hi, &lo_ty, &hi_ty, &hi_ctor));
            out.push(gen_downgrade(sd, lo, hi, &lo_ty, &hi_ty, &lo_ctor, loss));
        } else {
            out.push(mut_upgrade(sd, lo, hi, &lo_ty, &hi_ty, &hi_ctor)?);
            out.push(mut_downgrade(sd, lo, hi, &lo_ty, &hi_ty, &lo_ctor, loss)?);
        }
    }
    Ok(out)
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
            TypeError::Other {
                span: sd.span,
                msg: format!(
                    "rung `{to}` retypes a field of `{from}`, a type mutation, so `stable {}` \
                     must give a `{word} {from} -> {to} = ...` converter",
                    sd.name
                ),
            }
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
