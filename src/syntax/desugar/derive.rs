//! Deriving Eq, Ord, and Show instances.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::synonyms::subst_ty;
use super::{call, eint, evar, lam1, sp, spat};
use crate::core::builtins::Builtin;
use crate::core::contract_digest;
use crate::error::{suggest, ErrKind, TypeError};
use crate::fmt::decl::fmt_ty;
use crate::names::{
    self, ARBITRARY_METHOD, CHILDREN_METHOD, DECODE_METHOD, ENCODE_METHOD, EQ_METHOD, FAIL_OP,
    FROM_JSON_METHOD, HASH_METHOD, INT_CMP, JSON_FIELD_FN, JSON_OBJ, JSON_POS_KEY, JSON_STR,
    JSON_TAG_KEY, ORD_METHOD, QC_ARB_GEN, QC_GEN_BIND, QC_GEN_CHOOSE, QC_GEN_CONST, QC_GEN_RESIZE,
    QC_GEN_RUN, REBUILD_METHOD, SHAPE_DIGEST_METHOD, SHOW_METHOD, TO_JSON_METHOD, WIRE_CAT,
    WIRE_EMPTY, WIRE_GET_TAG, WIRE_TAG,
};
use crate::syntax::ast::{
    Arm, BigInt, BinOp, Constraint, Ctor, CtorShape, DataDecl, Decl, Expr, Fip, InstanceDecl,
    IntLit, Param, PathOp, PathStep, Pattern, Program, Row, Suffix, Total, Ty, S,
};
use crate::types::{
    ARBITRARY_CLASS, CONS, EQ_CLASS, FROM_JSON_CLASS, HASH_CLASS, IDENTIFIABLE,
    IDENTIFIABLE_BUNDLE, LENS, LIST, NIL, NONE, OPTION, ORD_CLASS, PLATE_CLASS, SERIALIZE_CLASS,
    SHOW_CLASS, SOME, STABLE_CLASS, TO_JSON_CLASS,
};

// `deriving (Eq, Ord, Show)` synthesizes ordinary named instances here, so the
// class machinery checks and elaborates them like hand-written ones. The
// synthesized nodes carry the empty span: dispatch identity is the node's
// `NodeId` (assigned after desugar), so a method callee no longer needs a
// distinct span to key its dictionary.
const Z: Span = Span::empty(0);

// The binders every derived method's arm patterns use: the value being taken
// apart, and the prefix its fields are bound under (`_f0`, `_f1`). One home, so
// two derivations in this file cannot drift into meaning different things by the
// same name.
const SELF_BINDER: &str = "_x";
const FIELD_BINDER: &str = "_f";

// Expand the `deriving (Identifiable)` sugar and drop duplicate class names.
// `Identifiable` is not a class: it stands for the identity starter pack
// (`IDENTIFIABLE_BUNDLE`), whose members splice in at the marker's position, each
// carrying the marker's span for diagnostics. A class already named explicitly
// wins, so `deriving (Show, Identifiable)` derives one `Show`, not two. The result
// is the surface order with bundle members filling in behind their marker, so the
// expansion is a deterministic function of the written list.
fn expand_derives(deriving: &[(String, Span)]) -> Vec<(String, Span)> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut out: Vec<(String, Span)> = Vec::new();
    for (class, span) in deriving {
        if class == IDENTIFIABLE {
            for member in IDENTIFIABLE_BUNDLE {
                if seen.insert(member) {
                    out.push((member.to_string(), *span));
                }
            }
        } else if seen.insert(class.as_str()) {
            out.push((class.clone(), *span));
        }
    }
    out
}

pub(super) fn derive_instances(
    prog: &mut Program,
    external_classes: &BTreeMap<String, String>,
    external_values: &BTreeMap<String, String>,
) -> Result<(), TypeError> {
    // `Stable`'s sole method is its shape contract digest, a per-type constant the
    // compiler computes and injects. A hand-written instance could only restate that
    // digest (or lie about it), so `Stable` is derive-only: reject a user-authored
    // instance and point at the derive, closing the one way a frozen contract could
    // be forged. The rungs a `stable` block generates go through the derive path
    // below, not here, so they are unaffected.
    if let Some(i) = prog
        .instances
        .iter()
        .find(|i| names::bare_name(&i.class) == STABLE_CLASS)
    {
        return Err(ErrKind::StableHandWritten {
            head: fmt_ty(&i.head),
        }
        .at(i.span));
    }
    // Each in-scope class's bare name mapped to its canonical name. A derived
    // instance must reference the canonical `Module.Class` the instance store
    // keys on, even though `deriving` writes the bare name; a prelude/root class
    // maps to itself. When two imports share a bare class name the last wins,
    // which is harmless: a genuinely ambiguous derive is already an overlap the
    // checker reports on the resulting instances.
    let mut class_canon = external_classes.clone();
    class_canon.extend(prog.classes.iter().map(|class| {
        (
            names::bare_name(&class.name).to_string(),
            class.name.clone(),
        )
    }));
    // Each in-scope top-level function's bare name mapped to its canonical name.
    // A derived instance is built after name resolution, so a reference it emits
    // to a library function (the wire codec's byte builders, the property
    // generators) must already be the canonical `Module.fn`. Prelude functions and
    // the user type's own constructors are canonical bare names, so they need no
    // lookup; only the opt-in library helpers do.
    let mut value_canon = external_values.clone();
    value_canon.extend(prog.fns.iter().map(|function| {
        (
            names::bare_name(&function.name).to_string(),
            function.name.clone(),
        )
    }));
    // Include library constructors: a derived JSON encoder names
    // `JObj`/`JStr`, which are constructors of an opt-in module. In module mode
    // `external_values` already carries them; in whole-program mode every library
    // declaration is merged into `prog.types`, so they must be picked up here or
    // the emitted reference stays bare and resolves to nothing.
    value_canon.extend(
        prog.types
            .iter()
            .flat_map(|d| &d.ctors)
            .map(|c| (names::bare_name(&c.name).to_string(), c.name.clone())),
    );
    let lib = |name: &str| {
        value_canon
            .get(name)
            .map_or(name, String::as_str)
            .to_string()
    };
    // The types whose every component is provably serializable-frozen: those that
    // derive (or hand-write) a `Stable` instance. Read once so a `deriving
    // (Stable)` can check its fields structurally at the derive site.
    let stable_types = stable_type_set(prog);
    // The optic library's lens constructor, canonically spelled, when the module
    // imports it. Presence in the value namespace is the whole condition: a
    // derived field lens is one application of it, so where it is out of scope
    // `deriving (Lens)` synthesizes the accessor pair alone.
    let mk_lens = value_canon.get(names::OPTIC_MK_LENS).cloned();
    // Every data declaration in the merged program, by canonical name. A derived
    // `Plate` reads the whole set because seeing through the
    // carrier records an AST holds its nodes in (a match arm, a spanned wrapper)
    // is the difference between one derived traversal and one hand-written match
    // per carrier.
    let decls: BTreeMap<&str, &DataDecl> =
        prog.types.iter().map(|d| (d.name.as_str(), d)).collect();
    let mut out = Vec::new();
    let mut fns = Vec::new();
    // Which type claimed each accessor name, so a second record deriving `Lens`
    // over a field name the first one already took is reported here rather than
    // reaching Core as two definitions of one name at two types.
    let mut accessors: BTreeMap<String, String> = BTreeMap::new();
    for d in &prog.types {
        let derives = expand_derives(&d.deriving);
        for (class, cspan) in &derives {
            // Lens is not a class: it synthesizes plain `<f>_of` / `with_<f>`
            // accessors, so it bypasses the class-existence and instance paths.
            if class == LENS {
                fns.extend(derive_lens(
                    d,
                    *cspan,
                    mk_lens.as_deref(),
                    &mut accessors,
                    &value_canon,
                )?);
                continue;
            }
            let Some(canon) = class_canon.get(class.as_str()) else {
                return Err(ErrKind::UnknownDerivingClass {
                    class: class.clone(),
                }
                .at(*cspan)
                .maybe_help(suggest::suggestion(
                    class,
                    class_canon.keys().map(String::as_str),
                )));
            };
            out.push(match class.as_str() {
                EQ_CLASS => derive_eq(d, canon),
                ORD_CLASS => derive_ord(d, canon),
                SHOW_CLASS => derive_show(d, canon),
                HASH_CLASS => derive_hash(d, canon),
                SERIALIZE_CLASS => derive_serialize(d, canon, &lib),
                STABLE_CLASS => derive_stable(d, canon, *cspan, &stable_types)?,
                ARBITRARY_CLASS => derive_arbitrary(d, canon, &lib),
                TO_JSON_CLASS => derive_to_json(d, canon, &lib),
                FROM_JSON_CLASS => derive_from_json(d, canon, &lib),
                PLATE_CLASS => {
                    let (inst, helpers) = derive_plate(d, canon, &decls, *cspan)?;
                    fns.extend(helpers);
                    inst
                }
                other => {
                    return Err(ErrKind::NotDerivable {
                        class: other.to_string(),
                        ty: d.name.clone(),
                    }
                    .at(*cspan))
                }
            });
        }
    }
    prog.instances.extend(out);
    prog.fns.extend(fns);
    Ok(())
}

// `deriving (Lens)` on a record type synthesizes, per field, a getter
// `<f>_of(r) = r.f` and a functional setter `with_<f>(r, v) = T { ..r, f = v }`.
// These are ordinary functions (composable with `.`, FBIP-reused on unique
// values), not optic types.
//
// When the optic library is in scope, each field also gets the two of them paired
// into one first-class lens value named for its type and field (`Point.x` gives
// `point_x`), which is what composition and lens-taking functions need. The pair
// is what the optic type holds, so the value is the constructor applied to the
// two functions and nothing more: no constraint on any type parameter (a lens
// neither shows nor compares anything, so a phantom-branded record derives lenses
// demanding nothing of its brand), no effect, and no new kind of node.
//
// `mk_lens` is the canonical name of that constructor, or `None` when the module
// does not import the optic library, in which case only the accessor pair is
// synthesized: the accessors predate the library and cost nothing, so a program
// that never mentions lens values keeps working with no import.
//
// `accessors` carries the accessor names earlier derives in the same program
// already claimed, mapped to the type that claimed them. The pair is named after
// the field alone, so two records sharing a field name would define one name
// twice at two types; the collision is refused here, where both types can be
// named, rather than surfacing as an unbuildable Core witness.
//
// `existing` is every top-level value name already in scope before deriving (the
// user's own functions, a module's opened names, constructors). A synthesized
// accessor whose name is already bound there would define that name a second time
// in the one flat namespace: against a hand-written function that reaches Core as
// two definitions of one name, against a library name it silently resolves to
// whichever the merge kept. Both are refused with a named diagnostic so neither
// an ICE nor an accidental winner can result.
fn derive_lens(
    d: &DataDecl,
    cspan: Span,
    mk_lens: Option<&str>,
    accessors: &mut BTreeMap<String, String>,
    existing: &BTreeMap<String, String>,
) -> Result<Vec<Decl>, TypeError> {
    let z = Z;
    let [ctor] = d.ctors.as_slice() else {
        return Err(ErrKind::LensNeedsRecord { ty: d.name.clone() }.at(cspan));
    };
    let Some(fields) = &ctor.fields else {
        return Err(ErrKind::LensNeedsNamedFields {
            ty: d.name.clone(),
            ctor: ctor.name.clone(),
        }
        .at(cspan));
    };
    let self_ty = Ty::Con(
        d.name.clone(),
        d.params.iter().cloned().map(Ty::Var).collect(),
    );
    let mut out = Vec::new();
    for (f, fty) in fields {
        let getter = names::lens_getter(f);
        let setter = names::lens_setter(f);
        // The first type to claim a name owns it, so the report is the same
        // whichever of the two is declared first: it always names the claimant.
        let claimed = accessors.get(&getter).or_else(|| accessors.get(&setter));
        if let Some(prior) = claimed.filter(|prior| *prior != &d.name) {
            return Err(ErrKind::LensAccessorCollision {
                ty: d.name.clone(),
                prior_ty: prior.clone(),
                field: f.clone(),
                getter: getter.clone(),
                setter: setter.clone(),
            }
            .at(cspan)
            .with_help(format!(
                "rename `{f}` on one of the two types, or drop `Lens` from one of the \
                 `deriving` clauses and write the accessors by hand"
            ))
            .note(format!(
                "the accessor pair is named after the field alone, and top-level names \
                 share one flat namespace that holds one definition per name. The lens \
                 values are named after their type, so `{}` and `{}` do not collide and \
                 that half of the derivation is unaffected.",
                names::lens_value(prior, f),
                names::lens_value(&d.name, f)
            )));
        }
        accessors.insert(getter.clone(), d.name.clone());
        accessors.insert(setter.clone(), d.name.clone());
        // A synthesized accessor may not take a name a pre-existing top-level
        // value already holds; deriving over the two accessor names alone would
        // otherwise clobber a hand-written function or lose to a library one.
        for name in [&getter, &setter] {
            if existing.contains_key(name) {
                return Err(shadows_value(d, f, name, cspan));
            }
        }
        // Both accessors are built twice over the same receiver expression: once
        // named, once anonymous inside the lens value below.
        let read = |r| sp(Expr::FieldAccess(Box::new(r), f.clone()), z);
        let write = |r| {
            sp(
                Expr::RecordUpdatePath(
                    Box::new(r),
                    vec![(vec![PathStep::Field(f.clone())], PathOp::Set(evar("_v", z)))],
                ),
                z,
            )
        };
        let mut g = mdecl(&getter, &["_r"], read(evar("_r", z)), z);
        g.params[0].ty = Some(self_ty.clone());
        g.ret = Some(fty.clone());
        out.push(g);
        let mut s = mdecl(&setter, &["_r", "_v"], write(evar("_r", z)), z);
        s.params[0].ty = Some(self_ty.clone());
        s.params[1].ty = Some(fty.clone());
        s.ret = Some(self_ty.clone());
        out.push(s);
        if let Some(mk) = mk_lens {
            let lv = names::lens_value(&d.name, f);
            if existing.contains_key(&lv) {
                return Err(shadows_value(d, f, &lv, cspan));
            }
            // The lens holds its own copy of the two accessors rather than naming
            // them: the accessor names carry the field but not the type, so two
            // records sharing a field name share their accessors, and a lens that
            // referred to them by name would silently be a lens into whichever
            // record was declared last. The receiver is ascribed because a lambda
            // parameter is otherwise unknown at the field access, and which record
            // a field belongs to is what resolves the access.
            let recv = || sp(Expr::Ann(Box::new(evar("_r", z)), self_ty.clone()), z);
            let read = lamn(&["_r"], read(recv()), z);
            let write = lamn(&["_r", "_v"], write(recv()), z);
            // A top-level value, not a function: it is inlined at each use site,
            // so a lens on a polymorphic record is as general as its fields are
            // without an annotation naming the optic type here.
            let mut l = mdecl(&lv, &[], call(evar(mk, z), vec![read, write], z), z);
            l.konst = true;
            out.push(l);
        }
    }
    Ok(out)
}

// A derived lens accessor `name` (for `field` of type `d`) collides with a
// top-level value that already holds that name. The help points at the two ways
// out that leave the flat namespace with one definition per name.
fn shadows_value(d: &DataDecl, field: &str, name: &str, cspan: Span) -> TypeError {
    ErrKind::LensAccessorShadowsValue {
        ty: d.name.clone(),
        field: field.to_string(),
        name: name.to_string(),
    }
    .at(cspan)
    .with_help(format!(
        "rename `{field}`, or drop `Lens` from the `deriving` clause and write the \
         accessor by hand under a name of your own"
    ))
    .note(
        "top-level names share one flat namespace that holds one definition per \
         name, so a synthesized accessor cannot reuse a name already bound",
    )
}

fn fvars(pre: &str, n: usize, z: Span) -> Vec<S<Pattern>> {
    (0..n)
        .map(|i| spat(Pattern::Var(format!("{pre}{i}")), z))
        .collect()
}

// One derived instance. `class` is the canonical class name (`Module.Class` for
// an imported class, a bare name for a prelude one); the context requires the
// same class of each type argument a field mentions, so a derived instance for
// `T(a)` reads `given C(a)`. `prefix` disambiguates the instance's own name.
fn inst_skel(d: &DataDecl, class: &str, prefix: &str, methods: Vec<Decl>, z: Span) -> InstanceDecl {
    inst_with_ctx(d, class, prefix, methods, z, Some(class))
}

// Every type-variable name occurring syntactically in a type expression: a bare
// variable, the head of a higher-kinded application (`f(a)` occurs `f` as well as
// `a`), and the tail of an effect row (`! {E | e}` occurs `e`). Nesting is looked
// through, so a variable is found however deep the constructors bury it. A name
// bound by a nested `forall` counts too: the walk is deliberately syntactic, and
// a shadowed name can only over-approximate, which is the conservative direction.
fn ty_var_names(t: &Ty, out: &mut BTreeSet<String>) {
    match t {
        Ty::Var(n) | Ty::App(n, _) => {
            out.insert(n.clone());
        }
        Ty::Fun(_, Row::Cons(_, Some(tail)), _) | Ty::RowLit(Row::Cons(_, Some(tail))) => {
            out.insert(tail.clone());
        }
        _ => {}
    }
    t.each_child(&mut |c| ty_var_names(c, out));
}

// The type parameters a derived instance constrains: those a constructor's field
// types actually mention. A phantom parameter (a phase brand, a unit marker) can
// reach no derived method, so requiring an instance of it would reject the type
// at every argument that has none, for a dictionary nothing could call. Occurrence
// is transitive through type application, so a field typed `Option(List(a))` still
// constrains `a`, and a recursive constructor's own occurrences are just more
// field types.
fn constrained_params(d: &DataDecl) -> Vec<&String> {
    let mut occurring = BTreeSet::new();
    for c in &d.ctors {
        for a in &c.args {
            ty_var_names(a, &mut occurring);
        }
    }
    d.params
        .iter()
        .filter(|p| occurring.contains(p.as_str()))
        .collect()
}

// As `inst_skel`, with the per-parameter context named separately. A derived
// method that only ever touches values of the derived type itself (rather than
// of its arguments) needs no context at all: `Plate(T(a))` finds `T(a)` subvalues
// structurally and never traverses an `a`, so requiring `given Plate(a)` would
// reject `T(Int)` for no reason.
fn inst_with_ctx(
    d: &DataDecl,
    class: &str,
    prefix: &str,
    methods: Vec<Decl>,
    z: Span,
    ctx: Option<&str>,
) -> InstanceDecl {
    let params = constrained_params(d);
    InstanceDecl {
        name: format!("{prefix}{}", d.name),
        class: class.into(),
        head: Ty::Con(
            d.name.clone(),
            d.params.iter().map(|p| Ty::Var(p.clone())).collect(),
        ),
        context: ctx
            .into_iter()
            .flat_map(|c| {
                params.iter().map(move |p| Constraint {
                    class: c.into(),
                    ty: Ty::Var((*p).clone()),
                    span: z,
                })
            })
            .collect(),
        methods,
        // The data type's canonical name carries its defining module, so a
        // derived instance is anchored to the same module as its type.
        module: crate::names::module_of(&d.name).to_string(),
        span: z,
    }
}

// A lambda of any arity, for the cases `lam1` cannot express.
fn lamn(params: &[&str], body: S<Expr>, z: Span) -> S<Expr> {
    let ps = params
        .iter()
        .map(|name| Param {
            name: (*name).into(),
            ty: None,
            borrow: false,
            pat: None,
            default: None,
        })
        .collect();
    sp(Expr::Lam(ps, Box::new(body)), z)
}

fn mdecl(name: &str, params: &[&str], body: S<Expr>, z: Span) -> Decl {
    Decl {
        name: name.into(),
        params: params
            .iter()
            .map(|p| Param {
                name: (*p).into(),
                ty: None,
                borrow: false,
                pat: None,
                default: None,
            })
            .collect(),
        ret: None,
        eff: None,
        eff_tail: None,
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
        bounded_stack: false,
        linear: false,
        span: z,
    }
}

fn pair_match(d: &DataDecl, z: Span, mut arm_body: impl FnMut(&str, usize) -> S<Expr>) -> Vec<Arm> {
    d.ctors
        .iter()
        .map(|c| Arm {
            pat: spat(
                Pattern::Tuple(vec![
                    spat(
                        Pattern::Ctor(c.name.clone(), fvars("_l", c.args.len(), z)),
                        z,
                    ),
                    spat(
                        Pattern::Ctor(c.name.clone(), fvars("_r", c.args.len(), z)),
                        z,
                    ),
                ]),
                z,
            ),
            guard: None,
            body: arm_body(&c.name, c.args.len()),
            alt: false,
        })
        .collect()
}

fn derive_eq(d: &DataDecl, class: &str) -> InstanceDecl {
    let z = Z;
    let mut arms = pair_match(d, z, |_, n| {
        let mut body = sp(Expr::Bool(true), z);
        for i in (0..n).rev() {
            let f = call(
                evar(EQ_METHOD, Z),
                vec![evar(&format!("_l{i}"), z), evar(&format!("_r{i}"), z)],
                z,
            );
            body = if i + 1 == n {
                f
            } else {
                sp(Expr::Bin(BinOp::And, Box::new(f), Box::new(body)), z)
            };
        }
        body
    });
    if d.ctors.len() > 1 {
        arms.push(Arm {
            pat: spat(Pattern::Wild, z),
            guard: None,
            body: sp(Expr::Bool(false), z),
            alt: false,
        });
    }
    let scrut = sp(Expr::Tuple(vec![evar(SELF_BINDER, z), evar("_y", z)]), z);
    let body = sp(Expr::Match(Box::new(scrut), arms), z);
    inst_skel(
        d,
        class,
        "eq",
        vec![mdecl(EQ_METHOD, &[SELF_BINDER, "_y"], body, z)],
        z,
    )
}

// Lexicographic compare: within a constructor, `cmp` the fields left to right
// and stop at the first non-equal result (built inner-first, so the loop runs
// fields in reverse); across distinct constructors, fall back to comparing
// declaration-order tags.
fn derive_ord(d: &DataDecl, class: &str) -> InstanceDecl {
    let z = Z;
    let mut arms = pair_match(d, z, |_, n| {
        let mut body = eint(0, z);
        for i in (0..n).rev() {
            let f = call(
                evar(ORD_METHOD, Z),
                vec![evar(&format!("_l{i}"), z), evar(&format!("_r{i}"), z)],
                z,
            );
            body = if i + 1 == n {
                f
            } else {
                sp(
                    Expr::Match(
                        Box::new(f),
                        vec![
                            Arm {
                                pat: spat(
                                    Pattern::Int(IntLit {
                                        value: BigInt::from(0usize),
                                        suffix: Suffix::None,
                                    }),
                                    z,
                                ),
                                guard: None,
                                body,
                                alt: false,
                            },
                            Arm {
                                pat: spat(Pattern::Var("_c".into()), z),
                                guard: None,
                                body: evar("_c", z),
                                alt: false,
                            },
                        ],
                    ),
                    z,
                )
            };
        }
        body
    });
    let tag = |v: &str| {
        let tarms = d
            .ctors
            .iter()
            .enumerate()
            .map(|(i, c)| Arm {
                pat: spat(
                    Pattern::Ctor(
                        c.name.clone(),
                        c.args.iter().map(|_| spat(Pattern::Wild, z)).collect(),
                    ),
                    z,
                ),
                guard: None,
                body: eint(i, z),
                alt: false,
            })
            .collect();
        sp(Expr::Match(Box::new(evar(v, z)), tarms), z)
    };
    if d.ctors.len() > 1 {
        arms.push(Arm {
            pat: spat(Pattern::Wild, z),
            guard: None,
            body: call(evar(INT_CMP, z), vec![tag(SELF_BINDER), tag("_y")], z),
            alt: false,
        });
    }
    let scrut = sp(Expr::Tuple(vec![evar(SELF_BINDER, z), evar("_y", z)]), z);
    let body = sp(Expr::Match(Box::new(scrut), arms), z);
    inst_skel(
        d,
        class,
        "ord",
        vec![mdecl(ORD_METHOD, &[SELF_BINDER, "_y"], body, z)],
        z,
    )
}

// Structural `show`, matching the canonical format the print-site generator in
// `core/elaborate/show.rs` also produces (the two are kept in lockstep by the
// `print_show_consistency` snapshot gate): a nullary constructor prints its
// bare name, a positional one prints `Name(f0, f1)`, and a record one prints
// `Name { field0 = v0, field1 = v1 }`. Each field recurses through `show`, so
// nested strings are quoted and nested records carry their own field names.
fn derive_show(d: &DataDecl, class: &str) -> InstanceDecl {
    let z = Z;
    let concat = |a: S<Expr>, b: S<Expr>| call(evar(Builtin::Concat.name(), z), vec![a, b], z);
    let shown = |i: usize| {
        call(
            evar(SHOW_METHOD, Z),
            vec![evar(&format!("{FIELD_BINDER}{i}"), z)],
            z,
        )
    };
    let arms = d
        .ctors
        .iter()
        .map(|c| {
            let n = c.args.len();
            let body = if n == 0 {
                sp(Expr::Str(c.name.clone()), z)
            } else {
                match c.shape() {
                    // Record constructor: `Name { f0 = v0, f1 = v1 }`.
                    CtorShape::Record(fields) => {
                        let mut acc = sp(Expr::Str(" }".into()), z);
                        for (i, (fname, _)) in fields.iter().enumerate().rev() {
                            let sep = if i > 0 { ", " } else { " { " };
                            acc = concat(
                                concat(sp(Expr::Str(format!("{sep}{fname} = ")), z), shown(i)),
                                acc,
                            );
                        }
                        concat(sp(Expr::Str(c.name.clone()), z), acc)
                    }
                    CtorShape::Positional(_) => {
                        let mut acc = sp(Expr::Str(")".into()), z);
                        for i in (0..n).rev() {
                            acc = concat(shown(i), acc);
                            if i > 0 {
                                acc = concat(sp(Expr::Str(", ".into()), z), acc);
                            }
                        }
                        concat(sp(Expr::Str(format!("{}(", c.name)), z), acc)
                    }
                }
            };
            Arm {
                pat: spat(Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, n, z)), z),
                guard: None,
                body,
                alt: false,
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, z)), arms), z);
    inst_skel(
        d,
        class,
        "show",
        vec![mdecl(SHOW_METHOD, &[SELF_BINDER], body, z)],
        z,
    )
}

// The canonical value-encoding prefix for one constructor, mirroring the
// discipline of `src/core/shape.rs` / `src/core/hash.rs`: a length-prefixed name
// and its declaration-order tag. Length-prefixing keeps two constructors whose
// names share a prefix from colliding, and the tag pins the sum position.
fn ctor_token(name: &str, tag: usize) -> String {
    format!("c{}:{}/{}", name.len(), name, tag)
}

// Structural content hash: a value folds to the blake3 of its constructor token
// followed by its fields' own hashes (each a fixed-width hex digest, so the
// concatenation is unambiguous). This is a Merkle fold in the same scheme as the
// compiler's content addressing, so structurally equal values hash equal, for
// free, on both backends. Leaf instances (`Int`, `String`, ...) live in the
// prelude beside the `Hash` class.
fn derive_hash(d: &DataDecl, class: &str) -> InstanceDecl {
    let z = Z;
    let cat = |a: S<Expr>, b: S<Expr>| call(evar(Builtin::Concat.name(), z), vec![a, b], z);
    let hashed = |i: usize| {
        call(
            evar(HASH_METHOD, z),
            vec![evar(&format!("{FIELD_BINDER}{i}"), z)],
            z,
        )
    };
    let arms = d
        .ctors
        .iter()
        .enumerate()
        .map(|(tag, c)| {
            let n = c.args.len();
            let token = sp(Expr::Str(ctor_token(&c.name, tag)), z);
            let enc = if n == 0 {
                token
            } else {
                let mut rest = hashed(n - 1);
                for i in (0..n - 1).rev() {
                    rest = cat(hashed(i), rest);
                }
                cat(token, rest)
            };
            Arm {
                pat: spat(Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, n, z)), z),
                guard: None,
                body: call(evar(Builtin::Blake3.name(), z), vec![enc], z),
                alt: false,
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, z)), arms), z);
    inst_skel(
        d,
        class,
        "hash",
        vec![mdecl(HASH_METHOD, &[SELF_BINDER], body, z)],
        z,
    )
}

// `encode`: the compact positional body. A product writes its fields in
// declaration order; a sum prefixes the constructor tag. `wire_cat`/`wire_tag`/
// `wire_empty` are the codec's byte builders (their bodies live in the wire
// library), so the derivation names the shape and the library owns the bytes.
fn encode_fields(n: usize, lib: &impl Fn(&str) -> String, z: Span) -> S<Expr> {
    let mut acc = evar(&lib(WIRE_EMPTY), z);
    for i in (0..n).rev() {
        let enc = call(
            evar(ENCODE_METHOD, z),
            vec![evar(&format!("{FIELD_BINDER}{i}"), z)],
            z,
        );
        acc = call(evar(&lib(WIRE_CAT), z), vec![enc, acc], z);
    }
    acc
}

// Apply a constructor to the already-decoded field binders `_a0.._a{n-1}`.
fn ctor_apply(c: &Ctor, z: Span) -> S<Expr> {
    let head = evar(&c.name, z);
    if c.args.is_empty() {
        head
    } else {
        let args = (0..c.args.len())
            .map(|i| evar(&format!("_a{i}"), z))
            .collect();
        call(head, args, z)
    }
}

// `decode`: a positional reader threading the remaining bytes. Field `i` is read
// from `cur`, binding its value `_a{i}` and the leftover `_r{i+1}` that the next
// field reads from; the base case pairs the rebuilt constructor with the bytes
// that follow it. Each `decode` resolves to the field type's own instance.
fn decode_read(c: &Ctor, i: usize, cur: &str, z: Span) -> S<Expr> {
    if i == c.args.len() {
        return sp(Expr::Tuple(vec![ctor_apply(c, z), evar(cur, z)]), z);
    }
    let next = format!("_r{}", i + 1);
    let dec = call(evar(DECODE_METHOD, z), vec![evar(cur, z)], z);
    let arm = Arm {
        pat: spat(
            Pattern::Tuple(vec![
                spat(Pattern::Var(format!("_a{i}")), z),
                spat(Pattern::Var(next.clone()), z),
            ]),
            z,
        ),
        guard: None,
        body: decode_read(c, i + 1, &next, z),
        alt: false,
    };
    sp(Expr::Match(Box::new(dec), vec![arm]), z)
}

// Structural codec. A single-constructor product encodes/decodes its fields with
// no tag; a sum tags each constructor by its declaration order and decodes by
// peeling that tag first, failing on an out-of-range tag (hostile input is one
// ordinary `Fail`, never a panic).
fn derive_serialize(d: &DataDecl, class: &str, lib: &impl Fn(&str) -> String) -> InstanceDecl {
    let z = Z;
    let multi = d.ctors.len() > 1;
    let enc_arms = d
        .ctors
        .iter()
        .enumerate()
        .map(|(tag, c)| {
            let fields = encode_fields(c.args.len(), lib, z);
            let body = if multi {
                let tagb = call(evar(&lib(WIRE_TAG), z), vec![eint(tag, z)], z);
                call(evar(&lib(WIRE_CAT), z), vec![tagb, fields], z)
            } else {
                fields
            };
            Arm {
                pat: spat(
                    Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, c.args.len(), z)),
                    z,
                ),
                guard: None,
                body,
                alt: false,
            }
        })
        .collect();
    let enc_body = sp(Expr::Match(Box::new(evar(SELF_BINDER, z)), enc_arms), z);
    let encode = mdecl(ENCODE_METHOD, &[SELF_BINDER], enc_body, z);

    let dec_body = if multi {
        let mut tag_arms: Vec<Arm> = d
            .ctors
            .iter()
            .enumerate()
            .map(|(tag, c)| Arm {
                pat: spat(
                    Pattern::Int(IntLit {
                        value: BigInt::from(tag),
                        suffix: Suffix::None,
                    }),
                    z,
                ),
                guard: None,
                body: decode_read(c, 0, "_r0", z),
                alt: false,
            })
            .collect();
        tag_arms.push(Arm {
            pat: spat(Pattern::Wild, z),
            guard: None,
            body: call(evar(FAIL_OP, z), vec![], z),
            alt: false,
        });
        let inner = sp(Expr::Match(Box::new(evar("_t", z)), tag_arms), z);
        let outer = Arm {
            pat: spat(
                Pattern::Tuple(vec![
                    spat(Pattern::Var("_t".into()), z),
                    spat(Pattern::Var("_r0".into()), z),
                ]),
                z,
            ),
            guard: None,
            body: inner,
            alt: false,
        };
        let gettag = call(evar(&lib(WIRE_GET_TAG), z), vec![evar("_bs", z)], z);
        sp(Expr::Match(Box::new(gettag), vec![outer]), z)
    } else if let Some(c0) = d.ctors.first() {
        decode_read(c0, 0, "_bs", z)
    } else {
        // An uninhabited type has no value to decode; failing is the only
        // honest reading of any input (never a panic in the compiler).
        call(evar(FAIL_OP, z), vec![], z)
    };
    let decode = mdecl(DECODE_METHOD, &["_bs"], dec_body, z);
    inst_skel(d, class, "serialize", vec![encode, decode], z)
}

// `deriving (ToJson, FromJson)` maps a declaration onto the dynamic JSON tree,
// for a type whose schema is the declaration itself. It is not the wire codec: a
// `Serialize` byte format is frozen and versioned, while a JSON document is read
// by something that was not compiled against this program, so the encoding is
// self-describing rather than compact.
//
// One constructor becomes one object. A record constructor's keys are its
// declared field names; a positional one's are its argument positions (`_0`,
// `_1`), which is the only name the declaration offers. A sum additionally
// carries its constructor's bare name under `$`, a key no field name can spell,
// so a document names the variant it holds rather than an unstable numeric index.
// A single-constructor type has
// nothing to discriminate and carries no tag.
//
// Order is the declaration's throughout, so one value has one tree; the canonical
// encoder sorts keys on the way out, so it also has one string.

// Binders of a derived JSON conversion: the tree being read, an object's
// members, and a decoded tag. The value being encoded uses `SELF_BINDER`, as
// every other derivation's arms do.
const JSON_TREE: &str = "_j";
const JSON_MEMBERS: &str = "_kvs";
const JSON_TAG: &str = "_tag";

// The key one constructor argument is carried under: its declared field name, or
// its position when the constructor is positional.
fn json_key(c: &Ctor, i: usize) -> String {
    match c.shape() {
        CtorShape::Record(fs) => fs[i].0.clone(),
        CtorShape::Positional(_) => format!("{JSON_POS_KEY}{i}"),
    }
}

// `("key", value)`, one member of a JSON object.
fn json_member(key: &str, value: S<Expr>, z: Span) -> S<Expr> {
    sp(Expr::Tuple(vec![sp(Expr::Str(key.into()), z), value]), z)
}

// A list literal, built from the prelude constructors as the other derivations do.
fn json_list(items: Vec<S<Expr>>, z: Span) -> S<Expr> {
    items.into_iter().rev().fold(evar(NIL, z), |tail, item| {
        call(evar(CONS, z), vec![item, tail], z)
    })
}

// `to_json`: one constructor to one object, tagged only when there is a choice.
fn derive_to_json(d: &DataDecl, class: &str, lib: &impl Fn(&str) -> String) -> InstanceDecl {
    let z = Z;
    let tagged = d.ctors.len() > 1;
    let arms = d
        .ctors
        .iter()
        .map(|c| {
            let tag = tagged.then(|| {
                json_member(
                    JSON_TAG_KEY,
                    call(
                        evar(&lib(JSON_STR), z),
                        vec![sp(Expr::Str(names::bare_name(&c.name).into()), z)],
                        z,
                    ),
                    z,
                )
            });
            let fields = (0..c.args.len()).map(|i| {
                json_member(
                    &json_key(c, i),
                    call(
                        evar(TO_JSON_METHOD, z),
                        vec![evar(&format!("{FIELD_BINDER}{i}"), z)],
                        z,
                    ),
                    z,
                )
            });
            Arm {
                pat: spat(
                    Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, c.args.len(), z)),
                    z,
                ),
                guard: None,
                body: call(
                    evar(&lib(JSON_OBJ), z),
                    vec![json_list(tag.into_iter().chain(fields).collect(), z)],
                    z,
                ),
                alt: false,
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, z)), arms), z);
    inst_skel(
        d,
        class,
        "toJson",
        vec![mdecl(TO_JSON_METHOD, &[SELF_BINDER], body, z)],
        z,
    )
}

// One constructor rebuilt from the members bound to `_kvs`: each argument is the
// decoding of its own key's member, so a missing key, a key of the wrong shape,
// and a nested field that will not decode all leave through the same `Fail`.
fn json_read(c: &Ctor, lib: &impl Fn(&str) -> String, z: Span) -> S<Expr> {
    let args = (0..c.args.len())
        .map(|i| {
            let member = call(
                evar(&lib(JSON_FIELD_FN), z),
                vec![evar(JSON_MEMBERS, z), sp(Expr::Str(json_key(c, i)), z)],
                z,
            );
            call(evar(FROM_JSON_METHOD, z), vec![member], z)
        })
        .collect::<Vec<_>>();
    if args.is_empty() {
        evar(&c.name, z)
    } else {
        call(evar(&c.name, z), args, z)
    }
}

// `from_json`: an object, read by the same keys the encoder wrote. A sum reads
// its tag first and compares it against each constructor's name in declaration
// order; anything that is not an object, carries no tag, or names a constructor
// this type does not have is one `Fail`.
fn derive_from_json(d: &DataDecl, class: &str, lib: &impl Fn(&str) -> String) -> InstanceDecl {
    let z = Z;
    let failed = || call(evar(FAIL_OP, z), vec![], z);
    let obj = if d.ctors.len() > 1 {
        let dispatch = d.ctors.iter().rev().fold(failed(), |otherwise, c| {
            let hit = sp(
                Expr::Bin(
                    BinOp::Eq,
                    Box::new(evar(JSON_TAG, z)),
                    Box::new(sp(Expr::Str(names::bare_name(&c.name).into()), z)),
                ),
                z,
            );
            sp(
                Expr::If(
                    Box::new(hit),
                    Box::new(json_read(c, lib, z)),
                    Box::new(otherwise),
                ),
                z,
            )
        });
        let read_tag = call(
            evar(&lib(JSON_FIELD_FN), z),
            vec![evar(JSON_MEMBERS, z), sp(Expr::Str(JSON_TAG_KEY.into()), z)],
            z,
        );
        sp(
            Expr::Match(
                Box::new(read_tag),
                vec![
                    Arm {
                        pat: spat(
                            Pattern::Ctor(
                                lib(JSON_STR),
                                vec![spat(Pattern::Var(JSON_TAG.into()), z)],
                            ),
                            z,
                        ),
                        guard: None,
                        body: dispatch,
                        alt: false,
                    },
                    Arm {
                        pat: spat(Pattern::Wild, z),
                        guard: None,
                        body: failed(),
                        alt: false,
                    },
                ],
            ),
            z,
        )
    } else if let Some(c0) = d.ctors.first() {
        json_read(c0, lib, z)
    } else {
        // An uninhabited type has no value to decode, so no document names one.
        failed()
    };
    let body = sp(
        Expr::Match(
            Box::new(evar(JSON_TREE, z)),
            vec![
                Arm {
                    pat: spat(
                        Pattern::Ctor(
                            lib(JSON_OBJ),
                            vec![spat(Pattern::Var(JSON_MEMBERS.into()), z)],
                        ),
                        z,
                    ),
                    guard: None,
                    body: obj,
                    alt: false,
                },
                Arm {
                    pat: spat(Pattern::Wild, z),
                    guard: None,
                    body: failed(),
                    alt: false,
                },
            ],
        ),
        z,
    );
    inst_skel(
        d,
        class,
        "fromJson",
        vec![mdecl(FROM_JSON_METHOD, &[JSON_TREE], body, z)],
        z,
    )
}

// The set of types whose format is provably frozen-serializable: those that
// derive or hand-write a `Stable` instance. Scalars are always stable and a type
// variable defers to the derived instance's `given Stable(a)` context, so only
// named types need this lookup (see `is_stable`).
fn stable_type_set(prog: &Program) -> BTreeSet<String> {
    let mut s = BTreeSet::new();
    for t in &prog.types {
        if t.deriving.iter().any(|(c, _)| c == STABLE_CLASS) {
            s.insert(t.name.clone());
        }
    }
    for i in &prog.instances {
        if names::bare_name(&i.class) == STABLE_CLASS {
            if let Ty::Con(n, _) = &i.head {
                s.insert(n.clone());
            }
        }
    }
    s
}

// Whether a component type is `Stable`. A scalar always is, and a type variable
// is taken stable because the derived instance requires `Stable` of every
// parameter in its context; a product/named type is stable when its parts are.
// A function, higher-kinded application, or quantified type is never
// frozen-serializable.
fn is_stable(t: &Ty, set: &BTreeSet<String>) -> bool {
    match t {
        Ty::Int
        | Ty::I64
        | Ty::U64
        | Ty::Bool
        | Ty::Unit
        | Ty::Float
        | Ty::Char
        | Ty::Str
        | Ty::Var(_)
        // A dimension index is erased and carries no serialized component, so it
        // imposes no `Stable` obligation on the enclosing type.
        | Ty::Nat(_) => true,
        Ty::Tuple(ts) => ts.iter().all(|x| is_stable(x, set)),
        Ty::Con(n, args) => set.contains(n) && args.iter().all(|x| is_stable(x, set)),
        // A usage row is rejected in desugar before deriving; a type carrying
        // one is never frozen-serializable. Unboxed products have no derived
        // instances, so they are not frozen-serializable either.
        Ty::App(..) | Ty::Fun(..) | Ty::Forall(..) | Ty::State(_) | Ty::RowLit(_)
        | Ty::Coeffect(..) | Ty::UnboxedTuple(_) | Ty::UnboxedRecord(_) => false,
    }
}

// `Stable` proves a frozen format and carries one method, `shape_digest_of`: the
// type's shape contract digest, injected here as a string literal from the single
// digest computation (`core::contract_digest`), so no downstream code hand-threads
// that digest into the wire envelope. The proof obligation is unchanged: every
// field must itself be `Stable`, or this is a compile error at the derive site
// naming the offending field and its type. The injected literal lands in the
// instance's elaborated Core, so it is content-hashed for free.
fn derive_stable(
    d: &DataDecl,
    class: &str,
    cspan: Span,
    set: &BTreeSet<String>,
) -> Result<InstanceDecl, TypeError> {
    for c in &d.ctors {
        for (i, arg) in c.args.iter().enumerate() {
            if !is_stable(arg, set) {
                return Err(ErrKind::StableFieldNotStable {
                    ty: names::bare_name(&d.name).to_string(),
                    field: field_label(c, i),
                    field_ty: fmt_ty(arg),
                }
                .at(cspan));
            }
        }
    }
    // The method ignores its argument (the digest is a compile-time constant of the
    // type); the argument exists only so dispatch resolves the instance by value.
    let digest = sp(Expr::Str(contract_digest(d)), Z);
    let method = mdecl(SHAPE_DIGEST_METHOD, &[SELF_BINDER], digest, Z);
    Ok(inst_skel(d, class, "stable", vec![method], Z))
}

// How a diagnostic names one constructor argument: by field name on a record
// constructor, by position on a positional one.
fn field_label(c: &Ctor, i: usize) -> String {
    match c.shape() {
        CtorShape::Record(fs) => format!("field `{}`", fs[i].0),
        CtorShape::Positional(_) => {
            format!("argument {} of `{}`", i + 1, names::bare_name(&c.name))
        }
    }
}

// Whether a type expression mentions the type being derived, so a recursive
// constructor can be told from a base one.
fn ty_mentions(t: &Ty, name: &str) -> bool {
    match t {
        Ty::Con(n, args) | Ty::App(n, args) => {
            n == name || args.iter().any(|a| ty_mentions(a, name))
        }
        _ => {
            let mut found = false;
            t.each_child(&mut |c| found |= ty_mentions(c, name));
            found
        }
    }
}

// One constructor's generator, built from the property-test combinators so all
// recursion is suspended inside `Gen` closures. A recursive `arbitrary` on a
// direct effectful path breaks effect reconciliation, so the derivation never
// self-calls in the method body; instead it composes `Gen` values that the
// runner forces, drawing each field a size smaller (`gen_resize(size - 1, ..)`)
// so the spine shrinks toward a base constructor.
fn ctor_gen(c: &Ctor, lib: &impl Fn(&str) -> String, z: Span) -> S<Expr> {
    let size_m1 = sp(
        Expr::Bin(BinOp::Sub, Box::new(evar("size", z)), Box::new(eint(1, z))),
        z,
    );
    let field = || {
        call(
            evar(&lib(QC_GEN_RESIZE), z),
            vec![size_m1.clone(), call(evar(&lib(QC_ARB_GEN), z), vec![], z)],
            z,
        )
    };
    let mut g = call(evar(&lib(QC_GEN_CONST), z), vec![ctor_apply(c, z)], z);
    for i in (0..c.args.len()).rev() {
        g = call(
            evar(&lib(QC_GEN_BIND), z),
            vec![field(), lam1(&format!("_a{i}"), g, z)],
            z,
        );
    }
    g
}

// A generator that picks uniformly among a set of constructors: one on its own
// generates directly, several go through `gen_choose(g0, [g1, ..])`.
fn choose_gen(ctors: &[&Ctor], lib: &impl Fn(&str) -> String, z: Span) -> S<Expr> {
    if ctors.is_empty() {
        // An uninhabited type has nothing to generate; the generator fails when
        // run rather than the compiler panicking on an empty constructor list.
        return call(evar(FAIL_OP, z), vec![], z);
    }
    if let [only] = ctors {
        return ctor_gen(only, lib, z);
    }
    let mut rest = evar(crate::types::NIL, z);
    for c in ctors[1..].iter().rev() {
        rest = call(
            evar(crate::types::CONS, z),
            vec![ctor_gen(c, lib, z), rest],
            z,
        );
    }
    call(
        evar(&lib(QC_GEN_CHOOSE), z),
        vec![ctor_gen(ctors[0], lib, z), rest],
        z,
    )
}

// A derived generator sized by fuel, expressed over the property-test
// combinators. With no recursive constructor it always chooses among all of
// them; otherwise, once the fuel runs out it restricts to the non-recursive
// constructors (always present for an inhabited type) so generation terminates.
// The method body is one `gen_run`, so the method itself performs the ambient
// `Random` exactly once and never self-recurses effectfully.
fn derive_arbitrary(d: &DataDecl, class: &str, lib: &impl Fn(&str) -> String) -> InstanceDecl {
    let z = Z;
    let all: Vec<&Ctor> = d.ctors.iter().collect();
    let base: Vec<&Ctor> = d
        .ctors
        .iter()
        .filter(|c| !c.args.iter().any(|a| ty_mentions(a, &d.name)))
        .collect();
    let gen = if base.len() == all.len() {
        choose_gen(&all, lib, z)
    } else {
        let base_set = if base.is_empty() { all.clone() } else { base };
        let guard = sp(
            Expr::Bin(BinOp::Le, Box::new(evar("size", z)), Box::new(eint(0, z))),
            z,
        );
        sp(
            Expr::If(
                Box::new(guard),
                Box::new(choose_gen(&base_set, lib, z)),
                Box::new(choose_gen(&all, lib, z)),
            ),
            z,
        )
    };
    let body = call(evar(&lib(QC_GEN_RUN), z), vec![gen, evar("size", z)], z);
    inst_skel(
        d,
        class,
        "arbitrary",
        vec![mdecl(ARBITRARY_METHOD, &["size"], body, z)],
        z,
    )
}

// `deriving (Plate)` emits `children` and `rebuild` over immediate subvalues of
// the derived type. Child order follows constructor and field declaration order.
//
// A least fixpoint over declared field shapes finds nested children through
// lists, options, tuples, and user data types. Each distinct shape shares one
// accumulator-threading helper.
//
// Reject opaque shapes that could contain a child, function types, and
// non-regular recursive occurrences.
//
// `rebuild` consumes replacements in the same shape order. A length mismatch
// performs `Fail`.

// The number of distinct field shapes one derivation may walk into. Only a
// non-regular recursion (a `T(a)` reached through `C(T(List(a)))`) can expand
// without bound; the cap turns that into a diagnostic instead of a hang.
const PLATE_MAX_SHAPES: usize = 512;
// Binders of a derived traversal: the children accumulated so far, and a list
// tail.
const PLATE_ACC: &str = "_acc";
const PLATE_TAIL: &str = "_t";
// Binders of a derived rebuild: the replacements not yet consumed, a component
// put back from them, and the finished value.
const PLATE_REST: &str = "_r";
const PLATE_HOLE: &str = "_g";
const PLATE_OUT: &str = "_y";

// What one component of a walked shape contributes to the children list.
#[derive(Clone, Copy)]
enum Comp {
    // The component is a child of the derived type.
    Node,
    // The component is another walked shape, by index.
    Shape(usize),
}

// How a walked shape is taken apart, which fixes the pattern its helper matches.
enum Form {
    // `List(u)`, walked head first so children come out in element order.
    List,
    // `Option(u)`.
    Opt,
    // A tuple: one component group.
    Tuple,
    // A data type declared in this program, named canonically: one group per
    // constructor, in declaration order.
    Data(String),
}

// One type the traversal walks into. `kids` holds one group per constructor for
// `Form::Data` and exactly one group otherwise; a `None` component contributes
// nothing.
struct Shape {
    ty: Ty,
    form: Form,
    kids: Vec<Vec<Option<Comp>>>,
}

// The shape graph of one derivation: which types the traversal walks into, and
// what each of them holds.
struct Plate<'a> {
    // Canonical name of the type being derived.
    target: &'a str,
    // Its own parameters as arguments: the only self-occurrence shape accepted.
    self_args: Vec<Ty>,
    decls: &'a BTreeMap<&'a str, &'a DataDecl>,
    // Every declared type that can lead back to the target, target included.
    reaching: BTreeSet<String>,
    // Printed type to shape index, so one shape is walked by one helper.
    index: BTreeMap<String, usize>,
    shapes: Vec<Shape>,
}

// The declared types from which the target is reachable: the target itself, and
// any type one of whose fields names a type already known to reach it. Purely
// syntactic and conservative. It guards shapes the traversal cannot inspect by
// asking whether each shape could hold a child.
fn reaching_set(target: &str, decls: &BTreeMap<&str, &DataDecl>) -> BTreeSet<String> {
    let mut set = BTreeSet::from([target.to_string()]);
    let mut grew = true;
    while grew {
        grew = false;
        for (n, d) in decls {
            let holds = d
                .ctors
                .iter()
                .flat_map(|c| &c.args)
                .any(|a| set.iter().any(|m| ty_mentions(a, m)));
            if holds && set.insert((*n).to_string()) {
                grew = true;
            }
        }
    }
    set
}

// The head of a type application, whether written as a saturated constructor or
// as a higher-kinded application.
const fn ty_head(t: &Ty) -> Option<(&str, &[Ty])> {
    match t {
        Ty::Con(n, args) | Ty::App(n, args) => Some((n.as_str(), args.as_slice())),
        _ => None,
    }
}

impl Plate<'_> {
    // An occurrence of the derived type at its own parameters, which is what the
    // instance head promises the children are.
    fn is_self(&self, t: &Ty) -> bool {
        ty_head(t).is_some_and(|(n, args)| n == self.target && args == self.self_args)
    }

    // Classify one field or component type, interning any new shape it walks
    // into. `Err` carries the printed type that could not be traversed, which the
    // caller reports against the field the descent started from.
    fn intern(&mut self, t: &Ty) -> Result<Option<Comp>, String> {
        if self.is_self(t) {
            return Ok(Some(Comp::Node));
        }
        let key = fmt_ty(t);
        if let Some(&i) = self.index.get(&key) {
            return Ok(Some(Comp::Shape(i)));
        }
        // A recursive occurrence at different arguments: its children would not
        // have the type this instance's `children` returns.
        if ty_head(t).is_some_and(|(n, _)| n == self.target) {
            return Err(key);
        }
        // A type the derivation cannot take apart contributes nothing, unless
        // something it is applied to leads back to the derived type, in which
        // case it may be holding a subterm the traversal would silently lose.
        // Asking only whether it names the derived type is not enough: a `Set`
        // the compiler has no declaration for, holding a carrier that holds a
        // node, names neither.
        let opaque = |key: String| {
            if self.reaching.iter().any(|n| ty_mentions(t, n)) {
                Err(key)
            } else {
                Ok(None)
            }
        };
        let (form, groups) = match t {
            Ty::Tuple(ts) => (Form::Tuple, vec![ts.clone()]),
            _ => match ty_head(t) {
                Some((LIST, [u])) => (Form::List, vec![vec![u.clone()]]),
                Some((OPTION, [u])) => (Form::Opt, vec![vec![u.clone()]]),
                Some((n, args)) => {
                    let Some(d) = self
                        .decls
                        .get(n)
                        .copied()
                        .filter(|d| d.params.len() == args.len())
                    else {
                        return opaque(key);
                    };
                    let sub: BTreeMap<String, Ty> =
                        d.params.iter().cloned().zip(args.iter().cloned()).collect();
                    let groups = d
                        .ctors
                        .iter()
                        .map(|c| c.args.iter().map(|a| subst_ty(a, &sub)).collect())
                        .collect();
                    (Form::Data(n.to_string()), groups)
                }
                None => return opaque(key),
            },
        };
        let i = self.shapes.len();
        if i >= PLATE_MAX_SHAPES {
            return Err(key);
        }
        // Reserved before its components are classified, so a shape that contains
        // itself (directly, or through another shape) terminates.
        self.index.insert(key, i);
        self.shapes.push(Shape {
            ty: t.clone(),
            form,
            kids: Vec::new(),
        });
        let mut kids: Vec<Vec<Option<Comp>>> = Vec::with_capacity(groups.len());
        for g in &groups {
            let mut row = Vec::with_capacity(g.len());
            for c in g {
                row.push(self.intern(c)?);
            }
            kids.push(row);
        }
        self.shapes[i].kids = kids;
        Ok(Some(Comp::Shape(i)))
    }

    // Which shapes actually hold a child, as the least fixpoint of "holds a node,
    // or holds a shape that does". A cycle of shapes that never reaches the
    // derived type is correctly excluded, and a shape whose only route to the
    // derived type runs through such a cycle is correctly included; a single
    // memoized descent would get one of those wrong depending on visit order.
    fn reachable(&self) -> Vec<bool> {
        let mut r = vec![false; self.shapes.len()];
        loop {
            let mut changed = false;
            for (i, s) in self.shapes.iter().enumerate() {
                if r[i] {
                    continue;
                }
                let holds = s.kids.iter().flatten().any(|k| match k {
                    Some(Comp::Node) => true,
                    Some(Comp::Shape(j)) => r[*j],
                    None => false,
                });
                if holds {
                    r[i] = true;
                    changed = true;
                }
            }
            if !changed {
                return r;
            }
        }
    }

    // One component's contribution, in front of what the rest of the value
    // contributes. A component that holds nothing leaves the accumulator alone.
    fn contrib(&self, k: Option<Comp>, r: &[bool], val: S<Expr>, tail: S<Expr>) -> S<Expr> {
        match k {
            Some(Comp::Node) => call(evar(CONS, Z), vec![val, tail], Z),
            Some(Comp::Shape(i)) if r[i] => call(
                evar(&names::plate_helper(self.target, i), Z),
                vec![val, tail],
                Z,
            ),
            _ => tail,
        }
    }

    // One group of components bound to `_f0..`, folded right to left so the
    // accumulator is threaded through exactly once and children come out in field
    // order.
    fn group(&self, ks: &[Option<Comp>], r: &[bool], tail: S<Expr>) -> S<Expr> {
        let mut acc = tail;
        for (i, k) in ks.iter().enumerate().rev() {
            acc = self.contrib(*k, r, evar(&format!("{FIELD_BINDER}{i}"), Z), acc);
        }
        acc
    }

    // The arms of a match over a data type's constructors, in declaration order.
    fn data_arms(
        &self,
        ctors: &[Ctor],
        kids: &[Vec<Option<Comp>>],
        r: &[bool],
        tail: &S<Expr>,
    ) -> Vec<Arm> {
        ctors
            .iter()
            .zip(kids)
            .map(|(c, ks)| Arm {
                pat: spat(
                    Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, c.args.len(), Z)),
                    Z,
                ),
                guard: None,
                body: self.group(ks, r, tail.clone()),
                alt: false,
            })
            .collect()
    }

    // One shape's helper: `(shape, children so far) -> children`. Accumulator
    // passing keeps the children in order without an append, and keeps the
    // accumulator expression from being duplicated once per nested shape.
    fn helper(&self, i: usize, r: &[bool], list_ty: &Ty) -> Decl {
        let s = &self.shapes[i];
        let acc = evar(PLATE_ACC, Z);
        let ctor_arm = |name: &str, binders: Vec<S<Pattern>>, body: S<Expr>| Arm {
            pat: spat(Pattern::Ctor(name.into(), binders), Z),
            guard: None,
            body,
            alt: false,
        };
        let head = || evar(&format!("{FIELD_BINDER}0"), Z);
        let arms = match &s.form {
            Form::List => {
                let rest = call(
                    evar(&names::plate_helper(self.target, i), Z),
                    vec![evar(PLATE_TAIL, Z), acc.clone()],
                    Z,
                );
                vec![
                    ctor_arm(NIL, Vec::new(), acc),
                    ctor_arm(
                        CONS,
                        vec![
                            spat(Pattern::Var(format!("{FIELD_BINDER}0")), Z),
                            spat(Pattern::Var(PLATE_TAIL.into()), Z),
                        ],
                        self.contrib(s.kids[0][0], r, head(), rest),
                    ),
                ]
            }
            Form::Opt => vec![
                ctor_arm(NONE, Vec::new(), acc.clone()),
                ctor_arm(
                    SOME,
                    fvars(FIELD_BINDER, 1, Z),
                    self.contrib(s.kids[0][0], r, head(), acc),
                ),
            ],
            Form::Tuple => vec![Arm {
                pat: spat(Pattern::Tuple(fvars(FIELD_BINDER, s.kids[0].len(), Z)), Z),
                guard: None,
                body: self.group(&s.kids[0], r, acc),
                alt: false,
            }],
            Form::Data(n) => {
                let d = self.decls[n.as_str()];
                self.data_arms(&d.ctors, &s.kids, r, &acc)
            }
        };
        let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, Z)), arms), Z);
        let mut f = mdecl(
            &names::plate_helper(self.target, i),
            &[SELF_BINDER, PLATE_ACC],
            body,
            Z,
        );
        f.params[0].ty = Some(s.ty.clone());
        f.params[1].ty = Some(list_ty.clone());
        f.ret = Some(list_ty.clone());
        f
    }

    // One group of components bound to `_f0..`, put back together left to right.
    // A component that can hold a child takes its replacements off the front of
    // the list, binding the component `_g{j}` it becomes and the shorter list the
    // next position reads from; a component that holds none is carried through
    // untouched. The result pairs the shape `make` names with whatever list is
    // left, which is what lets the helpers compose in field order and lets the
    // caller see that the list ran out even and only when it should have.
    fn regroup(
        &self,
        ks: &[Option<Comp>],
        r: &[bool],
        make: impl Fn(&[S<Expr>]) -> S<Expr>,
    ) -> S<Expr> {
        let mut outs: Vec<S<Expr>> = Vec::with_capacity(ks.len());
        // The consuming positions, each with the list index it reads from.
        let mut steps: Vec<(usize, Comp, usize)> = Vec::new();
        for (j, k) in ks.iter().enumerate() {
            let takes = match *k {
                Some(Comp::Node) => Some(Comp::Node),
                Some(Comp::Shape(i)) if r[i] => Some(Comp::Shape(i)),
                _ => None,
            };
            if let Some(c) = takes {
                outs.push(evar(&format!("{PLATE_HOLE}{j}"), Z));
                steps.push((j, c, steps.len()));
            } else {
                outs.push(evar(&format!("{FIELD_BINDER}{j}"), Z));
            }
        }
        let mut body = sp(Expr::Tuple(vec![make(&outs), rest_var(steps.len())]), Z);
        for (j, c, at) in steps.into_iter().rev() {
            let pair = vec![
                spat(Pattern::Var(format!("{PLATE_HOLE}{j}")), Z),
                spat(Pattern::Var(rest_name(at + 1)), Z),
            ];
            body = match c {
                // A child position: the next replacement comes off the front of
                // the list, and a list too short for this value's shape is one
                // ordinary `Fail`, never a half-filled value and never a panic.
                Comp::Node => sp(
                    Expr::Match(
                        Box::new(rest_var(at)),
                        vec![
                            Arm {
                                pat: spat(Pattern::Ctor(CONS.into(), pair), Z),
                                guard: None,
                                body,
                                alt: false,
                            },
                            Arm {
                                pat: spat(Pattern::Wild, Z),
                                guard: None,
                                body: call(evar(FAIL_OP, Z), vec![], Z),
                                alt: false,
                            },
                        ],
                    ),
                    Z,
                ),
                Comp::Shape(i) => {
                    let go = call(
                        evar(&names::plate_rebuilder(self.target, i), Z),
                        vec![evar(&format!("{FIELD_BINDER}{j}"), Z), rest_var(at)],
                        Z,
                    );
                    let arm = Arm {
                        pat: spat(Pattern::Tuple(pair), Z),
                        guard: None,
                        body,
                        alt: false,
                    };
                    sp(Expr::Match(Box::new(go), vec![arm]), Z)
                }
            };
        }
        body
    }

    // The arms of a rebuild over a data type's constructors: the same shapes
    // `data_arms` took apart, in the same declaration order, put back positionally.
    fn rebuild_arms(&self, ctors: &[Ctor], kids: &[Vec<Option<Comp>>], r: &[bool]) -> Vec<Arm> {
        ctors
            .iter()
            .zip(kids)
            .map(|(c, ks)| Arm {
                pat: spat(
                    Pattern::Ctor(c.name.clone(), fvars(FIELD_BINDER, c.args.len(), Z)),
                    Z,
                ),
                guard: None,
                body: self.regroup(ks, r, |outs| apply(&c.name, outs)),
                alt: false,
            })
            .collect()
    }

    // One shape's rebuilder: `(shape, replacements) -> (shape, replacements left
    // over)`. Threading the leftovers is what keeps the two directions in step,
    // since each rebuilder consumes exactly what the matching traversal helper
    // produced, in the same order.
    fn rebuilder(&self, i: usize, r: &[bool], list_ty: &Ty) -> Decl {
        let s = &self.shapes[i];
        let empty = |name: &'static str| Arm {
            pat: spat(Pattern::Ctor(name.into(), Vec::new()), Z),
            guard: None,
            body: self.regroup(&[], r, |_| evar(name, Z)),
            alt: false,
        };
        let arms = match &s.form {
            Form::List => vec![
                empty(NIL),
                Arm {
                    pat: spat(Pattern::Ctor(CONS.into(), fvars(FIELD_BINDER, 2, Z)), Z),
                    guard: None,
                    // The tail is the same shape, so this helper rebuilds the
                    // rest of the list itself, head first as the traversal read it.
                    body: self
                        .regroup(&[s.kids[0][0], Some(Comp::Shape(i))], r, |o| apply(CONS, o)),
                    alt: false,
                },
            ],
            Form::Opt => vec![
                empty(NONE),
                Arm {
                    pat: spat(Pattern::Ctor(SOME.into(), fvars(FIELD_BINDER, 1, Z)), Z),
                    guard: None,
                    body: self.regroup(&s.kids[0], r, |o| apply(SOME, o)),
                    alt: false,
                },
            ],
            Form::Tuple => vec![Arm {
                pat: spat(Pattern::Tuple(fvars(FIELD_BINDER, s.kids[0].len(), Z)), Z),
                guard: None,
                body: self.regroup(&s.kids[0], r, |o| sp(Expr::Tuple(o.to_vec()), Z)),
                alt: false,
            }],
            Form::Data(n) => {
                let d = self.decls[n.as_str()];
                self.rebuild_arms(&d.ctors, &s.kids, r)
            }
        };
        let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, Z)), arms), Z);
        let rest0 = rest_name(0);
        let mut f = mdecl(
            &names::plate_rebuilder(self.target, i),
            &[SELF_BINDER, &rest0],
            body,
            Z,
        );
        f.params[0].ty = Some(s.ty.clone());
        f.params[1].ty = Some(list_ty.clone());
        f.ret = Some(Ty::Tuple(vec![s.ty.clone(), list_ty.clone()]));
        f
    }
}

// The replacements a rebuild has not consumed yet, at one point in a group:
// index 0 is the argument, and each consuming position names the next.
fn rest_name(i: usize) -> String {
    format!("{PLATE_REST}{i}")
}

fn rest_var(i: usize) -> S<Expr> {
    evar(&rest_name(i), Z)
}

// Apply a constructor to already-rebuilt components.
fn apply(name: &str, args: &[S<Expr>]) -> S<Expr> {
    let head = evar(name, Z);
    if args.is_empty() {
        head
    } else {
        call(head, args.to_vec(), Z)
    }
}

// The `Plate` instance for one type, plus the traversal helpers its method calls.
fn derive_plate<'a>(
    d: &'a DataDecl,
    class: &str,
    decls: &'a BTreeMap<&'a str, &'a DataDecl>,
    cspan: Span,
) -> Result<(InstanceDecl, Vec<Decl>), TypeError> {
    let self_args: Vec<Ty> = d.params.iter().cloned().map(Ty::Var).collect();
    let mut plate = Plate {
        target: &d.name,
        self_args,
        decls,
        reaching: reaching_set(&d.name, decls),
        index: BTreeMap::new(),
        shapes: Vec::new(),
    };
    let mut kids: Vec<Vec<Option<Comp>>> = Vec::with_capacity(d.ctors.len());
    for c in &d.ctors {
        let mut row = Vec::with_capacity(c.args.len());
        for (i, a) in c.args.iter().enumerate() {
            row.push(plate.intern(a).map_err(|reached| {
                ErrKind::PlateNotTraversable {
                    ty: names::bare_name(&d.name).to_string(),
                    field: field_label(c, i),
                    reached,
                }
                .at(cspan)
            })?);
        }
        kids.push(row);
    }
    let r = plate.reachable();
    let list_ty = Ty::Con(
        LIST.into(),
        vec![Ty::Con(d.name.clone(), plate.self_args.clone())],
    );
    let arms = plate.data_arms(&d.ctors, &kids, &r, &evar(NIL, Z));
    let body = sp(Expr::Match(Box::new(evar(SELF_BINDER, Z)), arms), Z);
    let children = mdecl(CHILDREN_METHOD, &[SELF_BINDER], body, Z);
    // Putting the value back consumes the replacements the traversal would have
    // produced. Anything left over means the list was not the one `children`
    // returned, which is the caller's error and is reported as one `Fail`: padding
    // or truncating here would put back a value that is not the one asked for.
    let put = sp(
        Expr::Match(
            Box::new(evar(SELF_BINDER, Z)),
            plate.rebuild_arms(&d.ctors, &kids, &r),
        ),
        Z,
    );
    let done = Arm {
        pat: spat(
            Pattern::Tuple(vec![
                spat(Pattern::Var(PLATE_OUT.into()), Z),
                spat(Pattern::Ctor(NIL.into(), Vec::new()), Z),
            ]),
            Z,
        ),
        guard: None,
        body: evar(PLATE_OUT, Z),
        alt: false,
    };
    let over = Arm {
        pat: spat(Pattern::Wild, Z),
        guard: None,
        body: call(evar(FAIL_OP, Z), vec![], Z),
        alt: false,
    };
    let rest0 = rest_name(0);
    let rebuild = mdecl(
        REBUILD_METHOD,
        &[SELF_BINDER, &rest0],
        sp(Expr::Match(Box::new(put), vec![done, over]), Z),
        Z,
    );
    let helpers: Vec<Decl> = (0..plate.shapes.len())
        .filter(|i| r[*i])
        .flat_map(|i| {
            [
                plate.helper(i, &r, &list_ty),
                plate.rebuilder(i, &r, &list_ty),
            ]
        })
        .collect();
    // No per-parameter context: the traversal finds values of the derived type
    // structurally and never touches a type argument.
    Ok((
        inst_with_ctx(d, class, "plate", vec![children, rebuild], Z, None),
        helpers,
    ))
}

#[cfg(test)]
mod tests {
    use super::{constrained_params, Ctor, DataDecl, Row, Ty, Z};
    use crate::syntax::ast::EffLabel;
    use crate::types::{LIST, OPTION};

    fn decl(params: &[&str], args: Vec<Ty>) -> DataDecl {
        DataDecl {
            name: "T".into(),
            params: params.iter().map(|p| (*p).to_string()).collect(),
            param_kinds: Vec::new(),
            ctors: vec![Ctor {
                name: "MkT".into(),
                args,
                fields: None,
            }],
            deriving: Vec::new(),
            newtype: false,
            span: Z,
        }
    }

    fn names(d: &DataDecl) -> Vec<String> {
        constrained_params(d).into_iter().cloned().collect()
    }

    #[test]
    fn phantom_param_is_unconstrained() {
        let d = decl(&["a", "brand"], vec![Ty::Var("a".into())]);
        assert_eq!(names(&d), ["a"]);
    }

    #[test]
    fn occurrence_looks_through_nesting() {
        let nested = Ty::Con(
            OPTION.into(),
            vec![Ty::Con(LIST.into(), vec![Ty::Var("a".into())])],
        );
        let d = decl(&["a"], vec![nested]);
        assert_eq!(names(&d), ["a"]);
    }

    #[test]
    fn higher_kinded_head_and_argument_both_occur() {
        let d = decl(
            &["f", "a"],
            vec![Ty::App("f".into(), vec![Ty::Var("a".into())])],
        );
        assert_eq!(names(&d), ["f", "a"]);
    }

    #[test]
    fn a_recursive_field_constrains_what_it_mentions() {
        let d = decl(
            &["a", "brand"],
            vec![Ty::Con(
                "T".into(),
                vec![Ty::Var("a".into()), Ty::Var("brand".into())],
            )],
        );
        assert_eq!(names(&d), ["a", "brand"]);
    }

    #[test]
    fn a_row_tail_occurs() {
        let field = Ty::Fun(
            vec![Ty::Int],
            Row::Cons(vec![EffLabel::bare("IO")], Some("e".into())),
            Box::new(Ty::Int),
        );
        let d = decl(&["e", "brand"], vec![field]);
        assert_eq!(names(&d), ["e"]);
    }

    #[test]
    fn declaration_order_is_kept() {
        let d = decl(
            &["a", "b", "c"],
            vec![Ty::Var("c".into()), Ty::Var("a".into())],
        );
        assert_eq!(names(&d), ["a", "c"]);
    }
}
