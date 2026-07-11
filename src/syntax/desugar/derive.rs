//! Deriving Eq, Ord, and Show instances.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::{call, eint, evar, lam1, sp, spat};
use crate::core::builtins::Builtin;
use crate::core::contract_digest;
use crate::error::{ErrKind, TypeError};
use crate::fmt::decl::fmt_ty;
use crate::names::{
    self, ARBITRARY_METHOD, DECODE_METHOD, ENCODE_METHOD, EQ_METHOD, FAIL_OP, HASH_METHOD, INT_CMP,
    ORD_METHOD, QC_ARB_GEN, QC_GEN_BIND, QC_GEN_CHOOSE, QC_GEN_CONST, QC_GEN_RESIZE, QC_GEN_RUN,
    SHAPE_DIGEST_METHOD, SHOW_METHOD, WIRE_CAT, WIRE_EMPTY, WIRE_GET_TAG, WIRE_TAG,
};
use crate::syntax::ast::{
    Arm, BigInt, BinOp, Constraint, Ctor, CtorShape, DataDecl, Decl, Expr, Fip, InstanceDecl,
    IntLit, Param, PathOp, PathStep, Pattern, Program, Suffix, Ty, S,
};
use crate::types::{
    ARBITRARY_CLASS, EQ_CLASS, HASH_CLASS, IDENTIFIABLE, IDENTIFIABLE_BUNDLE, LENS, ORD_CLASS,
    SERIALIZE_CLASS, SHOW_CLASS, STABLE_CLASS,
};

// `deriving (Eq, Ord, Show)` synthesizes ordinary named instances here, so the
// class machinery checks and elaborates them like hand-written ones. The
// synthesized nodes carry the empty span: dispatch identity is the node's
// `NodeId` (assigned after desugar), so a method callee no longer needs a
// distinct span to key its dictionary.
const Z: Span = Span::empty(0);

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

pub(super) fn derive_instances(prog: &mut Program) -> Result<(), TypeError> {
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
    let class_canon: BTreeMap<&str, &str> = prog
        .classes
        .iter()
        .map(|c| (names::bare_name(&c.name), c.name.as_str()))
        .collect();
    // Each in-scope top-level function's bare name mapped to its canonical name.
    // A derived instance is built after name resolution, so a reference it emits
    // to a library function (the wire codec's byte builders, the property
    // generators) must already be the canonical `Module.fn`. Prelude functions and
    // the user type's own constructors are canonical bare names, so they need no
    // lookup; only the opt-in library helpers do.
    let value_canon: BTreeMap<&str, &str> = prog
        .fns
        .iter()
        .map(|f| (names::bare_name(&f.name), f.name.as_str()))
        .collect();
    let lib = |n: &str| value_canon.get(n).map_or(n, |c| *c).to_string();
    // The types whose every component is provably serializable-frozen: those that
    // derive (or hand-write) a `Stable` instance. Read once so a `deriving
    // (Stable)` can check its fields structurally at the derive site.
    let stable_types = stable_type_set(prog);
    let mut out = Vec::new();
    let mut fns = Vec::new();
    for d in &prog.types {
        let derives = expand_derives(&d.deriving);
        for (class, cspan) in &derives {
            // Lens is not a class: it synthesizes plain `<f>_of` / `with_<f>`
            // accessors, so it bypasses the class-existence and instance paths.
            if class == LENS {
                fns.extend(derive_lens(d, *cspan)?);
                continue;
            }
            let Some(&canon) = class_canon.get(class.as_str()) else {
                return Err(ErrKind::UnknownDerivingClass {
                    class: class.clone(),
                }
                .at(*cspan));
            };
            out.push(match class.as_str() {
                EQ_CLASS => derive_eq(d, canon),
                ORD_CLASS => derive_ord(d, canon),
                SHOW_CLASS => derive_show(d, canon),
                HASH_CLASS => derive_hash(d, canon),
                SERIALIZE_CLASS => derive_serialize(d, canon, &lib),
                STABLE_CLASS => derive_stable(d, canon, *cspan, &stable_types)?,
                ARBITRARY_CLASS => derive_arbitrary(d, canon, &lib),
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
fn derive_lens(d: &DataDecl, cspan: Span) -> Result<Vec<Decl>, TypeError> {
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
        let get = sp(Expr::FieldAccess(Box::new(evar("_r", z)), f.clone()), z);
        let mut g = mdecl(&format!("{f}_of"), &["_r"], get, z);
        g.params[0].ty = Some(self_ty.clone());
        g.ret = Some(fty.clone());
        out.push(g);
        let set = sp(
            Expr::RecordUpdatePath(
                Box::new(evar("_r", z)),
                vec![(vec![PathStep::Field(f.clone())], PathOp::Set(evar("_v", z)))],
            ),
            z,
        );
        let mut s = mdecl(&format!("with_{f}"), &["_r", "_v"], set, z);
        s.params[0].ty = Some(self_ty.clone());
        s.params[1].ty = Some(fty.clone());
        s.ret = Some(self_ty.clone());
        out.push(s);
    }
    Ok(out)
}

fn fvars(pre: &str, n: usize, z: Span) -> Vec<S<Pattern>> {
    (0..n)
        .map(|i| spat(Pattern::Var(format!("{pre}{i}")), z))
        .collect()
}

// One derived instance. `class` is the canonical class name (`Module.Class` for
// an imported class, a bare name for a prelude one); the per-parameter context
// requires the same class of each type argument, so a derived instance for
// `T(a)` reads `given C(a)`. `prefix` disambiguates the instance's own name.
fn inst_skel(d: &DataDecl, class: &str, prefix: &str, methods: Vec<Decl>, z: Span) -> InstanceDecl {
    InstanceDecl {
        name: format!("{prefix}{}", d.name),
        class: class.into(),
        head: Ty::Con(
            d.name.clone(),
            d.params.iter().map(|p| Ty::Var(p.clone())).collect(),
        ),
        context: d
            .params
            .iter()
            .map(|p| Constraint {
                class: class.into(),
                ty: Ty::Var(p.clone()),
                span: z,
            })
            .collect(),
        methods,
        // The data type's canonical name carries its defining module, so a
        // derived instance is anchored to the same module as its type.
        module: crate::names::module_of(&d.name).to_string(),
        span: z,
    }
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
                default: None,
            })
            .collect(),
        ret: None,
        eff: None,
        constraints: Vec::new(),
        body,
        wheres: Vec::new(),
        konst: false,
        fip: Fip::No,
        replayable: false,
        no_alloc: false,
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
        });
    }
    let scrut = sp(Expr::Tuple(vec![evar("_x", z), evar("_y", z)]), z);
    let body = sp(Expr::Match(Box::new(scrut), arms), z);
    inst_skel(
        d,
        class,
        "eq",
        vec![mdecl(EQ_METHOD, &["_x", "_y"], body, z)],
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
                            },
                            Arm {
                                pat: spat(Pattern::Var("_c".into()), z),
                                guard: None,
                                body: evar("_c", z),
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
            })
            .collect();
        sp(Expr::Match(Box::new(evar(v, z)), tarms), z)
    };
    if d.ctors.len() > 1 {
        arms.push(Arm {
            pat: spat(Pattern::Wild, z),
            guard: None,
            body: call(evar(INT_CMP, z), vec![tag("_x"), tag("_y")], z),
        });
    }
    let scrut = sp(Expr::Tuple(vec![evar("_x", z), evar("_y", z)]), z);
    let body = sp(Expr::Match(Box::new(scrut), arms), z);
    inst_skel(
        d,
        class,
        "ord",
        vec![mdecl(ORD_METHOD, &["_x", "_y"], body, z)],
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
    let shown = |i: usize| call(evar(SHOW_METHOD, Z), vec![evar(&format!("_f{i}"), z)], z);
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
                pat: spat(Pattern::Ctor(c.name.clone(), fvars("_f", n, z)), z),
                guard: None,
                body,
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar("_x", z)), arms), z);
    inst_skel(
        d,
        class,
        "show",
        vec![mdecl(SHOW_METHOD, &["_x"], body, z)],
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
    let hashed = |i: usize| call(evar(HASH_METHOD, z), vec![evar(&format!("_f{i}"), z)], z);
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
                pat: spat(Pattern::Ctor(c.name.clone(), fvars("_f", n, z)), z),
                guard: None,
                body: call(evar(Builtin::Blake3.name(), z), vec![enc], z),
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar("_x", z)), arms), z);
    inst_skel(
        d,
        class,
        "hash",
        vec![mdecl(HASH_METHOD, &["_x"], body, z)],
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
        let enc = call(evar(ENCODE_METHOD, z), vec![evar(&format!("_f{i}"), z)], z);
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
                    Pattern::Ctor(c.name.clone(), fvars("_f", c.args.len(), z)),
                    z,
                ),
                guard: None,
                body,
            }
        })
        .collect();
    let enc_body = sp(Expr::Match(Box::new(evar("_x", z)), enc_arms), z);
    let encode = mdecl(ENCODE_METHOD, &["_x"], enc_body, z);

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
            })
            .collect();
        tag_arms.push(Arm {
            pat: spat(Pattern::Wild, z),
            guard: None,
            body: call(evar(FAIL_OP, z), vec![], z),
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
        };
        let gettag = call(evar(&lib(WIRE_GET_TAG), z), vec![evar("_bs", z)], z);
        sp(Expr::Match(Box::new(gettag), vec![outer]), z)
    } else {
        decode_read(&d.ctors[0], 0, "_bs", z)
    };
    let decode = mdecl(DECODE_METHOD, &["_bs"], dec_body, z);
    inst_skel(d, class, "serialize", vec![encode, decode], z)
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
        // instances in V1, so they are not frozen-serializable either.
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
                let field = match c.shape() {
                    CtorShape::Record(fs) => format!("field `{}`", fs[i].0),
                    CtorShape::Positional(_) => {
                        format!("argument {} of `{}`", i + 1, names::bare_name(&c.name))
                    }
                };
                return Err(ErrKind::StableFieldNotStable {
                    ty: names::bare_name(&d.name).to_string(),
                    field,
                    field_ty: fmt_ty(arg),
                }
                .at(cspan));
            }
        }
    }
    // The method ignores its argument (the digest is a compile-time constant of the
    // type); the argument exists only so dispatch resolves the instance by value.
    let digest = sp(Expr::Str(contract_digest(d)), Z);
    let method = mdecl(SHAPE_DIGEST_METHOD, &["_x"], digest, Z);
    Ok(inst_skel(d, class, "stable", vec![method], Z))
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
