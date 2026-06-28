//! Deriving Eq, Ord, and Show instances.

use std::collections::BTreeSet;

use marginalia::Span;

use super::{call, eint, evar, sp, spat};
use crate::error::TypeError;
use crate::syntax::ast::{
    Arm, BigInt, BinOp, Constraint, DataDecl, Decl, Expr, Fip, InstanceDecl, IntLit, Param, PathOp,
    PathStep, Pattern, Program, Suffix, Ty, S,
};
use crate::types::{EQ_CLASS, ORD_CLASS, SHOW_CLASS};

// `deriving (Eq, Ord, Show)` synthesizes ordinary named instances here, so the
// class machinery checks and elaborates them like hand-written ones. Dictionary
// resolution keys on span, so each constrained method callee needs a distinct
// one. The allocator mints zero-width spans from a high reserved region no real
// source offset can occupy, via a monotonic counter; `zero` is a shared
// placeholder for nodes that need no dict key.
const SYNTH_BASE: usize = usize::MAX / 2;

struct SpanAlloc {
    n: usize,
}

impl SpanAlloc {
    const fn new() -> Self {
        Self { n: 0 }
    }

    const fn zero() -> Span {
        Span::empty(SYNTH_BASE)
    }

    const fn next(&mut self) -> Span {
        self.n += 1;
        Span::empty(SYNTH_BASE + self.n)
    }
}

pub(super) fn derive_instances(prog: &mut Program) -> Result<(), TypeError> {
    let declared: BTreeSet<&str> = prog.classes.iter().map(|c| c.name.as_str()).collect();
    let mut out = Vec::new();
    let mut fns = Vec::new();
    let mut al = SpanAlloc::new();
    for d in &prog.types {
        for (class, cspan) in &d.deriving {
            // Lens is not a class: it synthesizes plain `<f>_of` / `with_<f>`
            // accessors, so it bypasses the class-existence and instance paths.
            if class == "Lens" {
                fns.extend(derive_lens(d, &mut al, *cspan)?);
                continue;
            }
            if !declared.contains(class.as_str()) {
                return Err(TypeError::Other {
                    span: *cspan,
                    msg: format!("unknown class in deriving: {class}"),
                });
            }
            out.push(match class.as_str() {
                EQ_CLASS => derive_eq(d, &mut al),
                ORD_CLASS => derive_ord(d, &mut al),
                SHOW_CLASS => derive_show(d, &mut al),
                other => {
                    return Err(TypeError::Other {
                        span: *cspan,
                        msg: format!(
                            "cannot derive {other} for {}; derivable are Eq, Ord, Show, Lens",
                            d.name
                        ),
                    })
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
// values), not optic types. Each getter's field access gets a fresh span so
// field resolution stays correctly keyed.
fn derive_lens(d: &DataDecl, al: &mut SpanAlloc, cspan: Span) -> Result<Vec<Decl>, TypeError> {
    let z = SpanAlloc::zero();
    let [ctor] = d.ctors.as_slice() else {
        return Err(TypeError::Other {
            span: cspan,
            msg: format!(
                "cannot derive Lens for {}: needs a single record constructor",
                d.name
            ),
        });
    };
    let Some(fields) = &ctor.fields else {
        return Err(TypeError::Other {
            span: cspan,
            msg: format!(
                "cannot derive Lens for {}: `{}` has no named fields",
                d.name, ctor.name
            ),
        });
    };
    let self_ty = Ty::Con(
        d.name.clone(),
        d.params.iter().cloned().map(Ty::Var).collect(),
    );
    let mut out = Vec::new();
    for (f, fty) in fields {
        let gz = al.next();
        let get = sp(Expr::FieldAccess(Box::new(evar("_r", gz)), f.clone()), gz);
        let mut g = mdecl(&format!("{f}_of"), &["_r"], get, z);
        g.params[0].ty = Some(self_ty.clone());
        g.ret = Some(fty.clone());
        out.push(g);
        let sz = al.next();
        let set = sp(
            Expr::RecordUpdatePath(
                Box::new(evar("_r", sz)),
                vec![(
                    vec![PathStep::Field(f.clone())],
                    PathOp::Set(evar("_v", sz)),
                )],
            ),
            sz,
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

fn inst_skel(d: &DataDecl, class: &str, prefix: &str, method: Decl, z: Span) -> InstanceDecl {
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
        methods: vec![method],
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

fn derive_eq(d: &DataDecl, al: &mut SpanAlloc) -> InstanceDecl {
    let z = SpanAlloc::zero();
    let mut arms = pair_match(d, z, |_, n| {
        let mut body = sp(Expr::Bool(true), z);
        for i in (0..n).rev() {
            let f = call(
                evar("eq", al.next()),
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
    inst_skel(d, EQ_CLASS, "eq", mdecl("eq", &["_x", "_y"], body, z), z)
}

// Lexicographic compare: within a constructor, `cmp` the fields left to right
// and stop at the first non-equal result (built inner-first, so the loop runs
// fields in reverse); across distinct constructors, fall back to comparing
// declaration-order tags.
fn derive_ord(d: &DataDecl, al: &mut SpanAlloc) -> InstanceDecl {
    let z = SpanAlloc::zero();
    let mut arms = pair_match(d, z, |_, n| {
        let mut body = eint(0, z);
        for i in (0..n).rev() {
            let f = call(
                evar("cmp", al.next()),
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
            body: call(evar("int_cmp", z), vec![tag("_x"), tag("_y")], z),
        });
    }
    let scrut = sp(Expr::Tuple(vec![evar("_x", z), evar("_y", z)]), z);
    let body = sp(Expr::Match(Box::new(scrut), arms), z);
    inst_skel(d, ORD_CLASS, "ord", mdecl("cmp", &["_x", "_y"], body, z), z)
}

fn derive_show(d: &DataDecl, al: &mut SpanAlloc) -> InstanceDecl {
    let z = SpanAlloc::zero();
    let concat = |a: S<Expr>, b: S<Expr>| call(evar("concat", z), vec![a, b], z);
    let arms = d
        .ctors
        .iter()
        .map(|c| {
            let n = c.args.len();
            let body = if n == 0 {
                sp(Expr::Str(c.name.clone()), z)
            } else {
                let mut acc = sp(Expr::Str(")".into()), z);
                for i in (0..n).rev() {
                    let s = call(
                        evar("show_c", al.next()),
                        vec![evar(&format!("_f{i}"), z)],
                        z,
                    );
                    acc = concat(s, acc);
                    if i > 0 {
                        acc = concat(sp(Expr::Str(", ".into()), z), acc);
                    }
                }
                concat(sp(Expr::Str(format!("{}(", c.name)), z), acc)
            };
            Arm {
                pat: spat(Pattern::Ctor(c.name.clone(), fvars("_f", n, z)), z),
                guard: None,
                body,
            }
        })
        .collect();
    let body = sp(Expr::Match(Box::new(evar("_x", z)), arms), z);
    inst_skel(d, SHOW_CLASS, "show", mdecl("show_c", &["_x"], body, z), z)
}
