//! Common subexpression elimination for typed Core (late pass, O2).
//!
//! Mirrors [`super::super::opt::cse::cse_counted`] rule-for-rule: only a `Prim`
//! over a non-trapping operator (never `Div`/`Rem`, whose divide-by-zero trap
//! is observable) is shared, keyed on its operator and its two keyable
//! operands (`Float` keys on the bit pattern so the map stays total and
//! `Ord`); constructors, tuples, thunks, effects, refs, and calls are never
//! shared. The typed-specific step is representation transparency: a
//! [`TypedValueKind::Reinterpret`]/[`TypedValueKind::NewtypeRepr`] wrapper
//! erases away transparently ([`TypedValue::erase`]), so the operand key must
//! look through it via [`peel`] to key exactly what the erased legacy
//! operand would, while the rewrite still carries the original (possibly
//! wrapped) value forward unchanged. Each top-level function starts CSE from
//! an empty availability map, so the pass transforms every definition
//! independently and stays SCC-local.
//!
//! Runs after effect lowering (a late pass) so it cannot disturb the
//! var/State fusion.

use std::collections::BTreeMap;

use crate::core::CoreOp;
use crate::sym::Sym;

use super::specialize_support::Rewrite;
use super::{
    TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedHandleOp, TypedHandler,
    TypedPattern, TypedValue, TypedValueKind,
};

/// Rewrite counts for typed common subexpression elimination.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CseStats {
    ticks: u64,
}

impl CseStats {
    /// Repeated subexpressions eliminated.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Eliminate repeated pure scalar subexpressions, preserving every witness.
pub(crate) fn cse<P>(core: TypedCore<P>) -> (TypedCore<P>, CseStats) {
    let mut eliminator = Cse { ticks: 0 };
    let fns = core
        .fns
        .into_iter()
        .map(|function| {
            let body = eliminator.comp(&function.body, &Avail::new());
            TypedCoreFn::new(
                function.name,
                function.params,
                body,
                function.sig,
                function.dict_arity,
            )
        })
        .collect();
    (
        TypedCore::new(fns),
        CseStats {
            ticks: eliminator.ticks,
        },
    )
}

// A value looked through any Reinterpret/NewtypeRepr wrapper, since those
// erase away transparently and must key exactly as their erased form does.
fn peel(value: &TypedValue) -> &TypedValue {
    match &value.kind {
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => peel(inner),
        _ => value,
    }
}

// A key for a value usable as a `Prim` operand. `Float` keys on the bit
// pattern so the map stays total and `Ord`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum VKey {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(u64),
    Bool(bool),
    Unit,
    Str(String),
}

fn vkey(value: &TypedValue) -> Option<VKey> {
    Some(match &peel(value).kind {
        TypedValueKind::Var { name, .. } => VKey::Var(*name),
        TypedValueKind::Int(n) => VKey::Int(*n),
        TypedValueKind::I64(n) => VKey::I64(*n),
        TypedValueKind::U64(n) => VKey::U64(*n),
        TypedValueKind::Float(f) => VKey::Float(f.to_bits()),
        TypedValueKind::Bool(b) => VKey::Bool(*b),
        TypedValueKind::Unit => VKey::Unit,
        TypedValueKind::Str(s) => VKey::Str(s.clone()),
        TypedValueKind::Reinterpret(_)
        | TypedValueKind::LoweredRepr { .. }
        | TypedValueKind::NewtypeRepr { .. }
        | TypedValueKind::Thunk(_)
        | TypedValueKind::Ctor { .. }
        | TypedValueKind::Tuple(_)
        | TypedValueKind::UnboxedTuple(_)
        | TypedValueKind::UnboxedRecord(_) => return None,
    })
}

// The names a key mentions, for invalidation when one is rebound.
fn key_vars(key: &PrimKey) -> Vec<Sym> {
    let mut out = Vec::new();
    if let VKey::Var(name) = key.1.clone() {
        out.push(name);
    }
    if let VKey::Var(name) = key.2.clone() {
        out.push(name);
    }
    out
}

type PrimKey = (CoreOp, VKey, VKey);
type Avail = BTreeMap<PrimKey, Sym>;

// The shareable key of `rhs`, if it is a pure non-trapping `Prim` over
// keyable operands.
fn shareable(rhs: &TypedComp) -> Option<PrimKey> {
    let TypedCompKind::Prim(op, a, b) = &rhs.kind else {
        return None;
    };
    if matches!(op, CoreOp::Div | CoreOp::Rem) {
        return None;
    }
    Some((*op, vkey(a)?, vkey(b)?))
}

// Drop available entries a binder invalidates: those whose key mentions a
// rebound name, and those whose holding binder is itself rebound.
fn narrow(avail: &Avail, names: &[Sym]) -> Avail {
    if names.is_empty() {
        return avail.clone();
    }
    avail
        .iter()
        .filter(|(key, binder)| {
            !names.contains(binder) && key_vars(key).iter().all(|name| !names.contains(name))
        })
        .map(|(key, binder)| (key.clone(), *binder))
        .collect()
}

fn pattern_binder_names(pattern: &TypedPattern) -> Vec<Sym> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.name()],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().map(TypedBinder::name).collect()
        }
    }
}

struct Cse {
    ticks: u64,
}

impl Rewrite for Cse {
    type Ctx = Avail;

    fn comp(&mut self, comp: &TypedComp, avail: &Avail) -> TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(rhs, binder, body) => {
                let rhs2 = self.comp(rhs, avail);
                if let Some(key) = shareable(&rhs2) {
                    if let Some(previous) = avail.get(&key) {
                        // CSE hit: reuse the earlier binder; copy-prop/dead-let
                        // then erase this binding.
                        self.ticks += 1;
                        let rebind = TypedComp::new(
                            rhs2.sig.clone(),
                            TypedCompKind::Return(TypedValue::new(
                                rhs2.sig.result.clone(),
                                TypedValueKind::Var {
                                    name: *previous,
                                    instantiation: Vec::new(),
                                },
                            )),
                        );
                        let body2 = self.comp(body, &narrow(avail, &[binder.name()]));
                        return TypedComp::new(
                            comp.sig.clone(),
                            TypedCompKind::Bind(Box::new(rebind), binder.clone(), Box::new(body2)),
                        );
                    }
                    let mut avail2 = narrow(avail, &[binder.name()]);
                    avail2.insert(key, binder.name());
                    return TypedComp::new(
                        comp.sig.clone(),
                        TypedCompKind::Bind(
                            Box::new(rhs2),
                            binder.clone(),
                            Box::new(self.comp(body, &avail2)),
                        ),
                    );
                }
                let avail2 = narrow(avail, &[binder.name()]);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(
                        Box::new(rhs2),
                        binder.clone(),
                        Box::new(self.comp(body, &avail2)),
                    ),
                )
            }
            TypedCompKind::Lam(params, body) => {
                let names: Vec<Sym> = params.iter().map(TypedBinder::name).collect();
                let avail2 = narrow(avail, &names);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Lam(params.clone(), Box::new(self.comp(body, &avail2))),
                )
            }
            TypedCompKind::Case(scrutinee, arms) => TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Case(
                    scrutinee.clone(),
                    arms.iter()
                        .map(|(pattern, body)| {
                            let avail2 = narrow(avail, &pattern_binder_names(pattern));
                            (pattern.clone(), self.comp(body, &avail2))
                        })
                        .collect(),
                ),
            ),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body2 = Box::new(self.comp(body, avail));
                let return_body2 = return_body.as_ref().map(|rb| {
                    let names: Vec<Sym> = return_binder.iter().map(TypedBinder::name).collect();
                    let avail2 = narrow(avail, &names);
                    Box::new(self.comp(rb, &avail2))
                });
                let ops2 = TypedHandler {
                    arms: ops
                        .arms
                        .iter()
                        .map(|arm| {
                            let mut names: Vec<Sym> =
                                arm.params.iter().map(TypedBinder::name).collect();
                            names.push(arm.resume.name());
                            let avail2 = narrow(avail, &names);
                            TypedHandleOp {
                                name: arm.name,
                                instantiation: arm.instantiation.clone(),
                                params: arm.params.clone(),
                                resume: arm.resume.clone(),
                                body: self.comp(&arm.body, &avail2),
                            }
                        })
                        .collect(),
                    forwarded: ops.forwarded.clone(),
                };
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Handle {
                        body: body2,
                        return_binder: return_binder.clone(),
                        return_body: return_body2,
                        ops: ops2,
                    },
                )
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                let avail2 = narrow(avail, &[token.name()]);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::WithReuse {
                        token: token.clone(),
                        freed: self.value(freed, avail),
                        body: Box::new(self.comp(body, &avail2)),
                    },
                )
            }
            _ => self.descend_comp(comp, avail),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::core::opt::{run_spec_stage, CorePass, PassStage};
    use crate::core::{EffectStrategy, OpGrades};
    use crate::flags::{DynFlags, EffectTier};
    use crate::types::ty::{EffRow, Label};
    use crate::types::Type;

    use super::super::effect_lower::lower_effects;
    use super::super::verify::{verify, OperationSig, VerifyEnv};
    use super::super::{CompSig, CoreFnSig, CoreType, EffectLowered, Elaborated, TypedLowering};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> super::super::CompSig {
        super::super::CompSig::new(result, EffRow::Empty)
    }

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn prim(op: CoreOp, a: TypedValue, b: TypedValue) -> TypedComp {
        TypedComp::new(pure(source(Type::Int)), TypedCompKind::Prim(op, a, b))
    }

    fn assert_differential(
        functions: Vec<TypedCoreFn>,
        env: &VerifyEnv,
    ) -> (TypedCore<Elaborated>, u64) {
        let input = TypedCore::new(functions);
        if let Err(violations) = verify(&input, env) {
            panic!("input fixture is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Cse],
            PassStage::Late,
            &[],
            &DynFlags::default(),
        );
        let expected_ticks = legacy_stats.total();
        let (actual, stats) = cse(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("CSE'd typed Core is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), expected_ticks);
        (actual, expected_ticks)
    }

    fn lowered_cse_fixture() -> (TypedCore<EffectLowered>, VerifyEnv) {
        let operation = sym("ask");
        let effect = sym("Ask");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect),
            ),
        );
        let effects = EffRow::singleton(effect);
        let main_body = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(source(Type::Int), effects),
            ),
            0,
        );
        let input = TypedCore::<Elaborated>::new(vec![main]);
        if let Err(violations) = verify(&input, &env) {
            panic!("elaborated late-pass fixture is invalid: {violations:#?}");
        }
        let flags = DynFlags {
            effect_tier: EffectTier::FreeMonad,
            quiet: true,
            ..DynFlags::default()
        };
        let TypedLowering {
            core: lowered,
            env,
            ctors,
            warning: _,
            strategy,
        } = lower_effects(input, &env, &BTreeMap::new(), &flags, &OpGrades::new())
            .expect("fixture lowers through the production effect ABI");
        assert_eq!(strategy, EffectStrategy::SelectiveFreeMonad);
        assert!(ctors.contains_key("EPure"));
        assert!(ctors.contains_key("EOp"));

        let mul = || {
            prim(
                CoreOp::Mul,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            )
        };
        let cse_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(mul()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(mul()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(prim(
                            CoreOp::Add,
                            var("p", source(Type::Int)),
                            var("q", source(Type::Int)),
                        )),
                    ),
                )),
            ),
        );
        let cse_target = TypedCoreFn::new(
            sym("late_cse_target"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Int)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            cse_body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Int), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let mut functions = lowered.functions().to_vec();
        functions.push(cse_target);
        let core = TypedCore::<EffectLowered>::new(functions);
        if let Err(violations) = verify(&core, &env) {
            panic!("effect-lowered late-pass fixture is invalid: {violations:#?}");
        }
        (core, env)
    }

    fn assert_lowered_differential(
        input: TypedCore<EffectLowered>,
        env: &VerifyEnv,
    ) -> (TypedCore<EffectLowered>, u64) {
        if let Err(violations) = verify(&input, env) {
            panic!("effect-lowered CSE input is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Cse],
            PassStage::Late,
            &[],
            &DynFlags::default(),
        );
        let (actual, stats) = cse(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("effect-lowered CSE output is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), legacy_stats.total());
        (actual, stats.ticks())
    }

    #[test]
    fn effect_lowered_cse_matches_the_legacy_pass() {
        let (input, env) = lowered_cse_fixture();
        let (actual, ticks) = assert_lowered_differential(input, &env);
        assert!(ticks > 0, "the lowered fixture must exercise CSE");
        let target = actual
            .functions()
            .iter()
            .find(|function| function.name() == sym("late_cse_target"))
            .expect("the late-pass target survives");
        let TypedCompKind::Bind(_, _, rest) = target.body().kind() else {
            panic!("expected the first primitive binding")
        };
        let TypedCompKind::Bind(rhs, _, _) = rest.kind() else {
            panic!("expected the repeated primitive binding")
        };
        assert!(matches!(
            rhs.kind(),
            TypedCompKind::Return(TypedValue {
                kind: TypedValueKind::Var { name, .. },
                ..
            }) if *name == sym("p")
        ));
    }

    // `let p = a*b in let q = a*b in p + q`: the second `a*b` is shared, its
    // rhs becoming a copy of `p`.
    #[test]
    fn repeated_pure_prim_is_shared() {
        let env = VerifyEnv::new();
        let mul = || {
            prim(
                CoreOp::Mul,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            )
        };
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(mul()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(mul()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(prim(
                            CoreOp::Add,
                            var("p", source(Type::Int)),
                            var("q", source(Type::Int)),
                        )),
                    ),
                )),
            ),
        );
        let f = TypedCoreFn::new(
            sym("f"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Int)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Int), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let (actual, ticks) = assert_differential(vec![f], &env);
        assert_eq!(ticks, 1);
        let f = actual
            .functions()
            .iter()
            .find(|f| f.name() == sym("f"))
            .unwrap();
        match f.body().kind() {
            TypedCompKind::Bind(_, _, inner) => match &inner.kind {
                TypedCompKind::Bind(qrhs, _, _) => {
                    assert!(matches!(
                        &qrhs.kind,
                        TypedCompKind::Return(TypedValue {
                            kind: TypedValueKind::Var { name, .. },
                            ..
                        }) if *name == sym("p")
                    ));
                }
                other => panic!("expected inner bind, got {other:?}"),
            },
            other => panic!("expected outer bind, got {other:?}"),
        }
    }

    // A divide is never shared (its trap is observable), so nothing fires.
    #[test]
    fn divide_is_not_shared() {
        let env = VerifyEnv::new();
        let div = || {
            prim(
                CoreOp::Div,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            )
        };
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(div()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(div()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(TypedComp::new(
                            pure(source(Type::Int)),
                            TypedCompKind::Return(var("q", source(Type::Int))),
                        )),
                    ),
                )),
            ),
        );
        let f = TypedCoreFn::new(
            sym("f"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Int)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Int), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let (_, ticks) = assert_differential(vec![f], &env);
        assert_eq!(ticks, 0);
    }

    // A repeated Prim wrapped in Reinterpret still keys as the same erased
    // operand, so it shares just as the unwrapped form would.
    #[test]
    fn reinterpret_wrapped_operand_still_shares() {
        let env = VerifyEnv::new();
        let wrapped = |name: &str| {
            TypedValue::new(
                source(Type::Int),
                TypedValueKind::Reinterpret(Box::new(var(name, source(Type::Char)))),
            )
        };
        let mul = || prim(CoreOp::Mul, wrapped("a"), var("b", source(Type::Int)));
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(mul()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(mul()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(prim(
                            CoreOp::Add,
                            var("p", source(Type::Int)),
                            var("q", source(Type::Int)),
                        )),
                    ),
                )),
            ),
        );
        let f = TypedCoreFn::new(
            sym("f"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Char)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Char), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let (_, ticks) = assert_differential(vec![f], &env);
        assert_eq!(ticks, 1);
    }

    // A rebinding of `a` between the two occurrences invalidates the earlier
    // entry, so nothing shares.
    #[test]
    fn shadowing_invalidates_availability() {
        let env = VerifyEnv::new();
        let mul = || {
            prim(
                CoreOp::Mul,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            )
        };
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(mul()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            pure(source(Type::Int)),
                            TypedCompKind::Return(var("p", source(Type::Int))),
                        )),
                        TypedBinder::new(sym("a"), source(Type::Int)),
                        Box::new(TypedComp::new(
                            pure(source(Type::Int)),
                            TypedCompKind::Bind(
                                Box::new(mul()),
                                TypedBinder::new(sym("q"), source(Type::Int)),
                                Box::new(prim(
                                    CoreOp::Add,
                                    var("p", source(Type::Int)),
                                    var("q", source(Type::Int)),
                                )),
                            ),
                        )),
                    ),
                )),
            ),
        );
        let f = TypedCoreFn::new(
            sym("f"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Int)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Int), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let (_, ticks) = assert_differential(vec![f], &env);
        assert_eq!(ticks, 0);
    }

    // A repeated `Prim` inside a handler operation clause shares within that
    // clause's own scope, just as it would at the top level.
    #[test]
    fn shares_inside_handler_operation_clause() {
        let operation_name = sym("get");
        let effect_name = sym("State");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation_name,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect_name),
            ),
        );
        let mul = || {
            prim(
                CoreOp::Mul,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            )
        };
        let op_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(mul()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(mul()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(prim(
                            CoreOp::Add,
                            var("p", source(Type::Int)),
                            var("q", source(Type::Int)),
                        )),
                    ),
                )),
            ),
        );
        let handled_op = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::singleton(effect_name)),
            TypedCompKind::Do {
                operation: operation_name,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let outer = pure(source(Type::Int));
        let resume = TypedBinder::new(
            sym("resume"),
            CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
                CoreFnSig::new(Vec::new(), vec![source(Type::Int)], outer.clone()),
            ))))),
        );
        let clauses = TypedHandler::new(vec![TypedHandleOp::new(
            operation_name,
            Vec::new(),
            Vec::new(),
            resume,
            op_body,
        )])
        .expect("no duplicate operations");
        let body = TypedComp::new(
            outer,
            TypedCompKind::Handle {
                body: Box::new(handled_op),
                return_binder: None,
                return_body: None,
                ops: clauses,
            },
        );
        let f = TypedCoreFn::new(
            sym("f"),
            vec![
                TypedBinder::new(sym("a"), source(Type::Int)),
                TypedBinder::new(sym("b"), source(Type::Int)),
            ],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::Int), source(Type::Int)],
                pure(source(Type::Int)),
            ),
            0,
        );
        let (_, ticks) = assert_differential(vec![f], &env);
        assert_eq!(ticks, 1);
    }
}
