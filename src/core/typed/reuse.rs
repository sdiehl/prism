//! In-place constructor reuse for witness-carrying Core.
//!
//! A constructor-pattern arm may release its consumed scrutinee and spend that
//! shell on the first fitting constructor allocation reached on every path.
//! The rewrite mirrors [`super::super::fbip::reuse`] exactly while retaining the
//! freed value type, the rebuilt value type, and a linear token between them.

use crate::names::reuse_token;
use crate::sym::Sym;
use crate::types::Type;

use super::{
    CoreType, Owned, ReuseLowered, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn,
    TypedHandleOp, TypedHandler, TypedPattern, TypedValue, TypedValueKind,
};

/// Pair released constructor shells with fitting allocations without erasing
/// any type witnesses.
#[must_use]
pub(crate) fn reuse(core: TypedCore<Owned>) -> TypedCore<ReuseLowered> {
    TypedCore::new(
        core.fns
            .into_iter()
            .map(|function| {
                TypedCoreFn::new(
                    function.name,
                    function.params,
                    reuse_comp(&function.body),
                    function.sig,
                    function.dict_arity,
                )
            })
            .collect(),
    )
}

fn reuse_comp(comp: &TypedComp) -> TypedComp {
    let kind = match &comp.kind {
        TypedCompKind::Bind(first, binder, rest) => TypedCompKind::Bind(
            Box::new(reuse_comp(first)),
            binder.clone(),
            Box::new(reuse_comp(rest)),
        ),
        TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
            condition.clone(),
            Box::new(reuse_comp(yes)),
            Box::new(reuse_comp(no)),
        ),
        TypedCompKind::Lam(params, body) => {
            TypedCompKind::Lam(params.clone(), Box::new(reuse_comp(body)))
        }
        TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
            scrutinee.clone(),
            arms.iter()
                .map(|(pattern, body)| {
                    let body = reuse_comp(body);
                    (pattern.clone(), reuse_arm(scrutinee, pattern, &body))
                })
                .collect(),
        ),
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => TypedCompKind::Handle {
            body: Box::new(reuse_comp(body)),
            return_binder: return_binder.clone(),
            return_body: return_body.as_deref().map(reuse_comp).map(Box::new),
            ops: TypedHandler {
                arms: ops
                    .arms
                    .iter()
                    .map(|arm| TypedHandleOp {
                        body: reuse_comp(&arm.body),
                        ..arm.clone()
                    })
                    .collect(),
                forwarded: ops.forwarded.clone(),
            },
        },
        _ => return comp.clone(),
    };
    TypedComp::new(comp.sig.clone(), kind)
}

fn reuse_arm(scrutinee: &TypedValue, pattern: &TypedPattern, body: &TypedComp) -> TypedComp {
    let TypedValueKind::Var {
        name: scrutinee_name,
        instantiation: _,
    } = &scrutinee.kind
    else {
        return body.clone();
    };
    // A constructor pattern proves that the selected branch holds a boxed cell,
    // including constructors from the effect-runtime representation. Tuples
    // still need their source tuple witness because unboxed products share the
    // tuple-pattern shape.
    let capacity = match (pattern, &scrutinee.ty) {
        (TypedPattern::Ctor { fields, .. }, _)
        | (TypedPattern::Tuple(fields), CoreType::Source(Type::Tuple(_))) => fields.len(),
        _ => return body.clone(),
    };
    let token = TypedBinder::new(
        Sym::from(reuse_token(scrutinee_name.as_str())),
        CoreType::ReuseToken(Box::new(scrutinee.ty.clone())),
    );
    if pattern_binds(pattern, *scrutinee_name) || pattern_binds(pattern, token.name) {
        return body.clone();
    }
    try_reuse(body, *scrutinee_name, scrutinee, &token, capacity).unwrap_or_else(|| body.clone())
}

// Locate the drop that releases the matched cell. Once found, the remainder of
// that path must spend the resulting token. A branch with no such drop remains
// untouched; ambiguous conditional placement declines the entire rewrite.
fn try_reuse(
    comp: &TypedComp,
    scrutinee_name: Sym,
    freed: &TypedValue,
    token: &TypedBinder,
    capacity: usize,
) -> Option<TypedComp> {
    match &comp.kind {
        TypedCompKind::Bind(first, binder, rest) => {
            if let TypedCompKind::Drop(dropped) = &first.kind {
                if dropped == freed {
                    let body = consume_alloc(rest, token, capacity)?;
                    let sig = body.sig.clone();
                    return Some(TypedComp::new(
                        sig,
                        TypedCompKind::WithReuse {
                            token: token.clone(),
                            freed: freed.clone(),
                            body: Box::new(body),
                        },
                    ));
                }
            }
            if let Some(first) = try_reuse(first, scrutinee_name, freed, token, capacity) {
                return Some(TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(Box::new(first), binder.clone(), rest.clone()),
                ));
            }
            if binder.name == scrutinee_name || binder.name == token.name {
                return None;
            }
            let rest = try_reuse(rest, scrutinee_name, freed, token, capacity)?;
            Some(TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Bind(first.clone(), binder.clone(), Box::new(rest)),
            ))
        }
        TypedCompKind::If(condition, yes, no) => {
            let rewritten_yes = try_reuse(yes, scrutinee_name, freed, token, capacity);
            let rewritten_no = try_reuse(no, scrutinee_name, freed, token, capacity);
            match (rewritten_yes, rewritten_no) {
                (Some(rewritten_yes), None) => Some(TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::If(condition.clone(), Box::new(rewritten_yes), no.clone()),
                )),
                (None, Some(rewritten_no)) => Some(TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::If(condition.clone(), yes.clone(), Box::new(rewritten_no)),
                )),
                (Some(_), Some(_)) | (None, None) => None,
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            let mut hit = false;
            let arms = arms
                .iter()
                .map(|(pattern, body)| {
                    if pattern_binds(pattern, scrutinee_name) || pattern_binds(pattern, token.name)
                    {
                        return (pattern.clone(), body.clone());
                    }
                    try_reuse(body, scrutinee_name, freed, token, capacity).map_or_else(
                        || (pattern.clone(), body.clone()),
                        |body| {
                            hit = true;
                            (pattern.clone(), body)
                        },
                    )
                })
                .collect();
            hit.then(|| {
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Case(scrutinee.clone(), arms),
                )
            })
        }
        TypedCompKind::WithReuse {
            token: inner_token,
            freed: inner_freed,
            body,
        } => {
            if inner_token.name == scrutinee_name || inner_token.name == token.name {
                return None;
            }
            let body = try_reuse(body, scrutinee_name, freed, token, capacity)?;
            Some(TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::WithReuse {
                    token: inner_token.clone(),
                    freed: inner_freed.clone(),
                    body: Box::new(body),
                },
            ))
        }
        _ => None,
    }
}

// Spend one credit at the first fitting allocation on every continuation path.
// A non-allocating tail or a branch that cannot spend on all paths aborts the
// enclosing rewrite, leaving the original body unchanged.
fn consume_alloc(comp: &TypedComp, token: &TypedBinder, capacity: usize) -> Option<TypedComp> {
    match &comp.kind {
        TypedCompKind::Bind(first, binder, rest) => {
            if let Some(first) = consume_alloc(first, token, capacity) {
                return Some(TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(Box::new(first), binder.clone(), rest.clone()),
                ));
            }
            if binder.name == token.name {
                return None;
            }
            let rest = consume_alloc(rest, token, capacity)?;
            Some(TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Bind(first.clone(), binder.clone(), Box::new(rest)),
            ))
        }
        TypedCompKind::Return(value)
            if ctor_arity(value).is_some_and(|arity| arity <= capacity) =>
        {
            Some(TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Reuse(token.clone(), value.clone()),
            ))
        }
        TypedCompKind::If(condition, yes, no) => Some(TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::If(
                condition.clone(),
                Box::new(consume_alloc(yes, token, capacity)?),
                Box::new(consume_alloc(no, token, capacity)?),
            ),
        )),
        TypedCompKind::Case(scrutinee, arms) => Some(TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Case(
                scrutinee.clone(),
                arms.iter()
                    .map(|(pattern, body)| {
                        if pattern_binds(pattern, token.name) {
                            return None;
                        }
                        Some((pattern.clone(), consume_alloc(body, token, capacity)?))
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
        )),
        TypedCompKind::WithReuse {
            token: inner_token,
            freed,
            body,
        } => {
            if inner_token.name == token.name {
                return None;
            }
            Some(TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::WithReuse {
                    token: inner_token.clone(),
                    freed: freed.clone(),
                    body: Box::new(consume_alloc(body, token, capacity)?),
                },
            ))
        }
        _ => None,
    }
}

fn pattern_binds(pattern: &TypedPattern, name: Sym) -> bool {
    match pattern {
        TypedPattern::Wild => false,
        TypedPattern::Var(binder) => binder.name == name,
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().any(|binder| binder.name == name)
        }
    }
}

const fn ctor_arity(value: &TypedValue) -> Option<usize> {
    match &value.kind {
        TypedValueKind::Ctor { fields, .. } | TypedValueKind::Tuple(fields) => Some(fields.len()),
        TypedValueKind::Var { .. }
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_)
        | TypedValueKind::Reinterpret(_)
        | TypedValueKind::LoweredRepr { .. }
        | TypedValueKind::NewtypeRepr { .. }
        | TypedValueKind::Thunk(_)
        | TypedValueKind::UnboxedTuple(_)
        | TypedValueKind::UnboxedRecord(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::core::fbip::{balanced, reuse as legacy_reuse, Sigs};
    use crate::core::{Comp, Core, CoreFn, Value};
    use crate::types::ty::EffRow;

    use super::super::verify::{verify, ConstructorSig, VerifyEnv};
    use super::super::{CompSig, CoreFnSig, TypedValueKind};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
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

    fn int(value: i64) -> TypedValue {
        TypedValue::new(source(Type::Int), TypedValueKind::Int(value))
    }

    fn bool_(value: bool) -> TypedValue {
        TypedValue::new(source(Type::Bool), TypedValueKind::Bool(value))
    }

    fn ctor(name: &str, tag: usize, ty: CoreType, fields: Vec<TypedValue>) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Ctor {
                name: sym(name),
                tag,
                instantiation: Vec::new(),
                fields,
            },
        )
    }

    fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(value.ty.clone()), TypedCompKind::Return(value))
    }

    fn drop_(name: &str, ty: CoreType) -> TypedComp {
        TypedComp::new(pure(source(Type::Unit)), TypedCompKind::Drop(var(name, ty)))
    }

    fn bind(first: TypedComp, binder: TypedBinder, rest: TypedComp) -> TypedComp {
        TypedComp::new(
            rest.sig.clone(),
            TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
        )
    }

    fn after_drop(name: &str, ty: CoreType, rest: TypedComp) -> TypedComp {
        bind(
            drop_(name, ty),
            TypedBinder::new(sym("_"), source(Type::Unit)),
            rest,
        )
    }

    fn function(name: &str, params: Vec<TypedBinder>, body: TypedComp) -> TypedCoreFn {
        let signature = CoreFnSig::new(
            Vec::new(),
            params.iter().map(|binder| binder.ty.clone()).collect(),
            body.sig.clone(),
        );
        TypedCoreFn::new(sym(name), params, body, signature, 0)
    }

    fn pattern(name: &str, capacity: usize) -> TypedPattern {
        TypedPattern::Ctor {
            name: sym(name),
            instantiation: Vec::new(),
            fields: vec![None; capacity],
        }
    }

    fn case(scrutinee: TypedValue, pattern: TypedPattern, body: TypedComp) -> TypedComp {
        TypedComp::new(
            body.sig.clone(),
            TypedCompKind::Case(scrutinee, vec![(pattern, body)]),
        )
    }

    fn add_constructor(
        env: &mut VerifyEnv,
        name: &str,
        tag: usize,
        fields: Vec<CoreType>,
        result: CoreType,
    ) {
        env.insert_constructor(
            sym(name),
            ConstructorSig::new(Vec::new(), tag, fields, result),
        );
    }

    fn shape_env() -> (VerifyEnv, CoreType) {
        let shape = source(Type::Con(sym("Shape"), Vec::new()));
        let mut env = VerifyEnv::new();
        add_constructor(
            &mut env,
            "Wide",
            0,
            vec![source(Type::Int), source(Type::Int)],
            shape.clone(),
        );
        add_constructor(
            &mut env,
            "Narrow",
            1,
            vec![source(Type::Int)],
            shape.clone(),
        );
        add_constructor(
            &mut env,
            "TooWide",
            2,
            vec![source(Type::Int), source(Type::Int), source(Type::Int)],
            shape.clone(),
        );
        (env, shape)
    }

    fn assert_differential(
        input: TypedCore<Owned>,
        env: &VerifyEnv,
        balance: bool,
    ) -> TypedCore<ReuseLowered> {
        if let Err(violations) = verify(&input, env) {
            panic!("owned fixture is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let expected = legacy_reuse(&legacy_input);
        let actual = reuse(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("reuse-lowered fixture is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        if balance {
            if let Err(error) = balanced(&actual.clone().erase(), &Sigs::new()) {
                panic!("reuse-lowered balance oracle rejected the fixture: {error}");
            }
        }
        actual
    }

    fn single_body(core: &Core) -> &Comp {
        &core.fns[0].body
    }

    #[test]
    fn basic_reuse_matches_the_legacy_tree() {
        let (env, shape) = shape_env();
        let scrutinee = TypedBinder::new(sym("cell"), shape.clone());
        let rebuild = ctor("Narrow", 1, shape.clone(), vec![int(7)]);
        let body = case(
            var("cell", shape.clone()),
            pattern("Wide", 2),
            after_drop("cell", shape, ret(rebuild)),
        );
        let input = TypedCore::new(vec![function("main", vec![scrutinee], body)]);
        let actual = assert_differential(input, &env, true).erase();

        let Comp::Case(_, arms) = single_body(&actual) else {
            panic!("expected a case");
        };
        let Comp::WithReuse { token, freed, body } = &arms[0].1 else {
            panic!("fitting allocation did not reuse the released shell");
        };
        assert_eq!(token.as_str(), "reuse#cell");
        assert!(matches!(freed, Value::Var(name) if *name == sym("cell")));
        assert!(matches!(
            &**body,
            Comp::Reuse(name, Value::Ctor(ctor, _, fields))
                if *name == *token && *ctor == sym("Narrow") && fields.len() == 1
        ));
    }

    #[test]
    fn a_missing_drop_leaves_the_arm_unchanged() {
        let (env, shape) = shape_env();
        let scrutinee = TypedBinder::new(sym("cell"), shape.clone());
        let body = case(
            var("cell", shape.clone()),
            pattern("Wide", 2),
            ret(ctor("Narrow", 1, shape, vec![int(7)])),
        );
        let input = TypedCore::new(vec![function("main", vec![scrutinee], body)]);
        let actual = assert_differential(input, &env, false).erase();
        assert!(!format!("{:?}", single_body(&actual)).contains("WithReuse"));
    }

    #[test]
    fn insufficient_capacity_falls_back_without_a_partial_rewrite() {
        let (env, shape) = shape_env();
        let scrutinee = TypedBinder::new(sym("cell"), shape.clone());
        let rebuild = ctor("TooWide", 2, shape.clone(), vec![int(1), int(2), int(3)]);
        let body = case(
            var("cell", shape.clone()),
            pattern("Narrow", 1),
            after_drop("cell", shape, ret(rebuild)),
        );
        let input = TypedCore::new(vec![function("main", vec![scrutinee], body)]);
        let actual = assert_differential(input, &env, true).erase();
        assert!(!format!("{:?}", single_body(&actual)).contains("WithReuse"));
    }

    #[test]
    fn every_branch_spends_the_reuse_credit() {
        let (env, shape) = shape_env();
        let scrutinee = TypedBinder::new(sym("cell"), shape.clone());
        let branches = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::If(
                bool_(true),
                Box::new(ret(ctor("Narrow", 1, shape.clone(), vec![int(1)]))),
                Box::new(ret(ctor("Wide", 0, shape.clone(), vec![int(2), int(3)]))),
            ),
        );
        let body = case(
            var("cell", shape.clone()),
            pattern("Wide", 2),
            after_drop("cell", shape, branches),
        );
        let input = TypedCore::new(vec![function("main", vec![scrutinee], body)]);
        let actual = assert_differential(input, &env, true).erase();
        let Comp::Case(_, arms) = single_body(&actual) else {
            panic!("expected a case");
        };
        let Comp::WithReuse { body, .. } = &arms[0].1 else {
            panic!("expected a reuse scope");
        };
        let Comp::If(_, yes, no) = &**body else {
            panic!("expected the allocation branch inside the reuse scope");
        };
        assert!(matches!(&**yes, Comp::Reuse(..)));
        assert!(matches!(&**no, Comp::Reuse(..)));
    }

    #[test]
    fn one_nonallocating_branch_aborts_the_whole_rewrite() {
        let (env, shape) = shape_env();
        let factory_body = ret(ctor("Narrow", 1, shape.clone(), vec![int(0)]));
        let factory = function("factory", Vec::new(), factory_body);
        let scrutinee = TypedBinder::new(sym("cell"), shape.clone());
        let branches = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::If(
                bool_(true),
                Box::new(ret(ctor("Narrow", 1, shape.clone(), vec![int(1)]))),
                Box::new(TypedComp::new(
                    pure(shape.clone()),
                    TypedCompKind::Call {
                        callee: sym("factory"),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
            ),
        );
        let body = case(
            var("cell", shape.clone()),
            pattern("Wide", 2),
            after_drop("cell", shape, branches),
        );
        let main = function("main", vec![scrutinee], body);
        let input = TypedCore::new(vec![main, factory]);
        let actual = assert_differential(input, &env, true).erase();
        assert!(!format!("{:?}", single_body(&actual)).contains("WithReuse"));
    }

    #[test]
    fn a_shadowed_scrutinee_name_cannot_supply_the_outer_drop() {
        let (env, shape) = shape_env();
        let outer = TypedBinder::new(sym("cell"), shape.clone());
        let shadowing_value = ret(ctor("Narrow", 1, shape.clone(), vec![int(0)]));
        let shadowed_tail = after_drop(
            "cell",
            shape.clone(),
            ret(ctor("Narrow", 1, shape.clone(), vec![int(1)])),
        );
        let arm = bind(
            shadowing_value,
            TypedBinder::new(sym("cell"), shape.clone()),
            shadowed_tail,
        );
        let body = case(var("cell", shape), pattern("Wide", 2), arm);
        let input = TypedCore::new(vec![function("main", vec![outer], body)]);
        verify(&input, &env).expect("shadowing fixture is valid Owned Core");
        let actual = reuse(input);
        verify(&actual, &env).expect("the safe no-reuse result remains valid");
        assert!(!format!("{:?}", single_body(&actual.erase())).contains("WithReuse"));
    }

    #[test]
    fn a_case_field_that_shadows_its_scrutinee_disables_reuse() {
        let (env, shape) = shape_env();
        let outer = TypedBinder::new(sym("cell"), shape.clone());
        let pattern = TypedPattern::Ctor {
            name: sym("Wide"),
            instantiation: Vec::new(),
            fields: vec![Some(TypedBinder::new(sym("cell"), source(Type::Int))), None],
        };
        let arm = after_drop(
            "cell",
            source(Type::Int),
            ret(ctor("Narrow", 1, shape.clone(), vec![int(1)])),
        );
        let body = case(var("cell", shape), pattern, arm);
        let input = TypedCore::new(vec![function("main", vec![outer], body)]);
        verify(&input, &env).expect("pattern-shadow fixture is valid Owned Core");
        let actual = reuse(input);
        verify(&actual, &env).expect("the safe no-reuse result remains valid");
        assert!(!format!("{:?}", single_body(&actual.erase())).contains("WithReuse"));
    }

    #[test]
    fn a_binder_cannot_capture_the_generated_reuse_token() {
        let (env, shape) = shape_env();
        let cell = TypedBinder::new(sym("cell"), shape.clone());
        let other = TypedBinder::new(sym("other"), source(Type::Int));
        let allocation = ret(ctor("Narrow", 1, shape.clone(), vec![int(1)]));
        let release_shadow = after_drop("reuse#cell", source(Type::Unit), allocation);
        let shadowed_tail = bind(
            drop_("other", source(Type::Int)),
            TypedBinder::new(sym("reuse#cell"), source(Type::Unit)),
            release_shadow,
        );
        let arm = after_drop("cell", shape.clone(), shadowed_tail);
        let body = case(var("cell", shape), pattern("Wide", 2), arm);
        let input = TypedCore::new(vec![function("main", vec![cell, other], body)]);
        verify(&input, &env).expect("token-capture fixture is valid Owned Core");
        balanced(&input.clone().erase(), &Sigs::new()).expect("the Owned fixture is balanced");
        let actual = reuse(input);
        verify(&actual, &env).expect("the safe no-reuse result remains valid");
        assert!(!format!("{:?}", single_body(&actual.erase())).contains("WithReuse"));
    }

    #[test]
    fn nested_reuse_scopes_preserve_both_credits() {
        let (env, shape) = shape_env();
        let outer = TypedBinder::new(sym("outer"), shape.clone());
        let inner = TypedBinder::new(sym("inner"), shape.clone());
        let first_alloc = ret(ctor("Narrow", 1, shape.clone(), vec![int(1)]));
        let second_alloc = ret(ctor("Wide", 0, shape.clone(), vec![int(2), int(3)]));
        let allocations = bind(
            first_alloc,
            TypedBinder::new(sym("_"), shape.clone()),
            second_alloc,
        );
        let inner_body = after_drop(
            "outer",
            shape.clone(),
            after_drop("inner", shape.clone(), allocations),
        );
        let inner_case = case(var("inner", shape.clone()), pattern("Wide", 2), inner_body);
        let outer_case = case(var("outer", shape), pattern("Wide", 2), inner_case);
        let input = TypedCore::new(vec![function("main", vec![outer, inner], outer_case)]);
        let actual = assert_differential(input, &env, true).erase();
        let rendered = format!("{:?}", single_body(&actual));
        assert_eq!(rendered.matches("WithReuse").count(), 2);
        assert!(rendered.contains("reuse#outer"));
        assert!(rendered.contains("reuse#inner"));
    }

    #[test]
    fn equal_capacity_cross_type_reuse_is_valid() {
        let old_ty = source(Type::Con(sym("OldShape"), Vec::new()));
        let new_ty = source(Type::Con(sym("NewShape"), Vec::new()));
        let mut env = VerifyEnv::new();
        add_constructor(
            &mut env,
            "OldShell",
            0,
            vec![source(Type::Int), source(Type::Int)],
            old_ty.clone(),
        );
        add_constructor(
            &mut env,
            "NewShell",
            0,
            vec![source(Type::Int), source(Type::Int)],
            new_ty.clone(),
        );
        let old = TypedBinder::new(sym("old"), old_ty.clone());
        let rebuild = ctor("NewShell", 0, new_ty, vec![int(4), int(5)]);
        let body = case(
            var("old", old_ty.clone()),
            pattern("OldShell", 2),
            after_drop("old", old_ty, ret(rebuild)),
        );
        let input = TypedCore::new(vec![function("main", vec![old], body)]);
        let actual = assert_differential(input, &env, true).erase();
        assert!(format!("{:?}", single_body(&actual)).contains("WithReuse"));
    }

    #[test]
    fn verifier_rejects_a_credit_missing_on_one_branch() {
        let (env, shape) = shape_env();
        let freed = TypedBinder::new(sym("cell"), shape.clone());
        let token = TypedBinder::new(
            sym("reuse#cell"),
            CoreType::ReuseToken(Box::new(shape.clone())),
        );
        let rebuild = || ctor("Narrow", 1, shape.clone(), vec![int(1)]);
        let spend = || {
            TypedComp::new(
                pure(shape.clone()),
                TypedCompKind::Reuse(token.clone(), rebuild()),
            )
        };
        let branches = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::If(bool_(true), Box::new(spend()), Box::new(ret(rebuild()))),
        );
        let body = TypedComp::new(
            branches.sig.clone(),
            TypedCompKind::WithReuse {
                token,
                freed: var("cell", shape.clone()),
                body: Box::new(branches),
            },
        );
        let body = case(var("cell", shape), pattern("Wide", 2), body);
        let forged = TypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(&forged, &env).expect_err("one branch leaves the credit live");
        assert!(violations.iter().any(|violation| violation
            .message()
            .contains("branches consume different reuse-token credits")));
    }

    #[test]
    fn verifier_rejects_a_rebuild_larger_than_the_matched_shell() {
        let (env, shape) = shape_env();
        let freed = TypedBinder::new(sym("cell"), shape.clone());
        let token = TypedBinder::new(
            sym("reuse#cell"),
            CoreType::ReuseToken(Box::new(shape.clone())),
        );
        let rebuild = ctor("TooWide", 2, shape.clone(), vec![int(1), int(2), int(3)]);
        let spend = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::Reuse(token.clone(), rebuild),
        );
        let body = TypedComp::new(
            spend.sig.clone(),
            TypedCompKind::WithReuse {
                token,
                freed: var("cell", shape.clone()),
                body: Box::new(spend),
            },
        );
        let body = case(var("cell", shape), pattern("Narrow", 1), body);
        let forged = TypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(&forged, &env).expect_err("the rebuild exceeds the shell");
        assert!(violations
            .iter()
            .any(|violation| violation.message().contains("exceeds shell capacity")));
    }

    #[test]
    fn verifier_rejects_a_reuse_scope_outside_its_matching_case() {
        let (env, shape) = shape_env();
        let freed = TypedBinder::new(sym("cell"), shape.clone());
        let token = TypedBinder::new(
            sym("reuse#cell"),
            CoreType::ReuseToken(Box::new(shape.clone())),
        );
        let spend = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::Reuse(
                token.clone(),
                ctor("Narrow", 1, shape.clone(), vec![int(1)]),
            ),
        );
        let body = TypedComp::new(
            spend.sig.clone(),
            TypedCompKind::WithReuse {
                token,
                freed: var("cell", shape),
                body: Box::new(spend),
            },
        );
        let forged = TypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(&forged, &env).expect_err("reuse needs case-shell authority");
        assert!(violations.iter().any(|violation| violation
            .message()
            .contains("does not free the active boxed case scrutinee")));
    }

    #[test]
    fn verifier_rejects_freeing_one_matched_shell_twice() {
        let (env, shape) = shape_env();
        let freed = TypedBinder::new(sym("cell"), shape.clone());
        let outer_token = TypedBinder::new(
            sym("outer_token"),
            CoreType::ReuseToken(Box::new(shape.clone())),
        );
        let inner_token = TypedBinder::new(
            sym("inner_token"),
            CoreType::ReuseToken(Box::new(shape.clone())),
        );
        let rebuild = || ctor("Narrow", 1, shape.clone(), vec![int(1)]);
        let inner_spend = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::Reuse(inner_token.clone(), rebuild()),
        );
        let inner_scope = TypedComp::new(
            inner_spend.sig.clone(),
            TypedCompKind::WithReuse {
                token: inner_token,
                freed: var("cell", shape.clone()),
                body: Box::new(inner_spend),
            },
        );
        let outer_spend = TypedComp::new(
            pure(shape.clone()),
            TypedCompKind::Reuse(outer_token.clone(), rebuild()),
        );
        let sequential = bind(
            inner_scope,
            TypedBinder::new(sym("_"), shape.clone()),
            outer_spend,
        );
        let body = TypedComp::new(
            sequential.sig.clone(),
            TypedCompKind::WithReuse {
                token: outer_token,
                freed: var("cell", shape.clone()),
                body: Box::new(sequential),
            },
        );
        let body = case(var("cell", shape), pattern("Wide", 2), body);
        let forged = TypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(&forged, &env).expect_err("one shell cannot be freed twice");
        assert!(violations
            .iter()
            .any(|violation| violation.message().contains("freed more than once")));
    }

    #[test]
    fn legacy_oracle_really_uses_capacity_instead_of_type_equality() {
        let old = sym("old");
        let old_ctor = sym("OldShell");
        let new_ctor = sym("NewShell");
        let raw = Core {
            fns: vec![CoreFn {
                name: sym("main"),
                params: vec![old],
                dict_arity: 0,
                body: Comp::Case(
                    Value::Var(old),
                    vec![(
                        crate::core::CorePat::Ctor(old_ctor, vec![None, None]),
                        Comp::Bind(
                            Box::new(Comp::Drop(Value::Var(old))),
                            sym("_"),
                            Box::new(Comp::Return(Value::Ctor(
                                new_ctor,
                                0,
                                vec![Value::Int(1), Value::Int(2)],
                            ))),
                        ),
                    )],
                ),
            }],
        };
        let lowered = legacy_reuse(&raw);
        assert!(matches!(
            &lowered.fns[0].body,
            Comp::Case(_, arms) if matches!(&arms[0].1, Comp::WithReuse { .. })
        ));
    }
}
