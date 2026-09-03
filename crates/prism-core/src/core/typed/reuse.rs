//! In-place constructor reuse for witness-carrying Core.
//!
//! A constructor-pattern arm may release its consumed scrutinee and spend that
//! shell on the first fitting constructor allocation reached on every path.
//! The rewrite mirrors [`super::super::fbip::reuse`] exactly while retaining the
//! freed value type, the rebuilt value type, and a linear token between them.

use crate::types::Type;
use prism_common::sym::Sym;
use prism_syntax::kw;
use prism_syntax::names::reuse_token;

use super::verify::clone_core_type;
use super::{
    CompSig, CoreInstantiation, CoreType, Owned, ReuseLowered, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedForward, TypedHandleOp, TypedHandler, TypedPattern,
    TypedValue, TypedValueKind, UncheckedTypedCore,
};

/// Pair released constructor shells with fitting allocations without erasing
/// any type witnesses.
#[must_use]
pub fn reuse(core: TypedCore<Owned>) -> UncheckedTypedCore<ReuseLowered> {
    UncheckedTypedCore::new(
        core.into_unchecked()
            .into_functions()
            .into_iter()
            .map(|function| {
                TypedCoreFn::new(
                    function.name,
                    function.params,
                    reuse_comp(function.body),
                    function.sig,
                    function.dict_arity,
                )
            })
            .collect(),
    )
}

fn reuse_comp(comp: TypedComp) -> TypedComp {
    let mut work = vec![ReuseFrame::Comp(comp)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            ReuseFrame::Comp(comp) => {
                let TypedComp { sig, kind } = comp;
                match kind {
                    TypedCompKind::Bind(first, binder, rest) => {
                        work.push(ReuseFrame::FinishBind { sig, binder });
                        work.push(ReuseFrame::Comp(*rest));
                        work.push(ReuseFrame::Comp(*first));
                    }
                    TypedCompKind::If(condition, yes, no) => {
                        work.push(ReuseFrame::FinishIf { sig, condition });
                        work.push(ReuseFrame::Comp(*no));
                        work.push(ReuseFrame::Comp(*yes));
                    }
                    TypedCompKind::Lam(params, body) => {
                        work.push(ReuseFrame::FinishLam { sig, params });
                        work.push(ReuseFrame::Comp(*body));
                    }
                    TypedCompKind::Case(scrutinee, arms) => {
                        let mut patterns = Vec::with_capacity(arms.len());
                        let mut bodies = Vec::with_capacity(arms.len());
                        for (pattern, body) in arms {
                            patterns.push(pattern);
                            bodies.push(body);
                        }
                        work.push(ReuseFrame::FinishCase {
                            sig,
                            scrutinee,
                            patterns,
                        });
                        work.extend(bodies.into_iter().rev().map(ReuseFrame::Comp));
                    }
                    TypedCompKind::Handle {
                        body,
                        return_binder,
                        return_body,
                        ops,
                    } => {
                        let TypedHandler { arms, forwarded } = ops;
                        let mut metadata = Vec::with_capacity(arms.len());
                        let mut bodies = Vec::with_capacity(arms.len());
                        for arm in arms {
                            metadata.push(HandleMetadata {
                                name: arm.name,
                                instantiation: arm.instantiation,
                                params: arm.params,
                                resume: arm.resume,
                            });
                            bodies.push(arm.body);
                        }
                        let has_return = return_body.is_some();
                        work.push(ReuseFrame::FinishHandle {
                            sig,
                            return_binder,
                            has_return,
                            metadata,
                            forwarded,
                        });
                        work.extend(bodies.into_iter().rev().map(ReuseFrame::Comp));
                        if let Some(return_body) = return_body {
                            work.push(ReuseFrame::Comp(*return_body));
                        }
                        work.push(ReuseFrame::Comp(*body));
                    }
                    other => results.push(TypedComp::new(sig, other)),
                }
            }
            ReuseFrame::FinishBind { sig, binder } => {
                let rest = pop_comp(&mut results);
                let first = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
                ));
            }
            ReuseFrame::FinishIf { sig, condition } => {
                let no = pop_comp(&mut results);
                let yes = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::If(condition, Box::new(yes), Box::new(no)),
                ));
            }
            ReuseFrame::FinishLam { sig, params } => {
                let body = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::Lam(params, Box::new(body)),
                ));
            }
            ReuseFrame::FinishCase {
                sig,
                scrutinee,
                patterns,
            } => {
                let start = results
                    .len()
                    .checked_sub(patterns.len())
                    .expect("each case arm has a rewritten body");
                let bodies = results.drain(start..);
                let arms = patterns
                    .into_iter()
                    .zip(bodies)
                    .map(|(pattern, body)| {
                        let body = reuse_arm(&scrutinee, &pattern, body);
                        (pattern, body)
                    })
                    .collect();
                results.push(TypedComp::new(sig, TypedCompKind::Case(scrutinee, arms)));
            }
            ReuseFrame::FinishHandle {
                sig,
                return_binder,
                has_return,
                metadata,
                forwarded,
            } => {
                let body_count = 1 + usize::from(has_return) + metadata.len();
                let start = results
                    .len()
                    .checked_sub(body_count)
                    .expect("each handler clause has a rewritten body");
                let (body, return_body, arms) = {
                    let mut bodies = results.drain(start..);
                    let body = Box::new(bodies.next().expect("a handled body exists"));
                    let return_body = has_return
                        .then(|| Box::new(bodies.next().expect("a return-clause body exists")));
                    let arms = metadata
                        .into_iter()
                        .map(|arm| TypedHandleOp {
                            name: arm.name,
                            instantiation: arm.instantiation,
                            params: arm.params,
                            resume: arm.resume,
                            body: bodies.next().expect("an operation-clause body exists"),
                        })
                        .collect();
                    let extra_body = bodies.next();
                    debug_assert!(extra_body.is_none());
                    (body, return_body, arms)
                };
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::Handle {
                        body,
                        return_binder,
                        return_body,
                        ops: TypedHandler { arms, forwarded },
                    },
                ));
            }
        }
    }
    let result = pop_comp(&mut results);
    debug_assert!(results.is_empty());
    result
}

enum ReuseFrame {
    Comp(TypedComp),
    FinishBind {
        sig: CompSig,
        binder: TypedBinder,
    },
    FinishIf {
        sig: CompSig,
        condition: TypedValue,
    },
    FinishLam {
        sig: CompSig,
        params: Vec<TypedBinder>,
    },
    FinishCase {
        sig: CompSig,
        scrutinee: TypedValue,
        patterns: Vec<TypedPattern>,
    },
    FinishHandle {
        sig: CompSig,
        return_binder: Option<TypedBinder>,
        has_return: bool,
        metadata: Vec<HandleMetadata>,
        forwarded: Vec<TypedForward>,
    },
}

struct HandleMetadata {
    name: Sym,
    instantiation: Vec<CoreInstantiation>,
    params: Vec<TypedBinder>,
    resume: TypedBinder,
}

fn pop_comp(results: &mut Vec<TypedComp>) -> TypedComp {
    results.pop().expect("a rewritten computation exists")
}

fn reuse_arm(scrutinee: &TypedValue, pattern: &TypedPattern, body: TypedComp) -> TypedComp {
    let TypedValueKind::Var {
        name: scrutinee_name,
        instantiation: _,
    } = &scrutinee.kind
    else {
        return body;
    };
    let Some(capacity) = reuse_cell_capacity(pattern, &scrutinee.ty) else {
        return body;
    };
    let token = TypedBinder::new(
        Sym::from(reuse_token(scrutinee_name.as_str())),
        CoreType::ReuseToken(Box::new(clone_core_type(scrutinee.ty()))),
    );
    if pattern_binds(pattern, *scrutinee_name) || pattern_binds(pattern, token.name) {
        return body;
    }
    try_reuse(body, *scrutinee_name, &token, capacity)
}

// Locate the drop that releases the matched cell. Once found, the remainder of
// that path must spend the resulting token. A branch with no such drop remains
// untouched; ambiguous conditional placement declines the entire rewrite.
fn try_reuse(
    comp: TypedComp,
    scrutinee_name: Sym,
    token: &TypedBinder,
    capacity: usize,
) -> TypedComp {
    let mut plans = Vec::new();
    let Some(root) = plan_try_reuse(&comp, scrutinee_name, token.name, capacity, &mut plans) else {
        return comp;
    };
    apply_plan(comp, root, &plans, token)
}

fn plan_try_reuse(
    comp: &TypedComp,
    scrutinee_name: Sym,
    token_name: Sym,
    capacity: usize,
    plans: &mut Vec<Plan>,
) -> Option<PlanId> {
    let mut work = vec![TryFrame::Comp(comp)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            TryFrame::Comp(comp) => match comp.kind() {
                TypedCompKind::Bind(first, binder, rest) => {
                    if matches!(
                        first.kind(),
                        TypedCompKind::Drop(TypedValue {
                            kind: TypedValueKind::Var { name, .. },
                            ..
                        }) if *name == scrutinee_name
                    ) {
                        let plan = plan_consume_alloc(rest, token_name, capacity, plans)
                            .map(|consume| push_plan(plans, Plan::TryDrop { consume }));
                        results.push(plan);
                    } else {
                        work.push(TryFrame::BindFirst {
                            rest,
                            shadowed: binder.name == scrutinee_name || binder.name == token_name,
                        });
                        work.push(TryFrame::Comp(first));
                    }
                }
                TypedCompKind::If(_, yes, no) => {
                    work.push(TryFrame::FinishIf);
                    work.push(TryFrame::Comp(no));
                    work.push(TryFrame::Comp(yes));
                }
                TypedCompKind::Case(_, arms) => {
                    work.push(TryFrame::FinishCase {
                        arm_count: arms.len(),
                    });
                    work.extend(arms.iter().rev().map(|(pattern, body)| {
                        if pattern_binds(pattern, scrutinee_name)
                            || pattern_binds(pattern, token_name)
                        {
                            TryFrame::Blocked
                        } else {
                            TryFrame::Comp(body)
                        }
                    }));
                }
                TypedCompKind::WithReuse {
                    token: inner_token,
                    body,
                    ..
                } if inner_token.name != scrutinee_name && inner_token.name != token_name => {
                    work.push(TryFrame::FinishWithReuse);
                    work.push(TryFrame::Comp(body));
                }
                _ => results.push(None),
            },
            TryFrame::Blocked => results.push(None),
            TryFrame::BindFirst { rest, shadowed } => {
                if let Some(child) = pop_plan(&mut results) {
                    results.push(Some(push_plan(plans, Plan::TryBindFirst { child })));
                } else if shadowed {
                    results.push(None);
                } else {
                    work.push(TryFrame::BindRest);
                    work.push(TryFrame::Comp(rest));
                }
            }
            TryFrame::BindRest => {
                let plan = pop_plan(&mut results)
                    .map(|child| push_plan(plans, Plan::TryBindRest { child }));
                results.push(plan);
            }
            TryFrame::FinishIf => {
                let no = pop_plan(&mut results);
                let yes = pop_plan(&mut results);
                let plan = match (yes, no) {
                    (Some(child), None) => Some(push_plan(plans, Plan::TryIfYes { child })),
                    (None, Some(child)) => Some(push_plan(plans, Plan::TryIfNo { child })),
                    _ => None,
                };
                results.push(plan);
            }
            TryFrame::FinishCase { arm_count } => {
                let start = results
                    .len()
                    .checked_sub(arm_count)
                    .expect("each case arm has a reuse plan");
                let arms: Vec<_> = results.drain(start..).collect();
                let hit = arms.iter().any(Option::is_some);
                results.push(hit.then(|| push_plan(plans, Plan::TryCase { arms })));
            }
            TryFrame::FinishWithReuse => {
                let plan = pop_plan(&mut results)
                    .map(|child| push_plan(plans, Plan::TryWithReuse { child }));
                results.push(plan);
            }
        }
    }
    let result = pop_plan(&mut results);
    debug_assert!(results.is_empty());
    result
}

enum TryFrame<'a> {
    Comp(&'a TypedComp),
    Blocked,
    BindFirst { rest: &'a TypedComp, shadowed: bool },
    BindRest,
    FinishIf,
    FinishCase { arm_count: usize },
    FinishWithReuse,
}

// Spend one credit at the first fitting allocation on every path.
fn plan_consume_alloc(
    comp: &TypedComp,
    token_name: Sym,
    capacity: usize,
    plans: &mut Vec<Plan>,
) -> Option<PlanId> {
    let mut work = vec![ConsumeFrame::Comp(comp)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            ConsumeFrame::Comp(comp) => match comp.kind() {
                TypedCompKind::Bind(first, binder, rest) => {
                    work.push(ConsumeFrame::BindFirst {
                        rest,
                        shadowed: binder.name == token_name,
                    });
                    work.push(ConsumeFrame::Comp(first));
                }
                TypedCompKind::Return(value)
                    if rebuild_arity(value).is_some_and(|arity| arity <= capacity) =>
                {
                    results.push(Some(push_plan(plans, Plan::ConsumeReturn)));
                }
                TypedCompKind::If(_, yes, no) => {
                    work.push(ConsumeFrame::IfYes { no });
                    work.push(ConsumeFrame::Comp(yes));
                }
                TypedCompKind::Case(_, arms) if arms.is_empty() => {
                    results.push(Some(push_plan(
                        plans,
                        Plan::ConsumeCase { arms: Vec::new() },
                    )));
                }
                TypedCompKind::Case(_, arms) => {
                    if pattern_binds(&arms[0].0, token_name) {
                        results.push(None);
                    } else {
                        work.push(ConsumeFrame::CaseArm {
                            arms,
                            index: 0,
                            rebuilt: Vec::with_capacity(arms.len()),
                        });
                        work.push(ConsumeFrame::Comp(&arms[0].1));
                    }
                }
                TypedCompKind::WithReuse {
                    token: inner_token,
                    body,
                    ..
                } if inner_token.name != token_name => {
                    work.push(ConsumeFrame::FinishWithReuse);
                    work.push(ConsumeFrame::Comp(body));
                }
                _ => results.push(None),
            },
            ConsumeFrame::BindFirst { rest, shadowed } => {
                if let Some(child) = pop_plan(&mut results) {
                    results.push(Some(push_plan(plans, Plan::ConsumeBindFirst { child })));
                } else if shadowed {
                    results.push(None);
                } else {
                    work.push(ConsumeFrame::BindRest);
                    work.push(ConsumeFrame::Comp(rest));
                }
            }
            ConsumeFrame::BindRest => {
                let plan = pop_plan(&mut results)
                    .map(|child| push_plan(plans, Plan::ConsumeBindRest { child }));
                results.push(plan);
            }
            ConsumeFrame::IfYes { no } => {
                if let Some(yes) = pop_plan(&mut results) {
                    work.push(ConsumeFrame::IfNo { yes });
                    work.push(ConsumeFrame::Comp(no));
                } else {
                    results.push(None);
                }
            }
            ConsumeFrame::IfNo { yes } => {
                let plan =
                    pop_plan(&mut results).map(|no| push_plan(plans, Plan::ConsumeIf { yes, no }));
                results.push(plan);
            }
            ConsumeFrame::CaseArm {
                arms,
                index,
                mut rebuilt,
            } => {
                if let Some(body) = pop_plan(&mut results) {
                    rebuilt.push(body);
                    let next = index + 1;
                    if next == arms.len() {
                        results.push(Some(push_plan(plans, Plan::ConsumeCase { arms: rebuilt })));
                    } else if pattern_binds(&arms[next].0, token_name) {
                        results.push(None);
                    } else {
                        work.push(ConsumeFrame::CaseArm {
                            arms,
                            index: next,
                            rebuilt,
                        });
                        work.push(ConsumeFrame::Comp(&arms[next].1));
                    }
                } else {
                    results.push(None);
                }
            }
            ConsumeFrame::FinishWithReuse => {
                let plan = pop_plan(&mut results)
                    .map(|child| push_plan(plans, Plan::ConsumeWithReuse { child }));
                results.push(plan);
            }
        }
    }
    let result = pop_plan(&mut results);
    debug_assert!(results.is_empty());
    result
}

enum ConsumeFrame<'a> {
    Comp(&'a TypedComp),
    BindFirst {
        rest: &'a TypedComp,
        shadowed: bool,
    },
    BindRest,
    IfYes {
        no: &'a TypedComp,
    },
    IfNo {
        yes: PlanId,
    },
    CaseArm {
        arms: &'a [(TypedPattern, TypedComp)],
        index: usize,
        rebuilt: Vec<PlanId>,
    },
    FinishWithReuse,
}

type PlanId = usize;

enum Plan {
    TryDrop { consume: PlanId },
    TryBindFirst { child: PlanId },
    TryBindRest { child: PlanId },
    TryIfYes { child: PlanId },
    TryIfNo { child: PlanId },
    TryCase { arms: Vec<Option<PlanId>> },
    TryWithReuse { child: PlanId },
    ConsumeReturn,
    ConsumeBindFirst { child: PlanId },
    ConsumeBindRest { child: PlanId },
    ConsumeIf { yes: PlanId, no: PlanId },
    ConsumeCase { arms: Vec<PlanId> },
    ConsumeWithReuse { child: PlanId },
}

fn push_plan(plans: &mut Vec<Plan>, plan: Plan) -> PlanId {
    let id = plans.len();
    plans.push(plan);
    id
}

fn pop_plan(results: &mut Vec<Option<PlanId>>) -> Option<PlanId> {
    results.pop().expect("a child reuse plan exists")
}

fn apply_plan(comp: TypedComp, root: PlanId, plans: &[Plan], token: &TypedBinder) -> TypedComp {
    let mut work = vec![ApplyFrame::Comp(comp, root)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            ApplyFrame::Comp(comp, id) => {
                let TypedComp { sig, kind } = comp;
                match &plans[id] {
                    Plan::TryDrop { consume } => {
                        let TypedCompKind::Bind(drop, _, rest) = kind else {
                            unreachable!("a drop plan applies to a bind");
                        };
                        let TypedCompKind::Drop(freed) = drop.kind else {
                            unreachable!("a drop plan applies to a drop computation");
                        };
                        work.push(ApplyFrame::FinishDrop { sig, freed });
                        work.push(ApplyFrame::Comp(*rest, *consume));
                    }
                    Plan::TryBindFirst { child } | Plan::ConsumeBindFirst { child } => {
                        let TypedCompKind::Bind(first, binder, rest) = kind else {
                            unreachable!("a first-child plan applies to a bind");
                        };
                        work.push(ApplyFrame::FinishBindFirst { sig, binder, rest });
                        work.push(ApplyFrame::Comp(*first, *child));
                    }
                    Plan::TryBindRest { child } | Plan::ConsumeBindRest { child } => {
                        let TypedCompKind::Bind(first, binder, rest) = kind else {
                            unreachable!("a continuation plan applies to a bind");
                        };
                        work.push(ApplyFrame::FinishBindRest { sig, first, binder });
                        work.push(ApplyFrame::Comp(*rest, *child));
                    }
                    Plan::TryIfYes { child } => {
                        let TypedCompKind::If(condition, yes, no) = kind else {
                            unreachable!("a then-branch plan applies to an if");
                        };
                        work.push(ApplyFrame::FinishIfYes { sig, condition, no });
                        work.push(ApplyFrame::Comp(*yes, *child));
                    }
                    Plan::TryIfNo { child } => {
                        let TypedCompKind::If(condition, yes, no) = kind else {
                            unreachable!("an else-branch plan applies to an if");
                        };
                        work.push(ApplyFrame::FinishIfNo {
                            sig,
                            condition,
                            yes,
                        });
                        work.push(ApplyFrame::Comp(*no, *child));
                    }
                    Plan::TryCase { arms } => {
                        let TypedCompKind::Case(scrutinee, source_arms) = kind else {
                            unreachable!("an arm plan applies to a case");
                        };
                        push_case_apply(&mut work, sig, scrutinee, source_arms, arms);
                    }
                    Plan::TryWithReuse { child } | Plan::ConsumeWithReuse { child } => {
                        let TypedCompKind::WithReuse { token, freed, body } = kind else {
                            unreachable!("a nested reuse plan applies to WithReuse");
                        };
                        work.push(ApplyFrame::FinishWithReuse { sig, token, freed });
                        work.push(ApplyFrame::Comp(*body, *child));
                    }
                    Plan::ConsumeReturn => {
                        let TypedCompKind::Return(value) = kind else {
                            unreachable!("an allocation plan applies to a return");
                        };
                        results.push(TypedComp::new(
                            sig,
                            TypedCompKind::Reuse(clone_binder(token), value),
                        ));
                    }
                    Plan::ConsumeIf { yes, no } => {
                        let TypedCompKind::If(condition, yes_comp, no_comp) = kind else {
                            unreachable!("a branch allocation plan applies to an if");
                        };
                        work.push(ApplyFrame::FinishIfBoth { sig, condition });
                        work.push(ApplyFrame::Comp(*no_comp, *no));
                        work.push(ApplyFrame::Comp(*yes_comp, *yes));
                    }
                    Plan::ConsumeCase { arms } => {
                        let TypedCompKind::Case(scrutinee, source_arms) = kind else {
                            unreachable!("an allocation arm plan applies to a case");
                        };
                        let arms: Vec<_> = arms.iter().copied().map(Some).collect();
                        push_case_apply(&mut work, sig, scrutinee, source_arms, &arms);
                    }
                }
            }
            ApplyFrame::FinishDrop { sig, freed } => {
                let body = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::WithReuse {
                        token: clone_binder(token),
                        freed,
                        body: Box::new(body),
                    },
                ));
            }
            ApplyFrame::FinishBindFirst { sig, binder, rest } => {
                let first = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::Bind(Box::new(first), binder, rest),
                ));
            }
            ApplyFrame::FinishBindRest { sig, first, binder } => {
                let rest = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::Bind(first, binder, Box::new(rest)),
                ));
            }
            ApplyFrame::FinishIfYes { sig, condition, no } => {
                let yes = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::If(condition, Box::new(yes), no),
                ));
            }
            ApplyFrame::FinishIfNo {
                sig,
                condition,
                yes,
            } => {
                let no = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::If(condition, yes, Box::new(no)),
                ));
            }
            ApplyFrame::FinishIfBoth { sig, condition } => {
                let no = pop_comp(&mut results);
                let yes = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::If(condition, Box::new(yes), Box::new(no)),
                ));
            }
            ApplyFrame::FinishCase {
                sig,
                scrutinee,
                arms,
                rewritten,
            } => {
                let start = results
                    .len()
                    .checked_sub(rewritten)
                    .expect("each selected arm has a rewritten body");
                let arms = {
                    let mut bodies = results.drain(start..);
                    let arms = arms
                        .into_iter()
                        .map(|arm| {
                            let body = arm
                                .body
                                .unwrap_or_else(|| bodies.next().expect("a rewritten arm exists"));
                            (arm.pattern, body)
                        })
                        .collect();
                    let extra_body = bodies.next();
                    debug_assert!(extra_body.is_none());
                    arms
                };
                results.push(TypedComp::new(sig, TypedCompKind::Case(scrutinee, arms)));
            }
            ApplyFrame::FinishWithReuse { sig, token, freed } => {
                let body = pop_comp(&mut results);
                results.push(TypedComp::new(
                    sig,
                    TypedCompKind::WithReuse {
                        token,
                        freed,
                        body: Box::new(body),
                    },
                ));
            }
        }
    }
    let result = pop_comp(&mut results);
    debug_assert!(results.is_empty());
    result
}

fn push_case_apply(
    work: &mut Vec<ApplyFrame>,
    sig: CompSig,
    scrutinee: TypedValue,
    source_arms: Vec<(TypedPattern, TypedComp)>,
    plans: &[Option<PlanId>],
) {
    debug_assert_eq!(source_arms.len(), plans.len());
    let mut selected = Vec::new();
    let mut arms = Vec::with_capacity(source_arms.len());
    for ((pattern, body), plan) in source_arms.into_iter().zip(plans.iter().copied()) {
        if let Some(plan) = plan {
            arms.push(ArmSlot {
                pattern,
                body: None,
            });
            selected.push((body, plan));
        } else {
            arms.push(ArmSlot {
                pattern,
                body: Some(body),
            });
        }
    }
    work.push(ApplyFrame::FinishCase {
        sig,
        scrutinee,
        arms,
        rewritten: selected.len(),
    });
    work.extend(
        selected
            .into_iter()
            .rev()
            .map(|(body, plan)| ApplyFrame::Comp(body, plan)),
    );
}

fn clone_binder(binder: &TypedBinder) -> TypedBinder {
    TypedBinder::new(binder.name, clone_core_type(&binder.ty))
}

struct ArmSlot {
    pattern: TypedPattern,
    body: Option<TypedComp>,
}

enum ApplyFrame {
    Comp(TypedComp, PlanId),
    FinishDrop {
        sig: CompSig,
        freed: TypedValue,
    },
    FinishBindFirst {
        sig: CompSig,
        binder: TypedBinder,
        rest: Box<TypedComp>,
    },
    FinishBindRest {
        sig: CompSig,
        first: Box<TypedComp>,
        binder: TypedBinder,
    },
    FinishIfYes {
        sig: CompSig,
        condition: TypedValue,
        no: Box<TypedComp>,
    },
    FinishIfNo {
        sig: CompSig,
        condition: TypedValue,
        yes: Box<TypedComp>,
    },
    FinishIfBoth {
        sig: CompSig,
        condition: TypedValue,
    },
    FinishCase {
        sig: CompSig,
        scrutinee: TypedValue,
        arms: Vec<ArmSlot>,
        rewritten: usize,
    },
    FinishWithReuse {
        sig: CompSig,
        token: TypedBinder,
        freed: TypedValue,
    },
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

/// Capacity of the boxed cell a constructor-pattern arm releases, or `None`
/// when the match frees no reusable cell. A constructor pattern proves that
/// the selected branch holds a boxed cell, including constructors from the
/// effect-runtime representation; the wired nullable is excluded because it
/// frees no cell when matched (its native form is the null word or the
/// element itself). Tuples still need their source tuple witness because
/// unboxed products share the tuple-pattern shape. Counting fields measures
/// the cell exactly because every cell slot is one runtime word, an invariant
/// the typed verifier checks at each constructor and boxed tuple.
pub(crate) fn reuse_cell_capacity(
    pattern: &TypedPattern,
    scrutinee_ty: &CoreType,
) -> Option<usize> {
    match (pattern, scrutinee_ty) {
        (TypedPattern::Ctor { name, .. }, _) if kw::is_or_null_ctor(name.as_str()) => None,
        (TypedPattern::Ctor { fields, .. }, _)
        | (TypedPattern::Tuple(fields), CoreType::Source(Type::Tuple(_))) => Some(fields.len()),
        _ => None,
    }
}

/// Arity of an allocation that can be rebuilt inside a spent shell, or `None`
/// when the value allocates no cell. The wired nullable allocates no cell, so
/// it can never spend a reuse credit. As with the capacity, the field count
/// measures the rebuilt cell exactly because each slot is one runtime word.
pub(crate) fn rebuild_arity(value: &TypedValue) -> Option<usize> {
    match &value.kind {
        TypedValueKind::Ctor { name, .. } if kw::is_or_null_ctor(name.as_str()) => None,
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
    use std::{mem, thread};

    use crate::core::fbip::{balanced, reuse as legacy_reuse, Sigs};
    use crate::core::{Comp, Core, CoreFn, Value};
    use crate::types::ty::EffRow;

    use super::super::verify::{ConstructorSig, VerifyEnv};
    use super::super::violation::{ArityBound, ReuseFault, Violation};
    use super::super::{verify, CompSig, CoreFnSig, TypedValueKind};
    use super::*;

    const DEEP_REUSE_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

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
        input: UncheckedTypedCore<Owned>,
        env: &VerifyEnv,
        balance: bool,
    ) -> TypedCore<ReuseLowered> {
        let input = verify(input, env)
            .unwrap_or_else(|violations| panic!("owned fixture is invalid: {violations:#?}"));
        let legacy_input = input.clone().erase();
        let expected = legacy_reuse(&legacy_input);
        let actual = verify(reuse(input), env).unwrap_or_else(|violations| {
            panic!("reuse-lowered fixture is invalid: {violations:#?}")
        });
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![scrutinee], body)]);
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![scrutinee], body)]);
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![scrutinee], body)]);
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![scrutinee], body)]);
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
        let input = UncheckedTypedCore::new(vec![main, factory]);
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![outer], body)]);
        let input = verify(input, &env).expect("shadowing fixture is valid Owned Core");
        let actual = reuse(input);
        let actual = verify(actual, &env).expect("the safe no-reuse result remains valid");
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![outer], body)]);
        let input = verify(input, &env).expect("pattern-shadow fixture is valid Owned Core");
        let actual = reuse(input);
        let actual = verify(actual, &env).expect("the safe no-reuse result remains valid");
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![cell, other], body)]);
        let input = verify(input, &env).expect("token-capture fixture is valid Owned Core");
        balanced(&input.clone().erase(), &Sigs::new()).expect("the Owned fixture is balanced");
        let actual = reuse(input);
        let actual = verify(actual, &env).expect("the safe no-reuse result remains valid");
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![outer, inner], outer_case)]);
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
        let input = UncheckedTypedCore::new(vec![function("main", vec![old], body)]);
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
        let forged =
            UncheckedTypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(forged, &env).expect_err("one branch leaves the credit live");
        assert!(violations.iter().any(|violation| matches!(
            violation.kind(),
            Violation::Reuse(ReuseFault::UnequalCredits(_))
        )));
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
        let forged =
            UncheckedTypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(forged, &env).expect_err("the rebuild exceeds the shell");
        assert!(violations.iter().any(|violation| matches!(
            violation.kind(),
            Violation::Arity {
                bound: ArityBound::ShellCapacity,
                ..
            }
        )));
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
        let forged =
            UncheckedTypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(forged, &env).expect_err("reuse needs case-shell authority");
        assert!(
            violations
                .iter()
                .any(|violation| violation.kind()
                    == &Violation::Reuse(ReuseFault::ScrutineeNotActive))
        );
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
        let forged =
            UncheckedTypedCore::<ReuseLowered>::new(vec![function("main", vec![freed], body)]);
        let violations = verify(forged, &env).expect_err("one shell cannot be freed twice");
        assert!(violations.iter().any(
            |violation| violation.kind() == &Violation::Reuse(ReuseFault::ScrutineeFreedTwice)
        ));
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

    #[test]
    fn reuse_handles_deep_successful_control_and_values_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-typed-reuse".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let shape = source(Type::Con(sym("Shape"), Vec::new()));
                let mut field = int(0);
                for _ in 0..DEEP_REUSE_DEPTH {
                    field = TypedValue::new(
                        source(Type::Int),
                        TypedValueKind::Reinterpret(Box::new(field)),
                    );
                }
                let mut body = ret(ctor("Narrow", 1, shape.clone(), vec![field]));
                for depth in 0..DEEP_REUSE_DEPTH {
                    body = if depth % 2 == 0 {
                        bind(
                            ret(int(0)),
                            TypedBinder::new(sym("_"), source(Type::Int)),
                            body,
                        )
                    } else {
                        TypedComp::new(
                            pure(shape.clone()),
                            TypedCompKind::If(
                                bool_(true),
                                Box::new(body),
                                Box::new(ret(ctor("Narrow", 1, shape.clone(), vec![int(0)]))),
                            ),
                        )
                    };
                }
                let body = case(
                    var("cell", shape.clone()),
                    pattern("Wide", 2),
                    after_drop("cell", shape, body),
                );
                // Semantic fixtures above exercise the verified public phase
                // transition. This hostile-depth fixture isolates its owned
                // term worklist from the verifier's independent traversal.
                let output = reuse_comp(body);

                let TypedCompKind::Case(_, arms) = output.kind() else {
                    panic!("reuse changed the enclosing case");
                };
                let TypedCompKind::WithReuse { token, body, .. } = arms[0].1.kind() else {
                    panic!("the deep path did not reuse its freed shell");
                };
                let mut cursor = body.as_ref();
                for depth in (0..DEEP_REUSE_DEPTH).rev() {
                    if depth % 2 == 0 {
                        let TypedCompKind::Bind(first, binder, rest) = cursor.kind() else {
                            panic!("reuse changed the deep bind spine");
                        };
                        assert!(matches!(first.kind(), TypedCompKind::Return(_)));
                        assert_eq!(binder.name.as_str(), "_");
                        cursor = rest;
                    } else {
                        let TypedCompKind::If(_, yes, no) = cursor.kind() else {
                            panic!("reuse changed the deep control spine");
                        };
                        assert!(matches!(
                            no.kind(),
                            TypedCompKind::Reuse(spent, _) if spent.name == token.name
                        ));
                        cursor = yes;
                    }
                }
                assert!(matches!(
                    cursor.kind(),
                    TypedCompKind::Reuse(spent, _) if spent.name == token.name
                ));
                mem::forget(output);
            })
            .expect("spawn deep typed reuse test")
            .join()
            .expect("deep typed reuse test panicked");
    }
}
