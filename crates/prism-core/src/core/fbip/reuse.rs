use prism_common::sym::Sym;
use prism_syntax::kw;
use prism_syntax::names::reuse_token;

use crate::core::cbpv::{Comp, Core, CoreFn, CorePat, Value};
use crate::core::traverse::{Rewrite, RewriteControl};

#[must_use]
pub fn reuse(core: &Core) -> Core {
    let mut rewrite = ReuseRewrite;
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                dict_arity: f.dict_arity,
                body: rewrite.rewrite_comp(&f.body, &()),
            })
            .collect(),
    }
}

struct ReuseRewrite;

impl Rewrite for ReuseRewrite {
    type Ctx = ();

    fn enter_comp(&mut self, comp: &Comp, _cx: &Self::Ctx) -> RewriteControl<Comp> {
        match comp {
            Comp::Bind(..)
            | Comp::If(..)
            | Comp::Lam(..)
            | Comp::Case(..)
            | Comp::Handle { .. } => RewriteControl::Descend,
            _ => RewriteControl::Replace(clone_comp(comp)),
        }
    }

    fn enter_value(&mut self, value: &Value, _cx: &Self::Ctx) -> RewriteControl<Value> {
        RewriteControl::Replace(clone_value(value))
    }

    fn leave_comp(&mut self, source: &Comp, rewritten: Comp, _cx: &Self::Ctx) -> Comp {
        let Comp::Case(source_scrutinee, _) = source else {
            return rewritten;
        };
        let Comp::Case(scrutinee, arms) = rewritten else {
            unreachable!("a case rebuild remains a case");
        };
        Comp::Case(
            scrutinee,
            arms.into_iter()
                .map(|(pattern, body)| {
                    let body = reuse_arm(source_scrutinee, &pattern, body);
                    (pattern, body)
                })
                .collect(),
        )
    }
}

struct CoreClone;

impl Rewrite for CoreClone {
    type Ctx = ();
}

fn clone_comp(comp: &Comp) -> Comp {
    CoreClone.rewrite_comp(comp, &())
}

fn clone_value(value: &Value) -> Value {
    CoreClone.rewrite_value(value, &())
}

fn reuse_arm(scrut: &Value, p: &CorePat, body: Comp) -> Comp {
    let Value::Var(s) = scrut else {
        return body;
    };
    let arity = match p {
        // The wired nullable frees no cell when matched (its native form is
        // the null word or the element itself), so it can never seed a token.
        CorePat::Ctor(name, _) if kw::is_or_null_ctor(name.as_str()) => return body,
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => fields.len(),
        _ => return body,
    };
    let tok: Sym = reuse_token(s.as_str()).into();
    // Decline unless the freed cell can be spent exactly once on every path.
    // Success is balanced by construction: `WithReuse` frees the cell and each
    // selected allocation consumes its scoped token.
    try_reuse(body, *s, tok, arity).unwrap_or_else(|body| body)
}

// Pair `drop s` with a later fitting allocation. After the drop, every control
// path must spend the token exactly once; arms without the drop stay untouched.
fn try_reuse(c: Comp, s: Sym, tok: Sym, cap: usize) -> Result<Comp, Comp> {
    let mut plans = Vec::new();
    let Some(root) = plan_try_reuse(&c, s, cap, &mut plans) else {
        return Err(c);
    };
    Ok(apply_plan(c, root, &plans, s, tok))
}

fn plan_try_reuse(c: &Comp, s: Sym, cap: usize, plans: &mut Vec<Plan>) -> Option<PlanId> {
    let mut work = vec![TryFrame::Comp(c)];
    let mut results = Vec::new();

    while let Some(frame) = work.pop() {
        match frame {
            TryFrame::Comp(comp) => match comp {
                Comp::Bind(first, _, rest) => {
                    if matches!(first.as_ref(), Comp::Drop(Value::Var(d)) if *d == s) {
                        let plan = plan_consume_alloc(rest, cap, plans)
                            .map(|consume| push_plan(plans, Plan::TryDrop { consume }));
                        results.push(plan);
                    } else {
                        work.push(TryFrame::BindFirst { rest });
                        work.push(TryFrame::Comp(first));
                    }
                }
                Comp::If(_, yes, no) => {
                    work.push(TryFrame::FinishIf);
                    work.push(TryFrame::Comp(no));
                    work.push(TryFrame::Comp(yes));
                }
                Comp::Case(_, arms) => {
                    work.push(TryFrame::FinishCase {
                        arm_count: arms.len(),
                    });
                    work.extend(arms.iter().rev().map(|(_, body)| TryFrame::Comp(body)));
                }
                Comp::WithReuse { body, .. } => {
                    work.push(TryFrame::FinishWithReuse);
                    work.push(TryFrame::Comp(body));
                }
                _ => results.push(None),
            },
            TryFrame::BindFirst { rest } => {
                if let Some(child) = pop_plan(&mut results) {
                    results.push(Some(push_plan(plans, Plan::TryBindFirst { child })));
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
                    .expect("each case arm has a reuse result");
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
    Comp(&'a Comp),
    BindFirst { rest: &'a Comp },
    BindRest,
    FinishIf,
    FinishCase { arm_count: usize },
    FinishWithReuse,
}

// Spend the credit on the first fitting allocation. Every branch must spend it;
// a non-allocating path declines the whole rewrite.
fn plan_consume_alloc(c: &Comp, cap: usize, plans: &mut Vec<Plan>) -> Option<PlanId> {
    let mut work = vec![ConsumeFrame::Comp(c)];
    let mut results = Vec::new();

    while let Some(frame) = work.pop() {
        match frame {
            ConsumeFrame::Comp(comp) => match comp {
                Comp::Bind(first, _, rest) => {
                    work.push(ConsumeFrame::BindFirst { rest });
                    work.push(ConsumeFrame::Comp(first));
                }
                Comp::Return(value @ (Value::Ctor(..) | Value::Tuple(..)))
                    if ctor_arity(value) <= cap && !is_or_null_alloc(value) =>
                {
                    results.push(Some(push_plan(plans, Plan::ConsumeReturn)));
                }
                Comp::If(_, yes, no) => {
                    work.push(ConsumeFrame::IfYes { no });
                    work.push(ConsumeFrame::Comp(yes));
                }
                Comp::Case(_, arms) if arms.is_empty() => {
                    results.push(Some(push_plan(
                        plans,
                        Plan::ConsumeCase { arms: Vec::new() },
                    )));
                }
                Comp::Case(_, arms) => {
                    work.push(ConsumeFrame::CaseArm {
                        arms,
                        index: 0,
                        rebuilt: Vec::with_capacity(arms.len()),
                    });
                    work.push(ConsumeFrame::Comp(&arms[0].1));
                }
                Comp::WithReuse { body, .. } => {
                    work.push(ConsumeFrame::FinishWithReuse);
                    work.push(ConsumeFrame::Comp(body));
                }
                _ => results.push(None),
            },
            ConsumeFrame::BindFirst { rest } => {
                if let Some(child) = pop_plan(&mut results) {
                    results.push(Some(push_plan(plans, Plan::ConsumeBindFirst { child })));
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
            ConsumeFrame::IfYes { no, .. } => {
                if let Some(yes) = pop_plan(&mut results) {
                    work.push(ConsumeFrame::IfNo { yes });
                    work.push(ConsumeFrame::Comp(no));
                } else {
                    // The recursive implementation stopped before visiting the
                    // second branch when the first failed.
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
    Comp(&'a Comp),
    BindFirst {
        rest: &'a Comp,
    },
    BindRest,
    IfYes {
        no: &'a Comp,
    },
    IfNo {
        yes: PlanId,
    },
    CaseArm {
        arms: &'a [(CorePat, Comp)],
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

fn apply_plan(c: Comp, root: PlanId, plans: &[Plan], freed: Sym, token: Sym) -> Comp {
    let mut work = vec![ApplyFrame::Comp(c, root)];
    let mut results = Vec::new();

    while let Some(frame) = work.pop() {
        match frame {
            ApplyFrame::Comp(comp, id) => match &plans[id] {
                Plan::TryDrop { consume } => {
                    let Comp::Bind(drop, _, rest) = comp else {
                        unreachable!("a drop plan applies to a bind");
                    };
                    debug_assert!(matches!(drop.as_ref(), Comp::Drop(Value::Var(_))));
                    work.push(ApplyFrame::FinishDrop);
                    work.push(ApplyFrame::Comp(*rest, *consume));
                }
                Plan::TryBindFirst { child } | Plan::ConsumeBindFirst { child } => {
                    let Comp::Bind(first, binder, rest) = comp else {
                        unreachable!("a first-child plan applies to a bind");
                    };
                    work.push(ApplyFrame::FinishBindFirst { binder, rest });
                    work.push(ApplyFrame::Comp(*first, *child));
                }
                Plan::TryBindRest { child } | Plan::ConsumeBindRest { child } => {
                    let Comp::Bind(first, binder, rest) = comp else {
                        unreachable!("a continuation plan applies to a bind");
                    };
                    work.push(ApplyFrame::FinishBindRest { first, binder });
                    work.push(ApplyFrame::Comp(*rest, *child));
                }
                Plan::TryIfYes { child } => {
                    let Comp::If(condition, yes, no) = comp else {
                        unreachable!("a then-branch plan applies to an if");
                    };
                    work.push(ApplyFrame::FinishIfYes { condition, no });
                    work.push(ApplyFrame::Comp(*yes, *child));
                }
                Plan::TryIfNo { child } => {
                    let Comp::If(condition, yes, no) = comp else {
                        unreachable!("an else-branch plan applies to an if");
                    };
                    work.push(ApplyFrame::FinishIfNo { condition, yes });
                    work.push(ApplyFrame::Comp(*no, *child));
                }
                Plan::TryCase { arms: arm_plans } => {
                    let Comp::Case(scrutinee, arms) = comp else {
                        unreachable!("an arm plan applies to a case");
                    };
                    push_case_apply(&mut work, scrutinee, arms, arm_plans);
                }
                Plan::TryWithReuse { child } | Plan::ConsumeWithReuse { child } => {
                    let Comp::WithReuse { token, freed, body } = comp else {
                        unreachable!("a nested reuse plan applies to WithReuse");
                    };
                    work.push(ApplyFrame::FinishWithReuse { token, freed });
                    work.push(ApplyFrame::Comp(*body, *child));
                }
                Plan::ConsumeReturn => {
                    let Comp::Return(value) = comp else {
                        unreachable!("an allocation plan applies to a return");
                    };
                    results.push(Comp::Reuse(token, value));
                }
                Plan::ConsumeIf { yes, no } => {
                    let Comp::If(condition, yes_comp, no_comp) = comp else {
                        unreachable!("a branch allocation plan applies to an if");
                    };
                    work.push(ApplyFrame::FinishIfBoth { condition });
                    work.push(ApplyFrame::Comp(*no_comp, *no));
                    work.push(ApplyFrame::Comp(*yes_comp, *yes));
                }
                Plan::ConsumeCase { arms: arm_plans } => {
                    let Comp::Case(scrutinee, arms) = comp else {
                        unreachable!("an allocation arm plan applies to a case");
                    };
                    let arm_plans: Vec<_> = arm_plans.iter().copied().map(Some).collect();
                    push_case_apply(&mut work, scrutinee, arms, &arm_plans);
                }
            },
            ApplyFrame::FinishDrop => {
                let body = results.pop().expect("a reused continuation exists");
                results.push(Comp::WithReuse {
                    token,
                    freed: Value::Var(freed),
                    body: Box::new(body),
                });
            }
            ApplyFrame::FinishBindFirst { binder, rest } => {
                let first = results.pop().expect("a rewritten bound computation exists");
                results.push(Comp::Bind(Box::new(first), binder, rest));
            }
            ApplyFrame::FinishBindRest { first, binder } => {
                let rest = results.pop().expect("a rewritten continuation exists");
                results.push(Comp::Bind(first, binder, Box::new(rest)));
            }
            ApplyFrame::FinishIfYes { condition, no } => {
                let yes = results.pop().expect("a rewritten then branch exists");
                results.push(Comp::If(condition, Box::new(yes), no));
            }
            ApplyFrame::FinishIfNo { condition, yes } => {
                let no = results.pop().expect("a rewritten else branch exists");
                results.push(Comp::If(condition, yes, Box::new(no)));
            }
            ApplyFrame::FinishIfBoth { condition } => {
                let no = results.pop().expect("a rewritten else branch exists");
                let yes = results.pop().expect("a rewritten then branch exists");
                results.push(Comp::If(condition, Box::new(yes), Box::new(no)));
            }
            ApplyFrame::FinishCase {
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
                results.push(Comp::Case(scrutinee, arms));
            }
            ApplyFrame::FinishWithReuse { token, freed } => {
                let body = results.pop().expect("a rewritten reuse body exists");
                results.push(Comp::WithReuse {
                    token,
                    freed,
                    body: Box::new(body),
                });
            }
        }
    }

    let result = results.pop().expect("the root has a rewritten computation");
    debug_assert!(results.is_empty());
    result
}

fn push_case_apply(
    work: &mut Vec<ApplyFrame>,
    scrutinee: Value,
    arms: Vec<(CorePat, Comp)>,
    plans: &[Option<PlanId>],
) {
    debug_assert_eq!(arms.len(), plans.len());
    let mut selected = Vec::new();
    let mut slots = Vec::with_capacity(arms.len());
    for ((pattern, body), plan) in arms.into_iter().zip(plans.iter().copied()) {
        if let Some(plan) = plan {
            slots.push(ArmSlot {
                pattern,
                body: None,
            });
            selected.push((body, plan));
        } else {
            slots.push(ArmSlot {
                pattern,
                body: Some(body),
            });
        }
    }
    work.push(ApplyFrame::FinishCase {
        scrutinee,
        arms: slots,
        rewritten: selected.len(),
    });
    work.extend(
        selected
            .into_iter()
            .rev()
            .map(|(body, plan)| ApplyFrame::Comp(body, plan)),
    );
}

struct ArmSlot {
    pattern: CorePat,
    body: Option<Comp>,
}

enum ApplyFrame {
    Comp(Comp, PlanId),
    FinishDrop,
    FinishBindFirst {
        binder: Sym,
        rest: Box<Comp>,
    },
    FinishBindRest {
        first: Box<Comp>,
        binder: Sym,
    },
    FinishIfYes {
        condition: Value,
        no: Box<Comp>,
    },
    FinishIfNo {
        condition: Value,
        yes: Box<Comp>,
    },
    FinishIfBoth {
        condition: Value,
    },
    FinishCase {
        scrutinee: Value,
        arms: Vec<ArmSlot>,
        rewritten: usize,
    },
    FinishWithReuse {
        token: Sym,
        freed: Value,
    },
}

const fn ctor_arity(v: &Value) -> usize {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.len(),
        _ => 0,
    }
}

// The wired nullable allocates no cell, so it can never spend a reuse credit.
fn is_or_null_alloc(v: &Value) -> bool {
    matches!(v, Value::Ctor(name, ..) if kw::is_or_null_ctor(name.as_str()))
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;

    const DEEP_REUSE_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;
    const TEST_CTOR_TAG: usize = 0;

    fn allocation(name: &str, fields: usize) -> Comp {
        Comp::Return(Value::Ctor(
            Sym::new(name),
            TEST_CTOR_TAG,
            vec![Value::Unit; fields],
        ))
    }

    fn drop_then(cell: Sym, body: Comp) -> Comp {
        Comp::Bind(
            Box::new(Comp::Drop(Value::Var(cell))),
            Sym::new("_drop"),
            Box::new(body),
        )
    }

    fn one_arm_core(cell: Sym, fields: usize, body: Comp) -> Core {
        Core {
            fns: vec![CoreFn {
                name: Sym::new("reuse_test"),
                params: Vec::new(),
                body: Comp::Case(
                    Value::Var(cell),
                    vec![(CorePat::Ctor(Sym::new("Shell"), vec![None; fields]), body)],
                ),
                dict_arity: 0,
            }],
        }
    }

    #[test]
    fn reuse_spends_the_token_on_the_first_fitting_allocation() {
        let cell = Sym::new("cell");
        let body = drop_then(
            cell,
            Comp::Bind(
                Box::new(allocation("TooWide", 2)),
                Sym::new("wide"),
                Box::new(allocation("Fits", 1)),
            ),
        );

        let output = reuse(&one_arm_core(cell, 1, body));
        let Comp::Case(_, arms) = &output.fns[0].body else {
            panic!("reuse changed the enclosing case");
        };
        let Comp::WithReuse { token, body, .. } = &arms[0].1 else {
            panic!("the freed shell did not seed a reuse token");
        };
        let Comp::Bind(first, binder, rest) = body.as_ref() else {
            panic!("reuse changed the allocation bind");
        };
        assert!(matches!(
            first.as_ref(),
            Comp::Return(Value::Ctor(name, _, fields))
                if name.as_str() == "TooWide" && fields.len() == 2
        ));
        assert_eq!(binder.as_str(), "wide");
        assert!(matches!(
            rest.as_ref(),
            Comp::Reuse(spent, Value::Ctor(name, _, fields))
                if spent == token && name.as_str() == "Fits" && fields.len() == 1
        ));
    }

    #[test]
    fn reuse_requires_every_path_after_the_drop_to_allocate() {
        let cell = Sym::new("cell");
        let branch = Comp::If(
            Value::Bool(true),
            Box::new(allocation("Fits", 1)),
            Box::new(Comp::Return(Value::Int(0))),
        );
        let output = reuse(&one_arm_core(cell, 1, drop_then(cell, branch)));
        let Comp::Case(_, arms) = &output.fns[0].body else {
            panic!("reuse changed the enclosing case");
        };
        assert!(matches!(arms[0].1, Comp::Bind(..)));
    }

    #[test]
    fn reuse_rewrites_exactly_one_pre_drop_branch() {
        let cell = Sym::new("cell");
        let body = Comp::If(
            Value::Bool(true),
            Box::new(drop_then(cell, allocation("Fits", 1))),
            Box::new(Comp::Return(Value::Int(0))),
        );
        let output = reuse(&one_arm_core(cell, 1, body));
        let Comp::Case(_, arms) = &output.fns[0].body else {
            panic!("reuse changed the enclosing case");
        };
        let Comp::If(_, yes, no) = &arms[0].1 else {
            panic!("reuse changed the conditional");
        };
        assert!(matches!(yes.as_ref(), Comp::WithReuse { .. }));
        assert!(matches!(no.as_ref(), Comp::Return(Value::Int(0))));
    }

    #[test]
    fn reuse_handles_deep_control_and_reconstruction_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-reuse".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let cell = Sym::new("cell");
                let mut body = allocation("Fits", 1);
                for depth in 0..DEEP_REUSE_DEPTH {
                    body = if depth % 2 == 0 {
                        Comp::Bind(
                            Box::new(Comp::Return(Value::Int(0))),
                            Sym::new("_"),
                            Box::new(body),
                        )
                    } else {
                        Comp::If(
                            Value::Bool(true),
                            Box::new(body),
                            Box::new(allocation("Fits", 1)),
                        )
                    };
                }
                let input = one_arm_core(cell, 1, drop_then(cell, body));
                let output = reuse(&input);

                let Comp::Case(_, arms) = &output.fns[0].body else {
                    panic!("reuse changed the enclosing case");
                };
                let Comp::WithReuse { token, body, .. } = &arms[0].1 else {
                    panic!("the deep path did not reuse its freed shell");
                };
                let mut cursor = body.as_ref();
                for depth in (0..DEEP_REUSE_DEPTH).rev() {
                    if depth % 2 == 0 {
                        let Comp::Bind(first, binder, rest) = cursor else {
                            panic!("reuse changed the deep bind spine");
                        };
                        assert!(matches!(first.as_ref(), Comp::Return(Value::Int(0))));
                        assert_eq!(binder.as_str(), "_");
                        cursor = rest;
                    } else {
                        let Comp::If(Value::Bool(true), yes, no) = cursor else {
                            panic!("reuse changed the deep control spine");
                        };
                        assert!(matches!(no.as_ref(), Comp::Reuse(spent, _) if spent == token));
                        cursor = yes;
                    }
                }
                assert!(matches!(cursor, Comp::Reuse(spent, _) if spent == token));

                mem::forget(output);
                mem::forget(input);
            })
            .expect("spawn deep reuse test")
            .join()
            .expect("deep reuse test panicked");
    }
}
