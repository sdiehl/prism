use std::{collections::BTreeMap, mem};

use prism_common::sym::Sym;

use crate::core::cbpv::{Comp, Core, CorePat, Value};
use crate::core::effect_check::{residual_effect_node, HANDLE_NODE};
use crate::core::fv::{comp as freev, pat_vars};

use super::imbalance::{Imbalance, TokenFault};
use super::{borrow_mask, borrowed_at, borrowed_call_vars, count_val, Set, Sigs};

type Env = BTreeMap<Sym, i64>;

struct CaseState<'a> {
    arms: &'a [(CorePat, Comp)],
    index: usize,
    loaned_scrutinee: bool,
    base: Env,
    merged: Option<Env>,
    outer_external: Set,
}

// Verify inserted RC operations with a linear token simulation. Counts must
// remain nonnegative, reach zero at scope exit, and agree across branches.
/// # Errors
/// The token fault that broke the simulation, attributed to the declaration it
/// was found in.
pub fn balanced(core: &Core, sigs: &Sigs) -> Result<(), Imbalance> {
    for f in &core.fns {
        // Token simulation is defined only for lowered Core.
        if let Some(node) = residual_effect_node(&f.body) {
            return Err(Imbalance::in_function(
                TokenFault::UnloweredEffect { node },
                f.name,
            ));
        }
        let mask = sigs.get(&f.name).map(Vec::as_slice);
        let mut env: Env = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| (*p, i64::from(!borrowed_at(mask, i))))
            .collect();
        let external: Set = f
            .params
            .iter()
            .enumerate()
            .filter(|(index, _)| borrowed_at(mask, *index))
            .map(|(_, param)| *param)
            .collect();
        simulate(&f.body, &mut env, sigs, &external)
            .map_err(|fault| Imbalance::in_function(fault, f.name))?;
        for (v, n) in &env {
            if v.as_str() != "_" && *n != 0 {
                return Err(Imbalance::in_function(
                    TokenFault::ScopeExit {
                        var: *v,
                        tokens: *n,
                    },
                    f.name,
                ));
            }
        }
    }
    Ok(())
}

fn consume(x: Sym, k: i64, env: &mut Env) -> Result<(), TokenFault> {
    if x.as_str() == "_" {
        return Ok(());
    }
    let e = env.entry(x).or_insert(0);
    *e -= k;
    if *e < 0 {
        return Err(TokenFault::BelowZero { var: x });
    }
    Ok(())
}

enum Frame<'a> {
    Comp(&'a Comp),
    UseValue(&'a Value),
    VerifyValue(&'a Value),
    BindRight {
        binder: Sym,
        body: &'a Comp,
        outer_external: Set,
    },
    RestoreExternal(Set),
    BranchElse {
        alternative: &'a Comp,
        base: Env,
    },
    BranchMerge {
        left: Env,
        base: Env,
    },
    FinishCaseArm {
        state: CaseState<'a>,
        pattern_vars: Set,
    },
    WithReuseBody {
        token: Sym,
        body: &'a Comp,
        outer_external: Set,
    },
    FinishLambda {
        parent_env: Env,
        parent_external: Set,
    },
}

struct Simulator<'a> {
    sigs: &'a Sigs,
    env: Env,
    external: Set,
    frames: Vec<Frame<'a>>,
}

impl<'a> Simulator<'a> {
    fn run(&mut self, root: &'a Comp) -> Result<(), TokenFault> {
        self.frames.push(Frame::Comp(root));
        while let Some(frame) = self.frames.pop() {
            self.step(frame)?;
        }
        Ok(())
    }

    fn step(&mut self, frame: Frame<'a>) -> Result<(), TokenFault> {
        match frame {
            Frame::Comp(comp) => self.comp(comp),
            Frame::UseValue(value) => self.use_value(value),
            Frame::VerifyValue(value) => {
                self.verify_value(value);
                Ok(())
            }
            Frame::BindRight {
                binder,
                body,
                outer_external,
            } => {
                if binder.as_str() != "_" {
                    self.env.insert(binder, 1);
                }
                self.external.clone_from(&outer_external);
                self.external.remove(&binder);
                self.frames.push(Frame::RestoreExternal(outer_external));
                self.frames.push(Frame::Comp(body));
                Ok(())
            }
            Frame::RestoreExternal(external) => {
                self.external = external;
                Ok(())
            }
            Frame::BranchElse { alternative, base } => {
                let left = mem::replace(&mut self.env, base.clone());
                self.frames.push(Frame::BranchMerge { left, base });
                self.frames.push(Frame::Comp(alternative));
                Ok(())
            }
            Frame::BranchMerge { left, mut base } => {
                merge(&left, &self.env, &mut base)?;
                self.env = base;
                Ok(())
            }
            Frame::FinishCaseArm {
                state,
                pattern_vars,
            } => self.finish_case_arm(state, pattern_vars),
            Frame::WithReuseBody {
                token,
                body,
                outer_external,
            } => {
                self.env.insert(token, 1);
                self.external.clone_from(&outer_external);
                self.external.remove(&token);
                self.frames.push(Frame::RestoreExternal(outer_external));
                self.frames.push(Frame::Comp(body));
                Ok(())
            }
            Frame::FinishLambda {
                parent_env,
                parent_external,
            } => {
                for (var, tokens) in &self.env {
                    if var.as_str() != "_" && *tokens != 0 {
                        return Err(TokenFault::ThunkCapture {
                            var: *var,
                            tokens: *tokens,
                        });
                    }
                }
                self.env = parent_env;
                self.external = parent_external;
                Ok(())
            }
        }
    }

    fn comp(&mut self, comp: &'a Comp) -> Result<(), TokenFault> {
        match comp {
            Comp::Dup(Value::Var(var)) => {
                *self.env.entry(*var).or_insert(0) += 1;
            }
            Comp::Drop(Value::Var(var)) => consume(*var, 1, &mut self.env)?,
            Comp::Bind(bound, binder, body) => {
                // Renaming a loan extends it without spending or minting a token.
                if let Comp::Return(Value::Var(var)) = &**bound {
                    if self.external.contains(var) && binder.as_str() != "_" {
                        self.env.insert(*binder, 0);
                        let outer_external = self.external.clone();
                        self.external.insert(*binder);
                        self.frames.push(Frame::RestoreExternal(outer_external));
                        self.frames.push(Frame::Comp(body));
                        return Ok(());
                    }
                }
                self.frames.push(Frame::BindRight {
                    binder: *binder,
                    body,
                    outer_external: self.external.clone(),
                });
                self.frames.push(Frame::Comp(bound));
            }
            Comp::If(_, consequent, alternative) => {
                self.frames.push(Frame::BranchElse {
                    alternative,
                    base: self.env.clone(),
                });
                self.frames.push(Frame::Comp(consequent));
            }
            Comp::Case(scrutinee, arms) => {
                if !arms.is_empty() {
                    // Fields borrowed from a loaned scrutinee remain loans.
                    self.begin_case_arm(CaseState {
                        arms,
                        index: 0,
                        loaned_scrutinee: matches!(
                            scrutinee,
                            Value::Var(var) if self.external.contains(var)
                        ),
                        base: self.env.clone(),
                        merged: None,
                        outer_external: self.external.clone(),
                    });
                }
            }
            Comp::Return(value)
            | Comp::Force(value)
            | Comp::Error(value)
            | Comp::FloatBuiltin(_, value)
            | Comp::Neg(_, value)
            | Comp::UnboxedProject(value, _)
            | Comp::RefNew(value)
            | Comp::RefGet(value) => self.frames.push(Frame::UseValue(value)),
            Comp::RefSet(cell, value) | Comp::InitAt(cell, value) => {
                self.frames.push(Frame::UseValue(value));
                self.frames.push(Frame::UseValue(cell));
            }
            Comp::WithReuse { token, freed, body } => {
                self.frames.push(Frame::WithReuseBody {
                    token: *token,
                    body,
                    outer_external: self.external.clone(),
                });
                self.frames.push(Frame::UseValue(freed));
            }
            Comp::App(function, args) => {
                for var in freev(function) {
                    consume(var, 1, &mut self.env)?;
                }
                self.push_values(args);
            }
            Comp::Prim(_, left, right) => {
                self.frames.push(Frame::UseValue(right));
                self.frames.push(Frame::UseValue(left));
            }
            Comp::Call(callee, args) => self.call(*callee, args)?,
            Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
                self.push_values(args);
            }
            Comp::Reuse(token, value) => {
                consume(*token, 1, &mut self.env)?;
                self.frames.push(Frame::UseValue(value));
            }
            Comp::Mask(_, body) => self.frames.push(Frame::Comp(body)),
            // Lambda bodies run in an isolated token environment. Captures are
            // loans, while parameters start with one owned token.
            Comp::Lam(params, body) => self.enter_lambda(params, body),
            // The RC inserter emits Dup and Drop only for variables.
            Comp::Dup(_) | Comp::Drop(_) => {}
            Comp::Handle { .. } => {
                return Err(TokenFault::UnloweredEffect { node: HANDLE_NODE });
            }
        }
        Ok(())
    }

    fn use_value(&mut self, value: &'a Value) -> Result<(), TokenFault> {
        let mut counts = BTreeMap::new();
        count_val(value, &mut counts);
        for (var, count) in counts {
            consume(var, i64::try_from(count).unwrap_or(i64::MAX), &mut self.env)?;
        }
        self.frames.push(Frame::VerifyValue(value));
        Ok(())
    }

    fn verify_value(&mut self, value: &'a Value) {
        match value {
            Value::Thunk(comp) => match &**comp {
                Comp::Lam(params, body) => self.enter_lambda(params, body),
                body => self.enter_lambda(&[], body),
            },
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                for field in fields.iter().rev() {
                    self.frames.push(Frame::VerifyValue(field));
                }
            }
            Value::UnboxedRecord(fields) => {
                for (_, field) in fields.iter().rev() {
                    self.frames.push(Frame::VerifyValue(field));
                }
            }
            _ => {}
        }
    }

    fn enter_lambda(&mut self, params: &[Sym], body: &'a Comp) {
        let params: Set = params.iter().copied().collect();
        let free = freev(body);
        let external = free.difference(&params).copied().collect();
        let mut env: Env = free.into_iter().map(|var| (var, 0)).collect();
        for param in params {
            env.insert(param, 1);
        }
        let parent_env = mem::replace(&mut self.env, env);
        let parent_external = mem::replace(&mut self.external, external);
        self.frames.push(Frame::FinishLambda {
            parent_env,
            parent_external,
        });
        self.frames.push(Frame::Comp(body));
    }

    fn call(&mut self, callee: Sym, args: &'a [Value]) -> Result<(), TokenFault> {
        let mask = borrow_mask(callee, self.sigs);
        let borrowed = borrowed_call_vars(callee, args, self.sigs)?;
        let mut consumed = BTreeMap::new();
        for (index, arg) in args.iter().enumerate() {
            if !borrowed_at(mask, index) {
                count_val(arg, &mut consumed);
            }
        }
        for var in borrowed {
            let live = self.env.get(&var).copied().unwrap_or(0);
            let spent = i64::try_from(consumed.get(&var).copied().unwrap_or(0)).unwrap_or(i64::MAX);
            if !self.external.contains(&var) && live - spent < 1 {
                return Err(TokenFault::BorrowNotLive { var, callee });
            }
        }
        for (index, arg) in args.iter().enumerate().rev() {
            if !borrowed_at(mask, index) {
                self.frames.push(Frame::UseValue(arg));
            }
        }
        Ok(())
    }

    fn push_values(&mut self, values: &'a [Value]) {
        for value in values.iter().rev() {
            self.frames.push(Frame::UseValue(value));
        }
    }

    fn begin_case_arm(&mut self, state: CaseState<'a>) {
        let (pattern, body) = &state.arms[state.index];
        let mut pattern_vars = Set::new();
        pat_vars(pattern, &mut pattern_vars);
        self.env = state.base.clone();
        for var in &pattern_vars {
            self.env.insert(*var, 0);
        }
        self.external.clone_from(&state.outer_external);
        for var in &pattern_vars {
            if state.loaned_scrutinee {
                self.external.insert(*var);
            } else {
                self.external.remove(var);
            }
        }
        self.frames.push(Frame::FinishCaseArm {
            state,
            pattern_vars,
        });
        self.frames.push(Frame::Comp(body));
    }

    fn finish_case_arm(
        &mut self,
        mut state: CaseState<'a>,
        pattern_vars: Set,
    ) -> Result<(), TokenFault> {
        for var in pattern_vars {
            if self.env.get(&var).copied().unwrap_or(0) != 0 {
                return Err(TokenFault::ArmLeak { field: var });
            }
            self.env.remove(&var);
        }
        self.external.clone_from(&state.outer_external);
        state.merged = Some(match state.merged {
            None => self.env.clone(),
            Some(previous) => {
                let mut out = state.base.clone();
                merge(&previous, &self.env, &mut out)?;
                out
            }
        });
        state.index += 1;
        if state.index < state.arms.len() {
            self.begin_case_arm(state);
        } else {
            self.env = state.merged.expect("a completed case has an arm");
        }
        Ok(())
    }
}

fn simulate(root: &Comp, env: &mut Env, sigs: &Sigs, external: &Set) -> Result<(), TokenFault> {
    let mut simulator = Simulator {
        sigs,
        env: env.clone(),
        external: external.clone(),
        frames: Vec::new(),
    };
    simulator.run(root)?;
    *env = simulator.env;
    Ok(())
}

fn merge(
    a: &BTreeMap<Sym, i64>,
    b: &BTreeMap<Sym, i64>,
    out: &mut BTreeMap<Sym, i64>,
) -> Result<(), TokenFault> {
    let keys: Set = a.keys().chain(b.keys()).copied().collect();
    for k in keys {
        let (va, vb) = (
            a.get(&k).copied().unwrap_or(0),
            b.get(&k).copied().unwrap_or(0),
        );
        if va != vb {
            return Err(TokenFault::BranchDisagreement {
                var: k,
                left: va,
                right: vb,
            });
        }
        out.insert(k, va);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{iter, mem, thread};

    use super::*;
    use crate::core::cbpv::{CheckedHandler, CoreFn};

    const DEEP_BALANCE_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    #[test]
    fn balanced_handles_deep_computations_and_thunks_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-balance".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut value = Value::Thunk(Box::new(Comp::Return(Value::Unit)));
                for _ in 0..DEEP_BALANCE_DEPTH {
                    value = Value::Tuple(vec![value]);
                }
                let mut body = Comp::Return(value);
                for _ in 0..DEEP_BALANCE_DEPTH {
                    body = Comp::Bind(
                        Box::new(Comp::Return(Value::Int(0))),
                        Sym::new("_"),
                        Box::new(body),
                    );
                }
                let core = Core {
                    fns: vec![CoreFn {
                        name: Sym::new("deep_balance"),
                        params: Vec::new(),
                        body,
                        dict_arity: 0,
                    }],
                };

                assert_eq!(balanced(&core, &Sigs::new()), Ok(()));
                mem::forget(core);
            })
            .expect("spawn deep balance test")
            .join()
            .expect("deep balance test panicked");
    }

    #[test]
    fn borrowed_immediate_needs_no_retained_token() {
        let observe = Sym::new("observe_immediate");
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller_immediate"),
                params: Vec::new(),
                body: Comp::Call(observe, vec![Value::Int(42)]),
                dict_arity: 0,
            }],
        };
        let sigs = iter::once((observe, vec![true])).collect();

        assert_eq!(balanced(&core, &sigs), Ok(()));
    }

    #[test]
    fn borrowed_static_str_needs_no_retained_token() {
        let observe = Sym::new("observe_str");
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller_str"),
                params: Vec::new(),
                body: Comp::Call(observe, vec![Value::Str("static".into())]),
                dict_arity: 0,
            }],
        };
        let sigs = iter::once((observe, vec![true])).collect();

        assert_eq!(balanced(&core, &sigs), Ok(()));
    }

    #[test]
    fn borrowed_boxed_scalar_must_be_let_bound() {
        let observe = Sym::new("observe_float");
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller_float"),
                params: Vec::new(),
                body: Comp::Call(observe, vec![Value::Float(2.5)]),
                dict_arity: 0,
            }],
        };
        let sigs = iter::once((observe, vec![true])).collect();

        let error = balanced(&core, &sigs).expect_err("a boxed literal loan needs an owner");
        assert_eq!(
            error.fault,
            TokenFault::BorrowedArgNotBound {
                callee: observe,
                arg: Box::new(Value::Float(2.5)),
            }
        );
    }

    #[test]
    fn borrowed_heap_temporary_must_be_let_bound() {
        let observe = Sym::new("observe_heap");
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller_heap"),
                params: Vec::new(),
                body: Comp::Call(
                    observe,
                    vec![Value::Ctor("Box".into(), 0, vec![Value::Int(42)])],
                ),
                dict_arity: 0,
            }],
        };
        let sigs = iter::once((observe, vec![true])).collect();

        let error = balanced(&core, &sigs).expect_err("heap loan needs a caller-owned token");
        assert_eq!(
            error.fault,
            TokenFault::BorrowedArgNotBound {
                callee: observe,
                arg: Box::new(Value::Ctor("Box".into(), 0, vec![Value::Int(42)])),
            }
        );
    }

    #[test]
    fn rejects_a_drop_before_the_last_borrowed_call() {
        let retained = Sym::new("retained");
        let observe = Sym::new("observe");
        let body = Comp::Bind(
            Box::new(Comp::Drop(Value::Var(retained))),
            Sym::new("_"),
            Box::new(Comp::Call(observe, vec![Value::Var(retained)])),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller"),
                params: vec![retained],
                body,
                dict_arity: 0,
            }],
        };
        let sigs = iter::once((observe, vec![true])).collect();

        let error = balanced(&core, &sigs).expect_err("pre-call drop must end the loan");
        assert_eq!(
            error.fault,
            TokenFault::BorrowNotLive {
                var: retained,
                callee: observe,
            }
        );
    }

    #[test]
    fn a_shadowing_binder_does_not_inherit_an_external_loan() {
        let borrowed = Sym::new("borrowed");
        let observe = Sym::new("observe");
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Unit)),
            borrowed,
            Box::new(Comp::Bind(
                Box::new(Comp::Drop(Value::Var(borrowed))),
                Sym::new("_"),
                Box::new(Comp::Call(observe, vec![Value::Var(borrowed)])),
            )),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller"),
                params: vec![borrowed],
                body,
                dict_arity: 0,
            }],
        };
        let sigs = [(Sym::new("caller"), vec![true]), (observe, vec![true])]
            .into_iter()
            .collect();

        let error = balanced(&core, &sigs).expect_err("inner binder owns its own loan");
        assert_eq!(
            error.fault,
            TokenFault::BorrowNotLive {
                var: borrowed,
                callee: observe,
            }
        );
    }

    // The simulation cannot see into a handler's clauses, so a tree that still
    // carries one must be refused, never certified as balanced. This must hold
    // in release builds too, where a debug assertion would compile away.
    #[test]
    fn an_unlowered_handler_is_refused_not_certified() {
        let name = Sym::new("unlowered");
        let core = Core {
            fns: vec![CoreFn {
                name,
                params: Vec::new(),
                body: Comp::Handle {
                    body: Box::new(Comp::Return(Value::Unit)),
                    return_var: None,
                    return_body: None,
                    ops: CheckedHandler::new(Vec::new()).expect("no clauses, no duplicates"),
                },
                dict_arity: 0,
            }],
        };
        let sigs = Sigs::new();

        let error = balanced(&core, &sigs).expect_err("an unlowered handler must be refused");
        assert_eq!(
            error.fault,
            TokenFault::UnloweredEffect { node: HANDLE_NODE }
        );
        assert_eq!(error.function, Some(name));
    }
}
