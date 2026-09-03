//! Core Lint: the core-to-core sanity net.
//!
//! A well-formedness check run between optimization passes (under
//! `PRISM_CORE_LINT`, and in the lint-gated corpus test). A failure is a
//! compiler bug, an optimization pass that produced ill-formed Core, attributed
//! to the offending function so the culprit pass is obvious.
//!
//! Two invariants are checked:
//!
//! * Scoping, the single most valuable invariant and the one a buggy rewrite (a
//!   captured binder, a clone referencing a freed name) breaks first: every free
//!   variable of a function body must be a parameter or a top-level function
//!   (referenced first-class). This rides `fv`, which already subtracts every
//!   internal binder (let, lambda, case pattern, handler return/op/resume, reuse
//!   token), so a leak shows up as an unexpected free var.
//!
//! * Reuse-token linearity: a `WithReuse` frees a cell and binds its shell as a
//!   token that `Reuse` spends by overwriting the shell in place. Spending the
//!   same token twice on one path is a double in-place write (silent heap
//!   corruption) that scoping cannot see, since both uses are in scope. The
//!   `spends` walk counts spends along the worst-case single path (sequential
//!   composition adds, branches take the max), so a token spent more than once
//!   on any path is flagged. The complementary leak direction (a token never
//!   spent) is already gated dynamically by the runtime cell-balance check.
//!
//! Constructor arity against the ctor table and ANF argument shape are outside
//! this lint's current contract.

use std::collections::BTreeSet;

use prism_common::sym::Sym;

use crate::core::cbpv::{Comp, Core, CoreFn, ElaboratedCore, LoweredCore, Value};
use crate::core::fv;
use crate::core::traverse::Visit;

use super::PassStage;

impl ElaboratedCore {
    /// Validate a pre-effect-lowering program and mint its stage claim.
    ///
    /// This is the only public construction path. It rejects runtime nodes,
    /// unbound variables, and invalid reuse scopes before returning the wrapper.
    ///
    /// # Errors
    /// One message per structural violation, as the stage lint reports them.
    pub fn validate(core: Core) -> Result<Self, Vec<String>> {
        lint(&core, PassStage::PreLowering)?;
        Ok(Self::new(core))
    }

    /// Append synthesized top-level functions and revalidate the whole program.
    /// Consuming `self` prevents a caller from retaining a validated wrapper while
    /// mutating its contents behind the stage claim.
    ///
    /// # Errors
    /// One message per structural violation after the functions are appended.
    pub fn with_functions(
        self,
        functions: impl IntoIterator<Item = CoreFn>,
    ) -> Result<Self, Vec<String>> {
        let mut core = self.into_core();
        core.fns.extend(functions);
        Self::validate(core)
    }
}

impl LoweredCore {
    /// Structural stage validation, lint-grade: the checked public constructor
    /// for a lowered program an external producer hands to the backends.
    ///
    /// It establishes exactly what the pipeline's own stage lint enforces at
    /// this boundary: no pre-lowering effect node remains, every variable is
    /// bound, and no reuse token is spent twice on a path. It is NOT typed
    /// verification: no type, effect, handler, or ownership witness is checked,
    /// and a structurally valid program can still be semantically wrong. The
    /// pipeline's own product carries the stronger, verified claim.
    ///
    /// # Errors
    /// One message per structural violation, as the stage lint reports them.
    pub fn validate(core: Core) -> Result<Self, Vec<String>> {
        lint(&core, PassStage::Late)?;
        Ok(Self::new(core))
    }

    /// Backward-compatible spelling for the checked lowered-stage transition.
    ///
    /// # Errors
    /// One message per structural violation, as the stage lint reports them.
    pub fn validate_structural(core: Core) -> Result<Self, Vec<String>> {
        Self::validate(core)
    }
}

/// Lint `core` at pipeline `stage`, returning one message per violation.
/// `Ok(())` means well-formed.
///
/// The stage decides which of the two node families is legal: pre-lowering Core
/// must carry no runtime node (`Dup`, `Drop`, reuse, local cells) because effect
/// lowering has not run yet, and post-lowering Core must carry no effect node
/// (`Do`, `Handle`, `Mask`) because lowering eliminates every one. A node from
/// the wrong family is a pass constructing ill-formed Core, the residual bug the
/// stage newtypes at the pipeline seams cannot catch (they gate whole-program
/// routing, not the nodes inside a tree).
///
/// # Examples
///
/// A single function returning a literal is well-formed at the elaborated
/// (pre-lowering) stage:
///
/// ```
/// use prism_core::core::{lint_core, Comp, Core, CoreFn, PassStage, Value};
/// use prism_common::sym::Sym;
///
/// // fn main = return 42
/// let prog = Core {
///     fns: vec![CoreFn {
///         name: Sym::new("main"),
///         params: vec![],
///         body: Comp::Return(Value::Int(42)),
///         dict_arity: 0,
///     }],
/// };
/// assert!(lint_core(&prog, PassStage::PreLowering).is_ok());
/// ```
///
/// A reference-counting node is legal only after effect lowering, so linting a
/// program that carries one at the pre-lowering stage is an error:
///
/// ```
/// use prism_core::core::{lint_core, Comp, Core, CoreFn, PassStage, Value};
/// use prism_common::sym::Sym;
///
/// let bad = Core {
///     fns: vec![CoreFn {
///         name: Sym::new("main"),
///         params: vec![],
///         body: Comp::Dup(Value::Int(1)), // a runtime node, illegal pre-lowering
///         dict_arity: 0,
///     }],
/// };
/// let errs = lint_core(&bad, PassStage::PreLowering).unwrap_err();
/// assert!(errs[0].contains("runtime node"));
/// ```
///
/// # Errors
/// Returns the list of well-formedness violations (a wrong-stage node, an
/// out-of-scope free variable, or a reuse token spent more than once on a path),
/// one message per violation.
pub fn lint(core: &Core, stage: PassStage) -> Result<(), Vec<String>> {
    let top: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    let mut errs = Vec::new();
    for f in &core.fns {
        let mut allowed = top.clone();
        allowed.extend(f.params.iter().copied());
        for v in fv::comp(&f.body) {
            if !allowed.contains(&v) {
                errs.push(format!(
                    "fn `{}`: unbound variable `{}` (escaped binder or dangling reference)",
                    f.name, v
                ));
            }
        }
        let mut rl = ReuseLint {
            fname: f.name,
            errs: Vec::new(),
        };
        rl.walk_comp(&f.body);
        errs.append(&mut rl.errs);
        let mut sl = StageLint {
            fname: f.name,
            stage,
            errs: Vec::new(),
        };
        sl.walk_comp(&f.body);
        errs.append(&mut sl.errs);
    }
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

// Flags any node belonging to the family the stage forbids: runtime nodes before
// lowering, effect nodes after it. The two families are defined once on `Comp`
// (`is_effect_node` / `is_runtime_node`), so a new node in either family is
// classified there and this walk needs no edit.
struct StageLint {
    fname: Sym,
    stage: PassStage,
    errs: Vec<String>,
}

impl Visit for StageLint {
    fn comp(&mut self, c: &Comp) -> bool {
        let forbidden = match self.stage {
            PassStage::PreLowering => c.is_runtime_node(),
            PassStage::Late => c.is_effect_node(),
        };
        if forbidden {
            let (banned, expected) = match self.stage {
                PassStage::PreLowering => ("runtime", "before effect lowering"),
                PassStage::Late => ("effect", "after effect lowering"),
            };
            self.errs.push(format!(
                "fn `{}`: {banned} node `{}` is illegal {expected}",
                self.fname,
                c.kind()
            ));
        }
        true
    }
}

// Visits every `WithReuse` and checks its token is spent at most once on any
// path through its body.
struct ReuseLint {
    fname: Sym,
    errs: Vec<String>,
}

impl Visit for ReuseLint {
    fn comp(&mut self, c: &Comp) -> bool {
        if let Comp::WithReuse { token, body, .. } = c {
            let n = spends(*token, body);
            if n > 1 {
                self.errs.push(format!(
                    "fn `{}`: reuse token `{token}` spent {n} times on one path \
                     (must be at most once; double in-place write)",
                    self.fname
                ));
            }
        }
        true
    }
}

// Spends of `token` along the worst-case single execution path: sequential
// composition adds (both run), branches take the max (one arm runs). A nested
// `WithReuse` rebinding the same name shadows it, so its body is not counted.
fn spends(token: Sym, c: &Comp) -> usize {
    let mut work = vec![SpendFrame::Comp(c)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            SpendFrame::Comp(comp) => push_spend_comp(&mut work, token, comp),
            SpendFrame::Value(value) => push_spend_value(&mut work, value),
            SpendFrame::Sum { children, base } => {
                let children = pop_sum(&mut results, children);
                results.push(base + children);
            }
            SpendFrame::Branch { arms } => {
                let worst_arm = pop_max(&mut results, arms);
                let scrutinee = results.pop().expect("branch scrutinee result");
                results.push(scrutinee + worst_arm);
            }
        }
    }
    results.pop().expect("reuse-spend result")
}

enum SpendFrame<'a> {
    Comp(&'a Comp),
    Value(&'a Value),
    Sum { children: usize, base: usize },
    Branch { arms: usize },
}

fn push_sum<'a>(
    work: &mut Vec<SpendFrame<'a>>,
    values: impl DoubleEndedIterator<Item = &'a Value> + ExactSizeIterator,
) {
    work.push(SpendFrame::Sum {
        children: values.len(),
        base: 0,
    });
    work.extend(values.rev().map(SpendFrame::Value));
}

fn push_spend_comp<'a>(work: &mut Vec<SpendFrame<'a>>, token: Sym, comp: &'a Comp) {
    match comp {
        Comp::Reuse(spent, value) => {
            work.push(SpendFrame::Sum {
                children: 1,
                base: usize::from(*spent == token),
            });
            work.push(SpendFrame::Value(value));
        }
        Comp::InitAt(cell, value) | Comp::Prim(_, cell, value) | Comp::RefSet(cell, value) => {
            work.push(SpendFrame::Sum {
                children: 2,
                base: 0,
            });
            work.push(SpendFrame::Value(value));
            work.push(SpendFrame::Value(cell));
        }
        Comp::Bind(first, _, rest) => {
            work.push(SpendFrame::Sum {
                children: 2,
                base: 0,
            });
            work.push(SpendFrame::Comp(rest));
            work.push(SpendFrame::Comp(first));
        }
        Comp::If(condition, yes, no) => {
            work.push(SpendFrame::Branch { arms: 2 });
            work.push(SpendFrame::Comp(no));
            work.push(SpendFrame::Comp(yes));
            work.push(SpendFrame::Value(condition));
        }
        Comp::Case(scrutinee, arms) => {
            work.push(SpendFrame::Branch { arms: arms.len() });
            for (_, body) in arms.iter().rev() {
                work.push(SpendFrame::Comp(body));
            }
            work.push(SpendFrame::Value(scrutinee));
        }
        Comp::App(callee, args) => {
            work.push(SpendFrame::Sum {
                children: args.len() + 1,
                base: 0,
            });
            for argument in args.iter().rev() {
                work.push(SpendFrame::Value(argument));
            }
            work.push(SpendFrame::Comp(callee));
        }
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            push_sum(work, args.iter());
        }
        Comp::Return(value)
        | Comp::Force(value)
        | Comp::Error(value)
        | Comp::FloatBuiltin(_, value)
        | Comp::Neg(_, value)
        | Comp::UnboxedProject(value, _)
        | Comp::Dup(value)
        | Comp::Drop(value)
        | Comp::RefNew(value)
        | Comp::RefGet(value) => work.push(SpendFrame::Value(value)),
        Comp::Lam(_, body) | Comp::Mask(_, body) => work.push(SpendFrame::Comp(body)),
        Comp::WithReuse {
            token: inner,
            freed,
            body,
        } => {
            work.push(SpendFrame::Sum {
                children: usize::from(*inner != token) + 1,
                base: 0,
            });
            if *inner != token {
                work.push(SpendFrame::Comp(body));
            }
            work.push(SpendFrame::Value(freed));
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            work.push(SpendFrame::Sum {
                children: 1 + usize::from(return_body.is_some()) + ops.len(),
                base: 0,
            });
            for operation in ops.iter().rev() {
                work.push(SpendFrame::Comp(&operation.body));
            }
            if let Some(return_body) = return_body {
                work.push(SpendFrame::Comp(return_body));
            }
            work.push(SpendFrame::Comp(body));
        }
    }
}

fn push_spend_value<'a>(work: &mut Vec<SpendFrame<'a>>, value: &'a Value) {
    match value {
        Value::Thunk(body) => work.push(SpendFrame::Comp(body)),
        Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
            push_sum(work, fields.iter());
        }
        Value::UnboxedRecord(fields) => push_sum(work, fields.iter().map(|(_, field)| field)),
        Value::Var(_)
        | Value::Int(_)
        | Value::I64(_)
        | Value::U64(_)
        | Value::Float(_)
        | Value::Bool(_)
        | Value::Unit
        | Value::Str(_) => work.push(SpendFrame::Sum {
            children: 0,
            base: 0,
        }),
    }
}

fn pop_sum(results: &mut Vec<usize>, count: usize) -> usize {
    (0..count)
        .map(|_| results.pop().expect("reuse-spend child result"))
        .sum()
}

fn pop_max(results: &mut Vec<usize>, count: usize) -> usize {
    (0..count)
        .map(|_| results.pop().expect("reuse-spend branch result"))
        .max()
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;

    const DEEP_BIND_COUNT: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    #[test]
    fn lint_handles_deep_reuse_spines_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-core-lint".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let token = Sym::new("reuse_token");
                let mut body = Comp::Reuse(token, Value::Ctor("Cell".into(), 0, Vec::new()));
                for _ in 0..DEEP_BIND_COUNT {
                    body = Comp::Bind(
                        Box::new(Comp::Return(Value::Int(0))),
                        Sym::new("_"),
                        Box::new(body),
                    );
                }
                let core = program(Comp::WithReuse {
                    token,
                    freed: Value::Int(0),
                    body: Box::new(body),
                });

                assert_eq!(lint(&core, PassStage::Late), Ok(()));
                mem::forget(core);
            })
            .expect("spawn deep Core Lint test")
            .join()
            .expect("deep Core Lint test panicked");
    }

    #[test]
    fn reuse_spends_add_sequences_take_branch_maxima_and_respect_shadowing() {
        let token = Sym::new("token");
        let spend = || Comp::Reuse(token, Value::Unit);
        let sequence = Comp::Bind(Box::new(spend()), Sym::new("_"), Box::new(spend()));
        let branch = Comp::If(
            Value::Thunk(Box::new(spend())),
            Box::new(sequence),
            Box::new(spend()),
        );
        assert_eq!(spends(token, &branch), 3);

        let shadow = Comp::WithReuse {
            token,
            freed: Value::Thunk(Box::new(spend())),
            body: Box::new(spend()),
        };
        assert_eq!(spends(token, &shadow), 1);
    }

    fn program(body: Comp) -> Core {
        Core {
            fns: vec![CoreFn {
                name: Sym::new("main"),
                params: Vec::new(),
                body,
                dict_arity: 0,
            }],
        }
    }

    #[test]
    fn checked_stage_doors_reject_the_other_nodes() {
        assert!(ElaboratedCore::validate(program(Comp::Return(Value::Int(1)))).is_ok());
        assert!(ElaboratedCore::validate(program(Comp::Dup(Value::Int(1)))).is_err());
        assert!(LoweredCore::validate(program(Comp::Do(Sym::new("read"), Vec::new()))).is_err());
    }

    #[test]
    fn appending_functions_revalidates_the_stage_claim() {
        let core = ElaboratedCore::validate(program(Comp::Return(Value::Int(1))))
            .expect("plain elaborated core");
        let invalid = CoreFn {
            name: Sym::new("late"),
            params: Vec::new(),
            body: Comp::Drop(Value::Int(1)),
            dict_arity: 0,
        };
        assert!(core.with_functions([invalid]).is_err());
    }
}
