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
//! Richer checks (constructor arity against the ctor table, ANF argument shape)
//! are future additions; the harness is built to grow them.

use std::collections::BTreeSet;

use super::super::cbpv::{Comp, Core, Value};
use super::super::fv;
use super::super::traverse::Visit;
use super::PassStage;
use crate::sym::Sym;

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
/// use prism::core::{lint_core, Comp, Core, CoreFn, PassStage, Value};
/// use prism::sym::Sym;
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
/// use prism::core::{lint_core, Comp, Core, CoreFn, PassStage, Value};
/// use prism::sym::Sym;
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
        rl.visit_comp(&f.body);
        errs.append(&mut rl.errs);
        let mut sl = StageLint {
            fname: f.name,
            stage,
            errs: Vec::new(),
        };
        sl.visit_comp(&f.body);
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
    fn visit_comp(&mut self, c: &Comp) {
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
        self.descend_comp(c);
    }
}

// Visits every `WithReuse` and checks its token is spent at most once on any
// path through its body.
struct ReuseLint {
    fname: Sym,
    errs: Vec<String>,
}

impl Visit for ReuseLint {
    fn visit_comp(&mut self, c: &Comp) {
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
        self.descend_comp(c);
    }
}

// Spends of `token` along the worst-case single execution path: sequential
// composition adds (both run), branches take the max (one arm runs). A nested
// `WithReuse` rebinding the same name shadows it, so its body is not counted.
fn spends(token: Sym, c: &Comp) -> usize {
    match c {
        Comp::Reuse(t, v) => usize::from(*t == token) + spends_val(token, v),
        Comp::Bind(m, _, n) => spends(token, m) + spends(token, n),
        Comp::If(v, t, e) => spends_val(token, v) + spends(token, t).max(spends(token, e)),
        Comp::Case(v, arms) => {
            spends_val(token, v)
                + arms
                    .iter()
                    .map(|(_, b)| spends(token, b))
                    .max()
                    .unwrap_or(0)
        }
        Comp::App(f, args) => {
            spends(token, f) + args.iter().map(|a| spends_val(token, a)).sum::<usize>()
        }
        Comp::Prim(_, a, b) | Comp::RefSet(a, b) => spends_val(token, a) + spends_val(token, b),
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            args.iter().map(|a| spends_val(token, a)).sum()
        }
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => spends_val(token, v),
        Comp::Lam(_, b) | Comp::Mask(_, b) => spends(token, b),
        Comp::WithReuse {
            token: t2,
            freed,
            body,
        } => spends_val(token, freed) + if *t2 == token { 0 } else { spends(token, body) },
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            spends(token, body)
                + return_body.as_ref().map_or(0, |b| spends(token, b))
                + ops.iter().map(|op| spends(token, &op.body)).sum::<usize>()
        }
    }
}

fn spends_val(token: Sym, v: &Value) -> usize {
    match v {
        Value::Thunk(c) => spends(token, c),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().map(|f| spends_val(token, f)).sum(),
        _ => 0,
    }
}
