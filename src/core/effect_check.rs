//! Post-lowering erased-Core effect invariants.

use super::cbpv::{Comp, Core, Value};

/// Reject any raw `do`, `handle`, or `mask` node that survives typed effect
/// lowering and erasure.
pub(crate) fn residual_effects(core: &Core) -> Result<(), String> {
    for function in &core.fns {
        if raw_effects(&function.body) {
            return Err(format!(
                "residual effect in `{}` after lowering",
                function.name
            ));
        }
    }
    Ok(())
}

fn raw_effects(comp: &Comp) -> bool {
    if matches!(comp, Comp::Do(..) | Comp::Handle { .. } | Comp::Mask(..)) {
        return true;
    }
    match comp {
        Comp::Return(value)
        | Comp::Force(value)
        | Comp::Error(value)
        | Comp::FloatBuiltin(_, value)
        | Comp::Neg(_, value)
        | Comp::Dup(value)
        | Comp::Drop(value)
        | Comp::Reuse(_, value)
        | Comp::RefNew(value)
        | Comp::RefGet(value)
        | Comp::UnboxedProject(value, _) => raw_effects_value(value),
        Comp::WithReuse { freed, body, .. } => raw_effects_value(freed) || raw_effects(body),
        Comp::Prim(_, left, right) | Comp::RefSet(left, right) | Comp::InitAt(left, right) => {
            raw_effects_value(left) || raw_effects_value(right)
        }
        Comp::App(function, args) => raw_effects(function) || args.iter().any(raw_effects_value),
        Comp::Call(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            args.iter().any(raw_effects_value)
        }
        Comp::Bind(bound, _, body) => raw_effects(bound) || raw_effects(body),
        Comp::Lam(_, body) => raw_effects(body),
        Comp::If(value, then_branch, else_branch) => {
            raw_effects_value(value) || raw_effects(then_branch) || raw_effects(else_branch)
        }
        Comp::Case(value, arms) => {
            raw_effects_value(value) || arms.iter().any(|(_, body)| raw_effects(body))
        }
        Comp::Do(..) | Comp::Mask(..) | Comp::Handle { .. } => true,
    }
}

fn raw_effects_value(value: &Value) -> bool {
    match value {
        Value::Thunk(comp) => raw_effects(comp),
        Value::Ctor(_, _, fields) | Value::Tuple(fields) => fields.iter().any(raw_effects_value),
        _ => false,
    }
}
