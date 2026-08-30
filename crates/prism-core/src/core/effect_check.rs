//! Post-lowering erased-Core effect invariants.

use super::cbpv::{Comp, Core};
use super::traverse::Visit;

// The raw effect node names, shared with the reuse linearity check so its
// refusal names an unlowered node the same way this check does.
pub const DO_NODE: &str = "do";
pub const HANDLE_NODE: &str = "handle";
pub const MASK_NODE: &str = "mask";

/// Reject any raw `do`, `handle`, or `mask` node that survives typed effect
/// lowering and erasure.
///
/// # Errors
/// A message naming the first function that still carries such a node.
pub fn residual_effects(core: &Core) -> Result<(), String> {
    for function in &core.fns {
        if residual_effect_node(&function.body).is_some() {
            return Err(format!(
                "residual effect in `{}` after lowering",
                function.name
            ));
        }
    }
    Ok(())
}

/// The first raw effect node in the computation, including nested values.
#[must_use]
pub fn residual_effect_node(comp: &Comp) -> Option<&'static str> {
    let mut finder = EffectNodeFinder { found: None };
    finder.visit_comp(comp);
    finder.found
}

struct EffectNodeFinder {
    found: Option<&'static str>,
}

impl Visit for EffectNodeFinder {
    fn visit_comp(&mut self, c: &Comp) {
        if self.found.is_some() {
            return;
        }
        match c {
            Comp::Do(..) => self.found = Some(DO_NODE),
            Comp::Handle { .. } => self.found = Some(HANDLE_NODE),
            Comp::Mask(..) => self.found = Some(MASK_NODE),
            _ => self.descend_comp(c),
        }
    }
}
