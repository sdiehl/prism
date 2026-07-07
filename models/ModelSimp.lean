import Lean

/-
Shared Lean attributes for the model proofs. Keeping these in their own module
lets later files use the attributes without fighting Lean's same-file attribute
rules.
-/

register_simp_attr prism_model
register_grind_attr prism_grind
