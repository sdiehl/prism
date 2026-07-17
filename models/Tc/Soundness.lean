import Tc.Algorithm

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Prism
namespace Tc

/-!
Low- and mid-level proof obligations for a Prism typechecker soundness project.

These are intentionally theorem signatures first. The goal is to make the shape
of the proof reviewable before anyone attempts the proofs.
-/

theorem canonicalRow_nodup (labels : List (String × List Ty)) (tail : Row) :
    NoDupLabels (canonicalRow labels tail) := by
  /-
  This obligation is isolated because canonical-row normalization and tail
  preservation meet here.
  -/
  sorry

theorem canonicalRow_mem_iff (labels : List (String × List Ty)) (tail : Row)
    (label : String × List Ty) :
    label ∈ rowLabels (canonicalRow labels tail) ↔
      label ∈ labels ∨ label ∈ rowLabels tail := by
  sorry

theorem canonicalRow_tail (labels : List (String × List Ty)) (tail : Row) :
    rowTail (canonicalRow labels tail) = rowTail tail := by
  sorry

theorem inferKind_sound (Γ : KindEnv) (τ : Ty) (κ : Kind) :
    inferKind Γ τ = Except.ok κ →
    HasKind Γ τ κ := by
  sorry

theorem checkKind_sound (Γ : KindEnv) (τ : Ty) (κ : Kind) :
    checkKind Γ τ κ = Except.ok () →
    HasKind Γ τ κ := by
  sorry

theorem checkRow_sound (Γ : KindEnv) (ρ : Row) :
    checkRow Γ ρ = Except.ok () →
    RowWF Γ ρ := by
  sorry

theorem applyTy_preserves_kinding (Γ : KindEnv) (σ : Subst) (τ : Ty) (κ : Kind) :
    HasKind Γ τ κ →
    HasKind Γ (applyTy σ τ) κ := by
  sorry

theorem applyRow_preserves_wf (Γ : KindEnv) (σ : Subst) (ρ : Row) :
    RowWF Γ ρ →
    RowWF Γ (applyRow σ ρ) := by
  sorry

theorem applyTy_idempotent_after_zonk (σ : Subst) (τ : Ty) :
    applyTy σ (applyTy σ τ) = applyTy σ τ := by
  sorry

theorem applyRow_idempotent_after_zonk (σ : Subst) (ρ : Row) :
    applyRow σ (applyRow σ ρ) = applyRow σ ρ := by
  sorry

theorem unify_sound (τ υ : Ty) (σ : Subst) :
    unify τ υ = Except.ok σ →
    TyEq (applyTy σ τ) (applyTy σ υ) := by
  sorry

theorem unifyRow_sound (ρ₁ ρ₂ : Row) (σ : Subst) :
    unifyRow ρ₁ ρ₂ = Except.ok σ →
    RowEq (applyRow σ ρ₁) (applyRow σ ρ₂) := by
  sorry

theorem inferExpr_sound (Γ : TermEnv) (e : Expr) (τ : Ty) (eff : Row) :
    inferExpr Γ e = Except.ok (τ, eff) →
    HasType Γ e τ eff := by
  sorry

/-!
Subsystem obligations corresponding to the Rust `src/tc` modules. These use
abstract predicates rather than judgments over the resolved/desugared Prism AST
and the corresponding `Checked` side table.
-/

inductive DeclsWellTyped : Program → Checked → Prop where
  | assumed : DeclsWellTyped p c

inductive ClassesCoherent : Program → Checked → Prop where
  | assumed : ClassesCoherent p c

inductive DictionariesValid : Program → Checked → Prop where
  | assumed : DictionariesValid p c

inductive PatternsSound : Program → Checked → Prop where
  | assumed : PatternsSound p c

inductive EffectsSound : Program → Checked → Prop where
  | assumed : EffectsSound p c

inductive HandlerGradesSound : Program → Checked → Prop where
  | assumed : HandlerGradesSound p c

inductive SideTablesValid : Program → Checked → Prop where
  | assumed : SideTablesValid p c

theorem declaration_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c := by
  sorry

theorem class_resolution_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c ∧ DictionariesValid p c := by
  sorry

theorem pattern_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    PatternsSound p c := by
  sorry

theorem effect_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    EffectsSound p c ∧ HandlerGradesSound p c := by
  sorry

theorem checked_side_tables_valid (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c →
    DictionariesValid p c →
    PatternsSound p c →
    EffectsSound p c →
    HandlerGradesSound p c →
    SideTablesValid p c := by
  sorry

theorem checked_valid_from_subsystems (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c →
    DictionariesValid p c →
    PatternsSound p c →
    EffectsSound p c →
    HandlerGradesSound p c →
    SideTablesValid p c →
    CheckedValid p c := by
  sorry

theorem lean_typechecker_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c →
    DictionariesValid p c →
    PatternsSound p c →
    EffectsSound p c →
    HandlerGradesSound p c →
    SideTablesValid p c →
    ProgramWellTyped p c := by
  intro hInput hDecls hClasses hDicts hPatterns hEffects hGrades hSide
  exact ProgramWellTyped.checked hInput
    (checked_valid_from_subsystems p c hInput hDecls hClasses hDicts hPatterns hEffects hGrades hSide)

end Tc
end Prism
