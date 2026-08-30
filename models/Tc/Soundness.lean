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

/-- A row's terminal carries no labels: `rowTail` recurses past every
`extend`, and the three terminal constructors all have empty label lists. -/
theorem rowLabels_rowTail : (r : Row) → rowLabels (rowTail r) = []
  | .empty => rfl
  | .var _ => rfl
  | .exist _ => rfl
  | .extend _ _ rest => rowLabels_rowTail rest

theorem rowTail_rowTail : (r : Row) → rowTail (rowTail r) = rowTail r
  | .empty => rfl
  | .var _ => rfl
  | .exist _ => rfl
  | .extend _ _ rest => rowTail_rowTail rest

/-- Folding a label list over a row prepends exactly that list to its labels. -/
theorem rowLabels_foldr (ls : List (String × List Ty)) (r : Row) :
    rowLabels (ls.foldr (fun label acc => .extend label.fst label.snd acc) r) =
      ls ++ rowLabels r := by
  induction ls with
  | nil => rfl
  | cons l rest ih => simp [rowLabels, ih]

/-- Folding labels over a row cannot change which terminal it ends in. -/
theorem rowTail_foldr (ls : List (String × List Ty)) (r : Row) :
    rowTail (ls.foldr (fun label acc => .extend label.fst label.snd acc) r) =
      rowTail r := by
  induction ls with
  | nil => rfl
  | cons l rest ih => simp [rowTail, ih]

/-- The canonical form is sorted by key. Rows are multisets, so the invariant is
sorted-by-key with repeats permitted (the former no-duplicate law does not hold
once `mask<E>` can repeat a label). -/
theorem labelLe_trans (a b c : String × List Ty) :
    labelLe a b = true → labelLe b c = true → labelLe a c = true := by
  simp only [labelLe, decide_eq_true_eq]
  exact String.le_trans

theorem labelLe_total (a b : String × List Ty) :
    (labelLe a b || labelLe b a) = true := by
  simp only [labelLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total (labelKey a) (labelKey b)

theorem canonicalRow_sorted (labels : List (String × List Ty)) (tail : Row) :
    SortedLabels (canonicalRow labels tail) := by
  have hs :=
    List.pairwise_mergeSort labelLe_trans labelLe_total (labels ++ rowLabels tail)
  unfold SortedLabels canonicalRow
  rw [rowLabels_foldr, rowLabels_rowTail, List.append_nil]
  exact hs.imp fun h => of_decide_eq_true h

theorem canonicalRow_mem_iff (labels : List (String × List Ty)) (tail : Row)
    (label : String × List Ty) :
    label ∈ rowLabels (canonicalRow labels tail) ↔
      label ∈ labels ∨ label ∈ rowLabels tail := by
  simp [canonicalRow, rowLabels_foldr, rowLabels_rowTail, List.mem_mergeSort]

/-- `mask<E>` adds exactly one copy of `E` to the body's row: the count of the
masked label rises by one, and every other label is untouched. This is the
multiset heart of scoped effect labels; under the old set semantics the mask over
a body already performing `E` would be absorbed, and the extra handler obligation
would be lost. -/
theorem maskRow_prepends (name : String) (args : List Ty) (r : Row) :
    rowLabels (maskRow name args r) = (name, args) :: rowLabels r := by
  rfl

theorem maskRow_tail (name : String) (args : List Ty) (r : Row) :
    rowTail (maskRow name args r) = rowTail r := by
  rfl

theorem canonicalRow_tail (labels : List (String × List Ty)) (tail : Row) :
    rowTail (canonicalRow labels tail) = rowTail tail := by
  simp [canonicalRow, rowTail_foldr, rowTail_rowTail]

/-- Inversion for a successful `Except` bind: both halves must have succeeded.
The kinding algorithm is written in `do` notation over `TcM`, so every case
analysis below starts by peeling binds with this. -/
private theorem bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = Except.ok b) : ∃ a, m = Except.ok a ∧ f a = Except.ok b := by
  cases hm : m with
  | error e => rw [hm] at h; simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by rw [hm] at h; exact h⟩

/-- Inversion for a successful `*>`, the shape `inferKind` uses on `.row`. -/
private theorem seqRight_ok {ε α β : Type} {m : Except ε α} {n : Except ε β} {b : β}
    (h : (m *> n) = Except.ok b) : n = Except.ok b := by
  cases hm : m with
  | error e => rw [hm] at h; simp [SeqRight.seqRight, Except.bind] at h
  | ok a => rw [hm] at h; exact h

/-- Inversion for the `for x in xs do ...` loops of `inferKind`/`checkRow`: a
loop that ran to completion checked every element. `for` over a `List` in a
monad desugars to `forIn`, so the statement is about `forIn` rather than about
an explicit fold. -/
private theorem forIn_unit_ok {α : Type} {f : α → TcM Unit} :
    ∀ (xs : List α) (u : Unit),
      (forIn xs PUnit.unit
          (fun x _ => do f x; pure (ForInStep.yield PUnit.unit)) : TcM Unit)
          = Except.ok u →
      ∀ x ∈ xs, f x = Except.ok () := by
  intro xs
  induction xs with
  | nil => intro _ _ x hx; cases hx
  | cons a t ih =>
    intro u h x hx
    simp only [List.forIn_cons] at h
    cases hc : f a with
    | error e => rw [hc] at h; simp [bind, Except.bind] at h
    | ok v =>
      rw [hc] at h
      cases v
      cases hx with
      | head => exact hc
      | tail _ hmem => exact ih u h x hmem

/-!
Kind soundness. The three theorems mirror the mutual recursion of
`inferKind`/`checkKind`/`checkRow`, so they are proved as one mutual block:
`checkKind` calls `inferKind` at the same type, `inferKind` calls `checkKind`
and `checkRow` at strict subterms, and `checkRow` calls `checkKind` at the
argument types it carries. The `.con` and `.exist` arms of `inferKind` throw,
so those cases are vacuous rather than proved.
-/

mutual

theorem inferKind_sound (Γ : KindEnv) (τ : Ty) (κ : Kind) :
    inferKind Γ τ = Except.ok κ →
    HasKind Γ τ κ := by
  intro h
  cases τ with
  | unit => rw [inferKind] at h; injection h with h; subst h; exact .unit
  | int => rw [inferKind] at h; injection h with h; subst h; exact .int
  | i64 => rw [inferKind] at h; injection h with h; subst h; exact .i64
  | u64 => rw [inferKind] at h; injection h with h; subst h; exact .u64
  | bool => rw [inferKind] at h; injection h with h; subst h; exact .bool
  | float => rw [inferKind] at h; injection h with h; subst h; exact .float
  | char => rw [inferKind] at h; injection h with h; subst h; exact .char
  | str => rw [inferKind] at h; injection h with h; subst h; exact .str
  | nat n => rw [inferKind] at h; injection h with h; subst h; exact .natLit
  | var x =>
      rw [inferKind] at h
      split at h
      · next k hl => injection h with h; subst h; exact .var hl
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | exist n =>
      rw [inferKind] at h
      exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | con c args =>
      rw [inferKind] at h
      exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | row r =>
      rw [inferKind] at h
      have hκ := seqRight_ok h
      injection hκ with hκ
      subst hκ
      refine .row (checkRow_sound Γ r ?_)
      cases hr : checkRow Γ r with
      | ok u => cases u; rfl
      | error e => rw [hr] at h; simp [SeqRight.seqRight, Except.bind] at h
  | «fun» ps eff ret =>
      rw [inferKind] at h
      obtain ⟨u1, h1, h⟩ := bind_ok h
      obtain ⟨u2, h2, h⟩ := bind_ok h
      obtain ⟨u3, h3, h⟩ := bind_ok h
      injection h with h
      subst h
      exact .fun (fun t ht => checkKind_sound Γ t .type (forIn_unit_ok ps u1 h1 t ht))
        (checkRow_sound Γ eff (by cases u2; exact h2))
        (checkKind_sound Γ ret .type (by cases u3; exact h3))
  | tuple fields =>
      rw [inferKind] at h
      obtain ⟨u1, h1, h⟩ := bind_ok h
      injection h with h
      subst h
      exact .tuple fun t ht => checkKind_sound Γ t .type (forIn_unit_ok fields u1 h1 t ht)
  | forallE x body =>
      rw [inferKind] at h
      obtain ⟨u1, h1, h⟩ := bind_ok h
      injection h with h
      subst h
      exact .forallE (checkKind_sound ((x, .type) :: Γ) body .type (by cases u1; exact h1))
  | rowForall x body =>
      rw [inferKind] at h
      obtain ⟨u1, h1, h⟩ := bind_ok h
      injection h with h
      subst h
      exact .rowForall (checkKind_sound ((x, .row) :: Γ) body .type (by cases u1; exact h1))
  | app f x =>
      rw [inferKind] at h
      obtain ⟨kf, hkf, h⟩ := bind_ok h
      split at h
      · next dom cod =>
          obtain ⟨u1, h1, h⟩ := bind_ok h
          injection h with h
          subst h
          exact .app (inferKind_sound Γ f (.fun dom cod) hkf)
            (checkKind_sound Γ x dom (by cases u1; exact h1))
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

theorem checkKind_sound (Γ : KindEnv) (τ : Ty) (κ : Kind) :
    checkKind Γ τ κ = Except.ok () →
    HasKind Γ τ κ := by
  intro h
  rw [checkKind] at h
  obtain ⟨got, hgot, h⟩ := bind_ok h
  split at h
  · next heq => subst heq; exact inferKind_sound Γ τ got hgot
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

theorem checkRow_sound (Γ : KindEnv) (ρ : Row) :
    checkRow Γ ρ = Except.ok () →
    RowWF Γ ρ := by
  intro h
  cases ρ with
  | empty => exact .empty
  | exist n => exact .exist
  | var x =>
      rw [checkRow] at h
      split at h
      · next hl => exact .var hl
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | extend name args rest =>
      rw [checkRow] at h
      obtain ⟨u1, h1, h2⟩ := bind_ok h
      exact .extend (fun t ht => checkKind_sound Γ t .type (forIn_unit_ok args u1 h1 t ht))
        (checkRow_sound Γ rest h2)

end

/-- The well-formedness a substitution must carry for preservation to hold:
every row it can introduce is itself well formed, and stays well formed under
every extension of the environment.

Well formedness in `Γ` alone is not enough. Taking `Δ = []` recovers it, and
without that much the theorem is false, e.g. `σ.row 0 ↦ .var "x"` under
`Γ = []` rewrites the well-formed `.exist 0` (unconditionally WF) to an unbound
row variable. Quantifying over every prefix `Δ` is what the binder cases need:
`applyTy` is capture-unaware, so under `Γ = [("e", .row)]` and
`σ.row 0 ↦ .var "e"` the well-kinded `.forallE "e" (.fun [] (.exist 0) .unit)`
becomes `.forallE "e" (.fun [] (.var "e") .unit)`, whose `"e"` now resolves to
the `.type`-kinded binder and is no longer a well-formed row. Stability under
extension rules that substitution out, and it is exactly what `.forallE` and
`.rowForall` consume when they push a binder onto `Γ`.

No clause for `σ.ty` is needed: `HasKind` has no rule for `Ty.exist`, so a
kinded type cannot contain a type existential for `applyTy` to replace, whereas
`RowWF.exist` is unconditional and row existentials do occur inside well-formed
types. -/
def SubstWF (Γ : KindEnv) (σ : Subst) : Prop :=
  ∀ n r, σ.row n = some r → ∀ Δ : KindEnv, RowWF (Δ ++ Γ) r

/-- A zonked substitution: solved entries contain no further solvable
existentials, i.e. the substitution is a fixpoint on its own images. Without
this hypothesis idempotence is false, e.g. `σ.ty 0 ↦ .exist 1, σ.ty 1 ↦ .int`
sends `.exist 0` to `.exist 1` on the first pass and to `.int` on the second. -/
def Zonked (σ : Subst) : Prop :=
  (∀ n t, σ.ty n = some t → applyTy σ t = t) ∧
    (∀ n r, σ.row n = some r → applyRow σ r = r)

/-- The `Δ = []` instance: a substituted row is well formed in `Γ` itself. -/
private theorem SubstWF.here {Γ : KindEnv} {σ : Subst} {n : Nat} {r : Row}
    (h : SubstWF Γ σ) (hr : σ.row n = some r) : RowWF Γ r :=
  h n r hr []

/-- `SubstWF` is stable under pushing a binder, which is what the `.forallE`
and `.rowForall` cases of the preservation proof need. -/
private theorem SubstWF.push {Γ : KindEnv} {σ : Subst} (h : SubstWF Γ σ)
    (b : String × Kind) : SubstWF (b :: Γ) σ := by
  intro n r hr Δ
  have hx := h n r hr (Δ ++ [b])
  rwa [List.append_assoc] at hx

/-!
Preservation of kinding under substitution. `HasKind`, `RowWF` and
`SpineHasKind` are one mutual family, so the induction on the derivation needs
all three motives; the spine companion is where `applyTy` mapped over a `.con`
argument list is discharged.
-/

mutual

private theorem applyTy_kind {Γ : KindEnv} {σ : Subst} {τ : Ty} {κ : Kind}
    (hσ : SubstWF Γ σ) (h : HasKind Γ τ κ) : HasKind Γ (applyTy σ τ) κ := by
  cases h with
  | unit => simp only [applyTy]; exact .unit
  | int => simp only [applyTy]; exact .int
  | i64 => simp only [applyTy]; exact .i64
  | u64 => simp only [applyTy]; exact .u64
  | bool => simp only [applyTy]; exact .bool
  | float => simp only [applyTy]; exact .float
  | char => simp only [applyTy]; exact .char
  | str => simp only [applyTy]; exact .str
  | natLit => simp only [applyTy]; exact .natLit
  | var hl => simp only [applyTy]; exact .var hl
  | row hr => simp only [applyTy]; exact .row (applyRow_wf hσ hr)
  | «fun» hps heff hret =>
      simp only [applyTy]
      refine .fun ?_ (applyRow_wf hσ heff) (applyTy_kind hσ hret)
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact applyTy_kind hσ (hps a ha)
  | tuple hfs =>
      simp only [applyTy]
      refine .tuple ?_
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact applyTy_kind hσ (hfs a ha)
  | con ctorKind hspine =>
      simp only [applyTy]
      exact .con ctorKind (applySpine_kind hσ hspine)
  | app hf hx =>
      simp only [applyTy]
      exact .app (applyTy_kind hσ hf) (applyTy_kind hσ hx)
  | forallE hb =>
      simp only [applyTy]
      exact .forallE (applyTy_kind (hσ.push _) hb)
  | rowForall hb =>
      simp only [applyTy]
      exact .rowForall (applyTy_kind (hσ.push _) hb)

private theorem applyRow_wf {Γ : KindEnv} {σ : Subst} {ρ : Row}
    (hσ : SubstWF Γ σ) (h : RowWF Γ ρ) : RowWF Γ (applyRow σ ρ) := by
  cases h with
  | empty => simp only [applyRow]; exact .empty
  | var hl => simp only [applyRow]; exact .var hl
  | @exist _ n =>
      rw [applyRow]
      cases hn : σ.row n with
      | none => exact .exist
      | some r => exact hσ.here hn
  | extend hargs hrest =>
      simp only [applyRow]
      refine .extend ?_ (applyRow_wf hσ hrest)
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact applyTy_kind hσ (hargs a ha)

private theorem applySpine_kind {Γ : KindEnv} {σ : Subst} {k : Kind} {args : List Ty}
    {out : Kind} (hσ : SubstWF Γ σ) (h : SpineHasKind Γ k args out) :
    SpineHasKind Γ k (args.map (applyTy σ)) out := by
  cases h with
  | done => exact .done
  | step harg hrest =>
      simp only [List.map_cons]
      exact .step (applyTy_kind hσ harg) (applySpine_kind hσ hrest)

end

theorem applyTy_preserves_kinding (Γ : KindEnv) (σ : Subst) (τ : Ty) (κ : Kind) :
    SubstWF Γ σ →
    HasKind Γ τ κ →
    HasKind Γ (applyTy σ τ) κ := by
  intro hσ h
  exact applyTy_kind hσ h

theorem applyRow_preserves_wf (Γ : KindEnv) (σ : Subst) (ρ : Row) :
    SubstWF Γ σ →
    RowWF Γ ρ →
    RowWF Γ (applyRow σ ρ) := by
  intro hσ h
  exact applyRow_wf hσ h

/-- Elementwise idempotence lifts to the argument lists that `applyTy` maps
over in `.fun`, `.con` and `.tuple`. -/
private theorem map_applyTy_idem {σ : Subst} :
    ∀ (ts : List Ty), (∀ t ∈ ts, applyTy σ (applyTy σ t) = applyTy σ t) →
      (ts.map (applyTy σ)).map (applyTy σ) = ts.map (applyTy σ) := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h a (by simp), ih fun x hx => h x (by simp [hx])⟩

mutual

theorem applyTy_idempotent_after_zonk (σ : Subst) (τ : Ty) :
    Zonked σ →
    applyTy σ (applyTy σ τ) = applyTy σ τ := by
  intro hz
  cases τ with
  | unit => simp only [applyTy]
  | int => simp only [applyTy]
  | i64 => simp only [applyTy]
  | u64 => simp only [applyTy]
  | bool => simp only [applyTy]
  | float => simp only [applyTy]
  | char => simp only [applyTy]
  | str => simp only [applyTy]
  | var x => simp only [applyTy]
  | nat n => simp only [applyTy]
  | exist n =>
      cases hn : σ.ty n with
      | none =>
          have h1 : applyTy σ (Ty.exist n) = Ty.exist n := by rw [applyTy, hn]
          rw [h1]; exact h1
      | some t =>
          have h1 : applyTy σ (Ty.exist n) = t := by rw [applyTy, hn]
          rw [h1]; exact hz.1 n t hn
  | «fun» ps eff ret =>
      simp only [applyTy]
      rw [map_applyTy_idem ps fun t _ => applyTy_idempotent_after_zonk σ t hz,
        applyRow_idempotent_after_zonk σ eff hz,
        applyTy_idempotent_after_zonk σ ret hz]
  | con c args =>
      simp only [applyTy]
      rw [map_applyTy_idem args fun t _ => applyTy_idempotent_after_zonk σ t hz]
  | tuple fields =>
      simp only [applyTy]
      rw [map_applyTy_idem fields fun t _ => applyTy_idempotent_after_zonk σ t hz]
  | app f x =>
      simp only [applyTy]
      rw [applyTy_idempotent_after_zonk σ f hz, applyTy_idempotent_after_zonk σ x hz]
  | row r =>
      simp only [applyTy]
      rw [applyRow_idempotent_after_zonk σ r hz]
  | forallE x body =>
      simp only [applyTy]
      rw [applyTy_idempotent_after_zonk σ body hz]
  | rowForall x body =>
      simp only [applyTy]
      rw [applyTy_idempotent_after_zonk σ body hz]

theorem applyRow_idempotent_after_zonk (σ : Subst) (ρ : Row) :
    Zonked σ →
    applyRow σ (applyRow σ ρ) = applyRow σ ρ := by
  intro hz
  cases ρ with
  | empty => simp only [applyRow]
  | var x => simp only [applyRow]
  | exist n =>
      cases hn : σ.row n with
      | none =>
          have h1 : applyRow σ (Row.exist n) = Row.exist n := by rw [applyRow, hn]
          rw [h1]; exact h1
      | some r =>
          have h1 : applyRow σ (Row.exist n) = r := by rw [applyRow, hn]
          rw [h1]; exact hz.2 n r hn
  | extend name args rest =>
      simp only [applyRow]
      rw [map_applyTy_idem args fun t _ => applyTy_idempotent_after_zonk σ t hz,
        applyRow_idempotent_after_zonk σ rest hz]

end

/-- Vacuously true while `unify` is the throwing stub: the hypothesis can never
be produced. Implementing `unify` breaks this proof and resurfaces the real
obligation, which is the intent. -/
theorem unify_sound (τ υ : Ty) (σ : Subst) :
    unify τ υ = Except.ok σ →
    TyEq (applyTy σ τ) (applyTy σ υ) := by
  intro h
  simp [unify, throw, throwThe, MonadExceptOf.throw] at h

/-- Vacuously true while `unifyRow` is the throwing stub; see `unify_sound`. -/
theorem unifyRow_sound (ρ₁ ρ₂ : Row) (σ : Subst) :
    unifyRow ρ₁ ρ₂ = Except.ok σ →
    RowEq (applyRow σ ρ₁) (applyRow σ ρ₂) := by
  intro h
  simp [unifyRow, throw, throwThe, MonadExceptOf.throw] at h

/-- Vacuously true while `inferExpr` is the throwing stub; see `unify_sound`. -/
theorem inferExpr_sound (Γ : TermEnv) (e : Expr) (τ : Ty) (eff : Row) :
    inferExpr Γ e = Except.ok (τ, eff) →
    HasType Γ e τ eff := by
  intro h
  simp [inferExpr, throw, throwThe, MonadExceptOf.throw] at h

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

/-- Holds by construction while `DeclsWellTyped` is the abstract `.assumed`
placeholder. Refining the predicate to a real judgment breaks this proof and
resurfaces the obligation, which is the intent. -/
theorem declaration_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c := by
  intro _
  exact DeclsWellTyped.assumed

/-- Holds by construction while the predicates are `.assumed` placeholders;
see `declaration_checking_sound`. -/
theorem class_resolution_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c ∧ DictionariesValid p c := by
  intro _ _
  exact ⟨ClassesCoherent.assumed, DictionariesValid.assumed⟩

/-- Holds by construction while `PatternsSound` is the `.assumed` placeholder;
see `declaration_checking_sound`. -/
theorem pattern_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    PatternsSound p c := by
  intro _ _
  exact PatternsSound.assumed

/-- Holds by construction while the predicates are `.assumed` placeholders;
see `declaration_checking_sound`. -/
theorem effect_checking_sound (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    EffectsSound p c ∧ HandlerGradesSound p c := by
  intro _ _
  exact ⟨EffectsSound.assumed, HandlerGradesSound.assumed⟩

/-- Holds by construction while `SideTablesValid` is the `.assumed`
placeholder; see `declaration_checking_sound`. -/
theorem checked_side_tables_valid (p : Program) (c : Checked) :
    InputWellFormed p →
    DeclsWellTyped p c →
    ClassesCoherent p c →
    DictionariesValid p c →
    PatternsSound p c →
    EffectsSound p c →
    HandlerGradesSound p c →
    SideTablesValid p c := by
  intro _ _ _ _ _ _ _
  exact SideTablesValid.assumed

/-- Holds by construction while `CheckedValid` is the `.assumed` placeholder;
see `declaration_checking_sound`. -/
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
  intro _ _ _ _ _ _ _ _
  exact CheckedValid.assumed

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
