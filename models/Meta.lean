import Prism

/-
Metatheory of the substitution small-step semantics in `Prism.lean`, beyond the
existing `Step.deterministic`:

* `Steps.unique_normal` -- determinism lifted to whole runs: a computation has at
  most one normal (terminal) form (the Church-Rosser corollary for a deterministic
  relation).
* substitution unfolding helpers used throughout the development.
* `progress` -- a syntactic trichotomy: every computation is terminal, takes a
  step, or is an explicit `Stuck` error configuration. There are no silently
  stuck states; the error surface is exactly `Stuck`.
-/
namespace Prism

/-- A terminal computation (`ret`/`lam`) cannot step. Generalizes `noStepRet`/`noStepLam`. -/
theorem terminalNoStep {Γ : Core} {a b : Comp} (h : Terminal a) : ¬Step Γ a b :=
  by
    intro hs
    cases a <;> first | exact noStepRet hs | exact noStepLam hs | exact h.elim

/-- Unique normal form: any two terminating runs from the same start reach the
    same terminal computation. -/
theorem Steps.unique_normal {Γ : Core} {a m n : Comp} (hm : Steps Γ a m) (hn : Steps Γ a n) (tm : Terminal m) (tn : Terminal n) : m = n :=
  by induction hm generalizing n with
      | refl => cases hn with
          | refl => rfl
          | head hs _ => exact absurd hs (terminalNoStep tm)
      | head hs _ ih => cases hn with
          | refl => exact absurd hs (terminalNoStep tn)
          | head hs' hrest' =>
            have hbb := Step.deterministic hs hs'
            rw [← hbb] at hrest'
            exact ih hrest' tm tn

/-- `substMany` is the left fold of `substC`; these two equations are how it
    unfolds (definitional, recorded for readability and rewriting). -/
@[simp]
theorem substMany_nil (c : Comp) : substMany [] c = c := rfl

@[simp]
theorem substMany_cons (x : String) (w : Value) (rest : List (String × Value)) (c : Comp) : substMany ((x, w) :: rest) c = substMany rest (substC x w c) :=
  rfl

/-- A lambda absorbs substitution of one of its own parameters. -/
theorem substC_lam_shadow {x : String} {w : Value} {xs : List String} {b : Comp} (h : xs.contains x) : substC x w (.lam xs b) = .lam xs b :=
  by
    show Comp.lam xs (if xs.contains x then b else substC x w b) = .lam xs b
    rw [if_pos h]

/-- Explicit error / blocked configurations of the substitution semantics: the
    head redex is present but ill-formed (wrong operand shapes, a missing
    function, no matching arm, a returner where a function is needed, or a
    function where a returner is needed) or is an effect/IO node the pure core
    does not reduce. Mirrors the `Err`/`None` arms of the CEK machine. -/
inductive Stuck (Γ : Core) : Comp → Prop where
  | forceNonThunk (v : Value) : (∀ c, v ≠ .thunk c) → Stuck Γ (.force v)
  | iteNonBool (c : Value) (t e : Comp) : (∀ b, c ≠ .bool b) → Stuck Γ (.ite c t e)
  | primStuck (op : BinOp) (a b : Value) : delta op a b = none → Stuck Γ (.prim op a b)
  | callMissing (name : String) (args : List Value) : lookupFn Γ name = none → Stuck Γ (.call name args)
  | caseNoMatch (s : Value) (arms : List (Pat × Comp)) : matchArms s arms = none → Stuck Γ (.case s arms)
  | err (v : Value) : Stuck Γ (.err v)
  | doOp (n : String) (args : List Value) : Stuck Γ (.doOp n args)
  | handle (b : Comp) rv rb ops : Stuck Γ (.handle b rv rb ops)
  | mask (ops : List String) (b : Comp) : Stuck Γ (.mask ops b)
  | print (v : Value) : Stuck Γ (.print v)
  | printf (v : Value) : Stuck Γ (.printf v)
  | prints (v : Value) : Stuck Γ (.prints v)
  | readInt : Stuck Γ .readInt
  | floatBuiltin (n : String) (v : Value) : Stuck Γ (.floatBuiltin n v)
  | strBuiltin (n : String) (args : List Value) : Stuck Γ (.strBuiltin n args)
  -- a returner bound where a function is applied, or vice versa (ill-typed heads)
  | bindLam (xs : List String) (b : Comp) (x : String) (n : Comp) : Stuck Γ (.bind (.lam xs b) x n)
  | appRet (v : Value) (args : List Value) : Stuck Γ (.app (.ret v) args)
  -- a stuck head blocks the enclosing congruence frame
  | bindStuck (m : Comp) (x : String) (n : Comp) : Stuck Γ m → Stuck Γ (.bind m x n)
  | appStuck (f : Comp) (args : List Value) : Stuck Γ f → Stuck Γ (.app f args)

/-- `Stuck` and `Terminal` are disjoint: a blocked configuration is never a
    value. Together with `progress` this makes the classification a genuine
    partition of the non-stepping computations. -/
theorem stuckNotTerminal {Γ : Core} {c : Comp} (h : Stuck Γ c) : ¬Terminal c :=
  by cases h <;> intro ht <;> exact ht.elim

/-- A `Stuck` configuration genuinely does not reduce: this justifies the name
    and makes the three `progress` alternatives mutually exclusive. -/
theorem stuckNoStep {Γ : Core} {c c' : Comp} (h : Stuck Γ c) : ¬Step Γ c c' :=
  by induction h generalizing c' with
      | forceNonThunk v hne =>
        intro hs
        cases hs
        exact hne _ rfl
      | iteNonBool c t e hne =>
        intro hs
        cases hs <;> exact hne _ rfl
      | primStuck op a b hd =>
        intro hs
        cases hs
        rename_i hd'
        simp [hd] at hd'
      | callMissing name args hl =>
        intro hs
        cases hs
        rename_i hl'
        simp [hl] at hl'
      | caseNoMatch s arms hm =>
        intro hs
        cases hs
        rename_i hm'
        simp [hm] at hm'
      | err v =>
        intro hs
        cases hs
      | doOp n args =>
        intro hs
        cases hs
      | handle b rv rb ops =>
        intro hs
        cases hs
      | mask ops b =>
        intro hs
        cases hs
      | print v =>
        intro hs
        cases hs
      | printf v =>
        intro hs
        cases hs
      | prints v =>
        intro hs
        cases hs
      | readInt =>
        intro hs
        cases hs
      | floatBuiltin n v =>
        intro hs
        cases hs
      | strBuiltin n args =>
        intro hs
        cases hs
      | bindLam xs b x n =>
        intro hs
        cases hs
        rename_i hbad
        exact noStepLam hbad
      | appRet v args =>
        intro hs
        cases hs
        rename_i hbad
        exact noStepRet hbad
      | bindStuck m x n hst ih =>
        intro hs
        cases hs with
          | bindRet => exact (stuckNotTerminal hst) trivial
          | bindCong hm => exact ih hm
      | appStuck f args hst ih =>
        intro hs
        cases hs with
          | beta => exact (stuckNotTerminal hst) trivial
          | appCong hf => exact ih hf

/-- A terminal computation is either a `ret` or a `lam`. -/
theorem terminalCases {c : Comp} (h : Terminal c) : (∃ v, c = .ret v) ∨ (∃ xs b, c = .lam xs b) :=
  by
    revert h
    cases c <;> intro h <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, _, rfl⟩ | exact h.elim

theorem forceP (Γ : Core) (v : Value) : (∃ c', Step Γ (.force v) c') ∨ Stuck Γ (.force v) :=
  by cases v <;> first | exact Or.inl ⟨_, .forceThunk⟩ | exact Or.inr (.forceNonThunk _ (fun _ => nofun))

theorem iteP (Γ : Core) (c : Value) (t e : Comp) : (∃ c', Step Γ (.ite c t e) c') ∨ Stuck Γ (.ite c t e) :=
  by cases c with
      | bool b => cases b <;> first | exact Or.inl ⟨_, .ifTrue⟩ | exact Or.inl ⟨_, .ifFalse⟩
      | var x => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | int n => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | float f => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | unit => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | str s => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | thunk cc => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | ctor nm tg a => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))
      | tuple a => exact Or.inr (.iteNonBool _ _ _ (fun _ => nofun))

theorem primP (Γ : Core) (op : BinOp) (a b : Value) : (∃ c', Step Γ (.prim op a b) c') ∨ Stuck Γ (.prim op a b) :=
  by cases h : delta op a b with
      | some v => exact Or.inl ⟨_, .prim h⟩
      | none => exact Or.inr (.primStuck _ _ _ h)

theorem callP (Γ : Core) (name : String) (args : List Value) : (∃ c', Step Γ (.call name args) c') ∨ Stuck Γ (.call name args) :=
  by cases h : lookupFn Γ name with
      | some f => exact Or.inl ⟨_, .call h⟩
      | none => exact Or.inr (.callMissing _ _ h)

theorem caseP (Γ : Core) (s : Value) (arms : List (Pat × Comp)) : (∃ c', Step Γ (.case s arms) c') ∨ Stuck Γ (.case s arms) :=
  by cases h : matchArms s arms with
      | some c => exact Or.inl ⟨_, .caseMatch h⟩
      | none => exact Or.inr (.caseNoMatch _ _ h)

/--
Progress / safety classification: every computation is `Terminal` (`ret`/`lam`),
takes a `Step`, or is an explicit `Stuck` error configuration. There are no
silently stuck states; the error surface is exactly `Stuck`. (No type system is
assumed, so "stuck" genuinely occurs, e.g. `prim add true 1`; the theorem pins
down precisely where.)
-/
theorem progress (Γ : Core) : (c : Comp) → Terminal c ∨ (∃ c', Step Γ c c') ∨ Stuck Γ c
  | .ret _ => Or.inl trivial
  | .lam _ _ => Or.inl trivial
  | .force v => Or.inr (forceP Γ v)
  | .ite c t e => Or.inr (iteP Γ c t e)
  | .prim op a b => Or.inr (primP Γ op a b)
  | .call name args => Or.inr (callP Γ name args)
  | .case s arms => Or.inr (caseP Γ s arms)
  | .bind m x n =>
    match progress Γ m with
      | Or.inl tm =>
        match terminalCases tm with
          | Or.inl ⟨_, hv⟩ =>
            by
              subst hv
              exact Or.inr (Or.inl ⟨_, .bindRet⟩)
          | Or.inr ⟨_, _, hl⟩ =>
            by
              subst hl
              exact Or.inr (Or.inr (.bindLam _ _ _ _))
      | Or.inr (Or.inl ⟨_, hs⟩) => Or.inr (Or.inl ⟨_, .bindCong hs⟩)
      | Or.inr (Or.inr hst) => Or.inr (Or.inr (.bindStuck _ _ _ hst))
  | .app f args =>
    match progress Γ f with
      | Or.inl tf =>
        match terminalCases tf with
          | Or.inl ⟨_, hv⟩ =>
            by
              subst hv
              exact Or.inr (Or.inr (.appRet _ _))
          | Or.inr ⟨_, _, hl⟩ =>
            by
              subst hl
              exact Or.inr (Or.inl ⟨_, .beta⟩)
      | Or.inr (Or.inl ⟨_, hs⟩) => Or.inr (Or.inl ⟨_, .appCong hs⟩)
      | Or.inr (Or.inr hst) => Or.inr (Or.inr (.appStuck _ _ hst))
  | .dup _ => Or.inr (Or.inl ⟨_, .dupStep⟩)
  | .drop _ => Or.inr (Or.inl ⟨_, .dropStep⟩)
  | .withReuse _ _ _ => Or.inr (Or.inl ⟨_, .withReuseStep⟩)
  | .reuse _ _ => Or.inr (Or.inl ⟨_, .reuseStep⟩)
  | .err _ => Or.inr (Or.inr (.err _))
  | .doOp _ _ => Or.inr (Or.inr (.doOp _ _))
  | .handle _ _ _ _ => Or.inr (Or.inr (.handle _ _ _ _))
  | .mask _ _ => Or.inr (Or.inr (.mask _ _))
  | .print _ => Or.inr (Or.inr (.print _))
  | .printf _ => Or.inr (Or.inr (.printf _))
  | .prints _ => Or.inr (Or.inr (.prints _))
  | .readInt => Or.inr (Or.inr .readInt)
  | .floatBuiltin _ _ => Or.inr (Or.inr (.floatBuiltin _ _))
  | .strBuiltin _ _ => Or.inr (Or.inr (.strBuiltin _ _))

end Prism
