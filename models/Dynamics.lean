import CEK

/-
Effect dynamics: metatheory of the CEK machine's algebraic-effect handling
(`perform`/`findHandler` in `CEK.lean`, transcribing `perform` in
`src/eval/mod.rs`). The substitution core in `Prism.lean` reduces effects by
erasure; the *machine* implements them by walking the continuation stack to the
nearest enclosing handler, skipping one matching handler per crossed `mask`
(Koka semantics) and capturing the crossed frames -- handler included -- as a
multishot `resume`.

`Handles op skip stk` is the inductive predicate "operation `op` is handled in
stack `stk`, with `skip` matching handlers to skip first" -- the exact condition
the stack walk in `findHandler` is searching for. The two theorems then pin down
the machine's effect behavior precisely:

* `effect_progress`  -- if `op` is handled, `perform` makes progress (never stuck).
* `effect_unhandled` -- if `op` is not handled, `perform` is stuck (the "unhandled
  effect" error), exactly mirroring the `Err` arm in the Rust `perform`.

Together: `findHandler` succeeds iff `Handles` holds, so the oracle handles an
effect exactly when a matching handler is in dynamic scope.
-/
namespace Prism

/-- `op` is handled in `stk` after skipping `skip` matching handlers. Mirrors the
    search performed by `findHandler`: a `mask` of `op` increments the skip count,
    a matching `handle` either is the target (`here`, skip 0) or is one of the
    skipped handlers (`skipH`), and `bind`/`args`/non-matching frames are crossed. -/
inductive Handles (op : String) : Nat → Stack → Prop where
  | here ops rv rb env rest : handlerFor op ops ≠ none → Handles op 0 (.handle ops rv rb env :: rest)
  | skipH ops rv rb env rest skip : handlerFor op ops ≠ none → Handles op skip rest → Handles op (skip + 1) (.handle ops rv rb env :: rest)
  | passH ops rv rb env rest skip : handlerFor op ops = none → Handles op skip rest → Handles op skip (.handle ops rv rb env :: rest)
  | maskYes ops rest skip : ops.contains op → Handles op (skip + 1) rest → Handles op skip (.mask ops :: rest)
  | maskNo ops rest skip : ¬ops.contains op → Handles op skip rest → Handles op skip (.mask ops :: rest)
  | bind x n env rest skip : Handles op skip rest → Handles op skip (.bind x n env :: rest)
  | args a env rest skip : Handles op skip rest → Handles op skip (.args a env :: rest)

/-- A handled effect makes progress: the stack walk reaches a handler and the
    machine takes a step rather than getting stuck. -/
theorem effect_progress {op : String} {argvs : List Rv} {skip : Nat} {stk : Stack} (h : Handles op skip stk) : ∀ captured, (findHandler op argvs skip captured stk).isSome :=
  by induction h with
      | here ops rv rb env rest hf =>
        intro captured
        cases hfm : handlerFor op ops with
          | none => exact absurd hfm hf
          | some t => simp [findHandler, hfm]
      | skipH ops rv rb env rest skip hf _ ih =>
        intro captured
        cases hfm : handlerFor op ops with
          | none => exact absurd hfm hf
          | some t =>
            simp [findHandler, hfm]
            exact ih _
      | passH ops rv rb env rest skip hf _ ih =>
        intro captured
        simp [findHandler, hf]
        exact ih _
      | maskYes ops rest skip hc _ ih =>
        intro captured
        simp only [findHandler]
        rw [if_pos hc]
        exact ih _
      | maskNo ops rest skip hc _ ih =>
        intro captured
        simp only [findHandler]
        rw [if_neg hc]
        exact ih _
      | bind x n env rest skip _ ih =>
        intro captured
        simp [findHandler]
        exact ih _
      | args a env rest skip _ ih =>
        intro captured
        simp [findHandler]
        exact ih _

/-- An unhandled effect is stuck: with no matching handler in scope the stack
    walk runs off the end and `perform` reports the unhandled-effect error. -/
theorem effect_unhandled {op : String} {argvs : List Rv} : ∀ {skip : Nat} {stk : Stack}, ¬Handles op skip stk → ∀ captured, findHandler op argvs skip captured stk = none :=
  by
    intro skip stk
    induction stk generalizing skip with
      | nil =>
        intro _ captured
        rfl
      | cons fr rest ih =>
        intro hns captured
        cases fr with
          | bind x n env =>
            simp only [findHandler]
            exact ih (fun hr => hns (.bind x n env rest skip hr)) _
          | args a env =>
            simp only [findHandler]
            exact ih (fun hr => hns (.args a env rest skip hr)) _
          | mask ops =>
            simp only [findHandler]
            by_cases hc : ops.contains op
            · rw [if_pos hc]
              exact ih (fun hr => hns (.maskYes ops rest skip hc hr)) _
            · rw [if_neg hc]
              exact ih (fun hr => hns (.maskNo ops rest skip hc hr)) _
          | handle ops rv rb env =>
            simp only [findHandler]
            cases hfm : handlerFor op ops with
              | none => exact ih (fun hr => hns (.passH ops rv rb env rest skip hfm hr)) _
              | some t => cases skip with
                  | zero => exact absurd (Handles.here ops rv rb env rest (by
                      rw [hfm]
                      exact nofun)) hns
                  | succ k =>
                    simp only [Nat.succ_sub_one]
                    exact ih (fun hr => hns (.skipH ops rv rb env rest k (by
                      rw [hfm]
                      exact nofun) hr)) _

end Prism
