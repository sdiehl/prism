import CEK

/-
This file is about the effect stack walk in the CEK machine. `findHandler` is
operational code; `Handles` is the little logical predicate that says the same
thing without running the search.

The useful facts are simple. If a stack handles an operation, the machine makes
progress. If it does not, the machine reports the unhandled operation. Masks just
adjust how many matching handlers the search skips, and transparent scheduler
frames let foreign effects tunnel to an outer handler.
-/
namespace Prism

/-- `op` is handled in `stk` after skipping `skip` matching handlers. Mirrors the
    search performed by `findHandler`: a `mask` of `op` increments the skip count,
    a matching `handle` either is the target (`here`, skip 0) or is one of the
    skipped handlers (`skipH`), and `bind`/`args`/non-matching frames are crossed. -/
inductive Handles (op : String) : Nat → Stack → Prop where
  | here ops rv rb env rest :
      handlerFor op ops ≠ none →
      Handles op 0 (.handle ops rv rb env :: rest)
  | skipH ops rv rb env rest skip :
      handlerFor op ops ≠ none →
      Handles op skip rest →
      Handles op (skip + 1) (.handle ops rv rb env :: rest)
  | passH ops rv rb env rest skip :
      handlerFor op ops = none →
      Handles op skip rest →
      Handles op skip (.handle ops rv rb env :: rest)
  | maskYes ops rest skip :
      ops.contains op →
      Handles op (skip + 1) rest →
      Handles op skip (.mask ops :: rest)
  | maskNo ops rest skip :
      ¬ops.contains op →
      Handles op skip rest →
      Handles op skip (.mask ops :: rest)
  | bind x n env rest skip : Handles op skip rest → Handles op skip (.bind x n env :: rest)
  | args a env rest skip : Handles op skip rest → Handles op skip (.args a env :: rest)

namespace Handles

/-- If adding a bind frame would make a stack handled, then the tail was already
    handled. -/
theorem notBind {op : String} {x : String} {n : Comp} {env : Env}
    {rest : Stack} {skip : Nat} :
    ¬Handles op skip (.bind x n env :: rest) → ¬Handles op skip rest :=
  fun hns hr => hns (.bind x n env rest skip hr)

/-- If adding an argument frame would make a stack handled, then the tail was
    already handled. -/
theorem notArgs {op : String} {args : List Value} {env : Env}
    {rest : Stack} {skip : Nat} :
    ¬Handles op skip (.args args env :: rest) → ¬Handles op skip rest :=
  fun hns hr => hns (.args args env rest skip hr)

/-- If a mask names the operation, the search skips one matching handler in the
    tail. -/
theorem notMasked {op : String} {ops : List String} {rest : Stack}
    {skip : Nat} (hc : ops.contains op) :
    ¬Handles op skip (.mask ops :: rest) → ¬Handles op (skip + 1) rest :=
  fun hns hr => hns (.maskYes ops rest skip hc hr)

/-- If a mask does not name the operation, the search just crosses it. -/
theorem notUnmasked {op : String} {ops : List String} {rest : Stack}
    {skip : Nat} (hc : ¬ops.contains op) :
    ¬Handles op skip (.mask ops :: rest) → ¬Handles op skip rest :=
  fun hns hr => hns (.maskNo ops rest skip hc hr)

/-- At skip count zero, a matching handler contradicts an unhandled-stack
    assumption. -/
theorem impossibleHere {op : String} {ops : List HandleOp} {rv : Option String}
    {rb : Option Comp} {env : Env} {rest : Stack}
    (hf : handlerFor op ops ≠ none) :
    ¬Handles op 0 (.handle ops rv rb env :: rest) → False :=
  fun hns => hns (.here ops rv rb env rest hf)

/-- With positive skip count, a matching handler consumes one skip and the tail
    still has to be impossible. -/
theorem notSkippedHandler {op : String} {ops : List HandleOp} {rv : Option String}
    {rb : Option Comp} {env : Env} {rest : Stack} {skip : Nat}
    (hf : handlerFor op ops ≠ none) :
    ¬Handles op (skip + 1) (.handle ops rv rb env :: rest) →
    ¬Handles op skip rest :=
  fun hns hr => hns (.skipH ops rv rb env rest skip hf hr)

/-- A non-matching handler is transparent to this operation, so impossibility
    passes to the tail. -/
theorem notPassingHandler {op : String} {ops : List HandleOp} {rv : Option String}
    {rb : Option Comp} {env : Env} {rest : Stack} {skip : Nat}
    (hf : handlerFor op ops = none) :
    ¬Handles op skip (.handle ops rv rb env :: rest) → ¬Handles op skip rest :=
  fun hns hr => hns (.passH ops rv rb env rest skip hf hr)

end Handles

/-- A handled effect makes progress: the stack walk reaches a handler and the
    machine takes a step rather than getting stuck. -/
theorem effect_progress
    {op : String} {argvs : List Rv} {skip : Nat} {stk : Stack}
    (h : Handles op skip stk) :
    ∀ captured, (findHandler op argvs skip captured stk).isSome :=
  -- Trust the Lean kernel; grind baby grind.
  by induction h <;> grind [findHandler]

/-- An unhandled effect is stuck: with no matching handler in scope the stack
    walk runs off the end and `perform` reports the unhandled-effect error. -/
theorem effect_unhandled {op : String} {argvs : List Rv} :
    ∀ {skip : Nat} {stk : Stack},
      ¬Handles op skip stk →
      ∀ captured, findHandler op argvs skip captured stk = none :=
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
            exact ih (Handles.notBind hns) _
          | args a env =>
            simp only [findHandler]
            exact ih (Handles.notArgs hns) _
          | mask ops =>
            simp only [findHandler]
            by_cases hc : ops.contains op
            · rw [if_pos hc]
              exact ih (Handles.notMasked hc hns) _
            · rw [if_neg hc]
              exact ih (Handles.notUnmasked hc hns) _
          | handle ops rv rb env =>
            simp only [findHandler]
            cases hfm : handlerFor op ops with
              | none => exact ih (Handles.notPassingHandler hfm hns) _
              | some t => cases skip with
                  | zero => exact (Handles.impossibleHere (by rw [hfm]; exact nofun) hns).elim
                  | succ k =>
                    simp only [Nat.succ_sub_one]
                    exact ih (Handles.notSkippedHandler (by rw [hfm]; exact nofun) hns) _

/-
Ambient-row transparency (tunneling) at the machine level.

Effect-polymorphic concurrency ties a forked fiber's effect-row variable to the
caller's ambient row: a fiber that performs `E` forces `E` into the caller's row,
so `E` flows out through `run_async` and must be handled at the edge. The
scheduler is transparent to a fiber's non-`Async` effects: they tunnel past the
scheduler's own handler to an outer handler; nothing a fiber performs escapes
untyped or unhandled.

`findHandler` already realizes exactly this tunneling operationally: a scheduler
`handle` frame whose clauses do not cover `op` is crossed by `passH`, and the
`bind`/`args` frames the trampolining driver pushes are crossed by `bind`/`args`,
so the stack walk continues to an outer handler. `Tunnels op inner` names such a
transparent segment: a run of frames the search crosses without trapping `op` and
without shifting the skip count (no matching handler, no masking of `op`). This is
the machine image of "the scheduler segment `run_async` contributes does not trap
a fiber's foreign capability".

Gap to the surface guarantee (honest): the model proves the OPERATIONAL image.
If the scheduler segment is transparent to `op` and an outer handler covers `op`,
the machine tunnels to it and never gets stuck. The TYPING side (that the
ambient-row inference forces every `op` a fiber performs into the caller's row, so
a covering handler must exist at the edge) lives in the Rust row checker
(`bind_op_rows_to_ambient`), not here; this machine model does not formalize the
surface row types. The two meet at `Handles`: row inference guarantees the stack
covers the row, and these theorems guarantee a covered stack is effect-safe.
-/

/-- A stack segment the `findHandler` search crosses transparently for `op`:
    every frame is passed over without trapping `op` and without changing the
    skip count. Mirrors the non-terminating, skip-preserving arms of `findHandler`:
    `args`/`bind` (always crossed), a `handle` whose clauses do not cover `op`
    (crossed by `passH`), and a `mask` that does not name `op` (crossed by
    `maskNo`). This is the shape of the frames a transparent scheduler adds
    beneath a fiber: its `handle Async` frame plus the driver's `bind`/`args`. -/
inductive Tunnels (op : String) : Stack → Prop where
  | nil : Tunnels op []
  | args a env rest : Tunnels op rest → Tunnels op (.args a env :: rest)
  | bind x n env rest : Tunnels op rest → Tunnels op (.bind x n env :: rest)
  | passH ops rv rb env rest :
      handlerFor op ops = none →
      Tunnels op rest →
      Tunnels op (.handle ops rv rb env :: rest)
  | maskNo ops rest : ¬ops.contains op → Tunnels op rest → Tunnels op (.mask ops :: rest)

namespace Tunnels

/-- Transparency / tunneling: a transparent scheduler segment `inner` is crossed,
    so if an outer segment `outer` handles `op` (after skipping `skip`), the whole
    stack `inner ++ outer` still handles `op` with the same skip count. This is the
    machine image of a fiber's foreign effect tunneling past `run_async`'s handler
    to the caller's handler, exactly as `passH`/`bind`/`args` cross frames. -/
theorem handles {op : String} {skip : Nat} {outer : Stack} {inner : Stack}
    (ht : Tunnels op inner) (hh : Handles op skip outer) : Handles op skip (inner ++ outer) :=
  by induction ht with
      | nil => exact hh
      | args a env rest _ ih => exact Handles.args a env (rest ++ outer) skip ih
      | bind x n env rest _ ih => exact Handles.bind x n env (rest ++ outer) skip ih
      | passH ops rv rb env rest hf _ ih =>
        exact Handles.passH ops rv rb env (rest ++ outer) skip hf ih
      | maskNo ops rest hc _ ih => exact Handles.maskNo ops (rest ++ outer) skip hc ih

end Tunnels

/-- Same tunneling fact under the old theorem name used by downstream proofs. -/
theorem effect_tunnels {op : String} {skip : Nat} {outer : Stack} {inner : Stack}
    (ht : Tunnels op inner) (hh : Handles op skip outer) : Handles op skip (inner ++ outer) :=
  ht.handles hh

/-- Machine-step image of effect coverage: a `doOp` whose operation is handled in
    the current stack is never stuck: the machine takes a step. This is the
    per-form progress lemma for the effectful node, the analogue of the `Meta.lean`
    progress cases at the CEK level: a well-covered `doOp` makes progress. -/
theorem effect_doOp_progress {Γ : Core} {op : String} {args : List Value} {env : Env}
    {stk : Stack} {avs : List Rv}
    (hargs : atomEval.atomEvalL env args = some avs) (hh : Handles op 0 stk) :
    (step Γ (.eval (.doOp op args) env, stk)).isSome :=
  by
    simp only [step, hargs]
    exact effect_progress hh []

/-- Dual: a `doOp` whose operation is NOT handled anywhere in scope is stuck.
    `step` returns `none`, the machine's unhandled-effect error. This is the state
    the ambient-row typing rules out: the row demands a handler, so a well-rowed
    configuration never reaches this. -/
theorem effect_doOp_stuck {Γ : Core} {op : String} {args : List Value} {env : Env}
    {stk : Stack} {avs : List Rv}
    (hargs : atomEval.atomEvalL env args = some avs) (hns : ¬Handles op 0 stk) :
    step Γ (.eval (.doOp op args) env, stk) = none :=
  by
    simp only [step, hargs]
    exact effect_unhandled hns []

/-- Headline: ambient-row concurrency soundness, machine image. A fiber performs a
    foreign operation `op` (`doOp`) under a transparent scheduler segment `inner`
    that does not handle `op`; if the caller's stack `outer` supplies a handler for
    `op`, the machine STEPS rather than getting stuck: the effect tunnels through
    `run_async` to the edge handler. Combines `effect_tunnels` (the segment is
    crossed) with `effect_doOp_progress` (a covered `doOp` progresses). -/
theorem effect_tunnels_progress {Γ : Core} {op : String} {args : List Value} {env : Env}
    {inner outer : Stack} {avs : List Rv}
    (ht : Tunnels op inner) (hh : Handles op 0 outer)
    (hargs : atomEval.atomEvalL env args = some avs) :
    (step Γ (.eval (.doOp op args) env, inner ++ outer)).isSome :=
  effect_doOp_progress hargs (ht.handles hh)

end Prism
