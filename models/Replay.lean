import CEK

/-
Record-and-replay faithfulness for the Prism CEK machine.

The only nondeterministic INPUT to the core is `readInt`: every other I/O node is
output (erased to unit) and `doOp`/`handle`/`mask` are deterministic effect
plumbing. The oracle machine in `CEK.lean` erases `readInt` to the constant `0`
(input pinned, so the model stays a deterministic function the Rust differential
test can check by `rfl`). Here we ADD a *traced* machine that does not erase
input: it threads a list of integers `List Int` (the input trace) alongside the
ordinary configuration and, at a `readInt`, consumes the head of that trace
instead of returning `0`. An empty trace at a `readInt` halts the run (input
exhausted). Every non-`readInt` transition reuses the existing `step` verbatim
and leaves the trace untouched, so the traced machine is the oracle machine plus
an input tape.

`record` runs the traced machine on a full input list `ins` and reports the final
configuration together with the prefix of `ins` it actually read; `replay` runs
it on a supplied trace. The theorem `replay_faithful` is the record/replay
contract: replaying exactly the inputs that `record` consumed reproduces the
configuration `record` reached. The mathematical content is that the machine's
result depends only on the sequence of inputs it actually reads; supplying that
sequence (and nothing more) reaches the same place. The proof is a lockstep
argument: `tstep` is a function, so per-step determinism is free, and an
induction over the unconsumed suffix shows that stripping the suffix leaves every
step (hence the final configuration) unchanged. A monotonicity lemma (the
leftover trace never grows) rules out the only awkward case, a `readInt` that
would have run off the end of the shortened trace.
-/

namespace Prism

/-- A traced configuration: an ordinary CEK configuration paired with the
    remaining input trace (the integers a future `readInt` will consume). -/
abbrev TConf := Conf × List Int

/-- One transition of the traced machine. It is the oracle `step` for every
    node except `readInt`: at `readInt` it pops the head of the input trace
    (`v :: t` yields the value `v` and leaves `t`), and halts on an empty trace
    (`none`, input exhausted). Non-`readInt` transitions ignore the trace, so the
    existing `step` machinery is reused wholesale. -/
def tstep (Γ : Core) (t : TConf) : Option TConf :=
  match t with
  | ((.eval .readInt _, stk), v :: rest) => some ((.ret (.int v), stk), rest)
  | ((.eval .readInt _, _), []) => none
  | (cf, ins) => (step Γ cf).map (fun c' => (c', ins))

/-- Iterate the traced machine for at most `fuel` steps, stopping when it
    halts (`tstep = none`). Mirrors `run`. -/
def trun : Nat → Core → TConf → TConf
  | 0, _, t => t
  | n + 1, Γ, t => match tstep Γ t with
    | some t' => trun n Γ t'
    | none => t

/-- For a configuration that is not a `readInt` evaluation, the traced step is
    exactly the oracle step with the trace carried along untouched. -/
theorem tstep_not_readInt (Γ : Core) {cf : Conf}
    (h : ∀ env stk, cf ≠ (.eval .readInt env, stk)) (ins : List Int) :
    tstep Γ (cf, ins) = (step Γ cf).map (fun c' => (c', ins)) := by
  rcases cf with ⟨m, stk⟩
  cases m with
  | ret v => rfl
  | eval c env =>
      cases c <;> first
        | exact absurd rfl (h env stk)
        | rfl

theorem trun_succ_some {Γ : Core} {n : Nat} {t t' : TConf}
    (h : tstep Γ t = some t') : trun (n + 1) Γ t = trun n Γ t' := by
  simp only [trun, h]

theorem trun_succ_none {Γ : Core} {n : Nat} {t : TConf}
    (h : tstep Γ t = none) : trun (n + 1) Γ t = t := by
  simp only [trun, h]

/-- The traced step never lengthens the remaining trace. -/
theorem tstep_len {Γ : Core} {cf : Conf} {l : List Int} {t' : TConf}
    (h : tstep Γ (cf, l) = some t') : t'.2.length ≤ l.length := by
  by_cases hr : ∃ env stk, cf = (.eval .readInt env, stk)
  · obtain ⟨env, stk, rfl⟩ := hr
    cases l with
    | nil => simp [tstep] at h
    | cons v rest =>
        simp only [tstep] at h
        obtain rfl := Option.some.inj h
        simp
  · have hr' : ∀ env stk, cf ≠ (.eval .readInt env, stk) :=
      fun env stk hc => hr ⟨env, stk, hc⟩
    rw [tstep_not_readInt Γ hr'] at h
    cases hstep : step Γ cf with
    | none => rw [hstep] at h; simp at h
    | some cf' =>
        rw [hstep] at h
        rw [Option.map_some] at h
        obtain rfl := Option.some.inj h
        simp

/-- The traced step exposes the consumed input as a concrete prefix: the input
    `l` splits as a consumed part (`[]` or one popped integer) followed by the
    remaining trace of the next configuration. -/
theorem tstep_prefix {Γ : Core} {cf : Conf} {l : List Int} {t' : TConf}
    (h : tstep Γ (cf, l) = some t') : ∃ q, l = q ++ t'.2 := by
  by_cases hr : ∃ env stk, cf = (.eval .readInt env, stk)
  · obtain ⟨env, stk, rfl⟩ := hr
    cases l with
    | nil => simp [tstep] at h
    | cons v rest =>
        simp only [tstep] at h
        obtain rfl := Option.some.inj h
        exact ⟨[v], rfl⟩
  · have hr' : ∀ env stk, cf ≠ (.eval .readInt env, stk) :=
      fun env stk hc => hr ⟨env, stk, hc⟩
    rw [tstep_not_readInt Γ hr'] at h
    cases hstep : step Γ cf with
    | none => rw [hstep] at h; simp at h
    | some cf' =>
        rw [hstep] at h
        rw [Option.map_some] at h
        obtain rfl := Option.some.inj h
        exact ⟨[], rfl⟩

/-- The whole run never lengthens the trace: the leftover input is no longer
    than the input supplied. This rules out a `readInt` reading past the end of
    a shortened trace in `trun_strip`. -/
theorem trun_len_mono (Γ : Core) :
    ∀ (n : Nat) (cf : Conf) (l : List Int), (trun n Γ (cf, l)).2.length ≤ l.length := by
  intro n
  induction n with
  | zero => intro cf l; simp [trun]
  | succ n ih =>
      intro cf l
      cases hstep : tstep Γ (cf, l) with
      | none => rw [trun_succ_none hstep]; simp
      | some t' =>
          obtain ⟨cf', l'⟩ := t'
          rw [trun_succ_some hstep]
          exact Nat.le_trans (ih cf' l') (tstep_len hstep)

/-- The whole run exposes its consumed input as a concrete prefix: the supplied
    input `l` splits as a consumed prefix followed by the leftover trace. -/
theorem trun_prefix (Γ : Core) :
    ∀ (n : Nat) (cf : Conf) (l : List Int), ∃ p, l = p ++ (trun n Γ (cf, l)).2 := by
  intro n
  induction n with
  | zero => intro cf l; exact ⟨[], by simp [trun]⟩
  | succ n ih =>
      intro cf l
      cases hstep : tstep Γ (cf, l) with
      | none => exact ⟨[], by rw [trun_succ_none hstep]; simp⟩
      | some t' =>
          obtain ⟨cf', l'⟩ := t'
          rw [trun_succ_some hstep]
          obtain ⟨q, hq⟩ := tstep_prefix hstep
          obtain ⟨p, hp⟩ := ih cf' l'
          exact ⟨q ++ p, by rw [hq, List.append_assoc, ← hp]⟩

/-- LOCKSTEP / STRIP LEMMA. If the traced machine, run on input `p ++ s`,
    reaches configuration `m` with exactly `s` left over (so it consumed exactly
    `p`), then run on input `p` alone it reaches the same `m` with nothing left
    over. Equivalently: the unconsumed suffix is irrelevant to the run. -/
theorem trun_strip (Γ : Core) :
    ∀ (n : Nat) (cf : Conf) (p s : List Int) (m : Conf),
      trun n Γ (cf, p ++ s) = (m, s) → trun n Γ (cf, p) = (m, []) := by
  intro n
  induction n with
  | zero =>
      intro cf p s m h
      simp only [trun] at h ⊢
      rw [Prod.mk.injEq] at h
      obtain ⟨hcf, hps⟩ := h
      have hp : p = [] := by
        have hh := congrArg List.length hps
        simp only [List.length_append] at hh
        exact List.length_eq_zero_iff.mp (by omega)
      subst hp; subst hcf; rfl
  | succ n ih =>
      intro cf p s m h
      by_cases hr : ∃ env stk, cf = (.eval .readInt env, stk)
      · obtain ⟨env, stk, rfl⟩ := hr
        cases p with
        | nil =>
            rw [List.nil_append] at h
            cases s with
            | nil =>
                rw [trun_succ_none (by simp [tstep])] at h ⊢
                exact h
            | cons v s' =>
                have hstep : tstep Γ ((.eval .readInt env, stk), v :: s')
                    = some ((.ret (.int v), stk), s') := by simp [tstep]
                rw [trun_succ_some hstep] at h
                have hlen := trun_len_mono Γ n (.ret (.int v), stk) s'
                rw [h] at hlen
                simp at hlen
                exact absurd hlen (by omega)
        | cons v p' =>
            have hstep : tstep Γ ((.eval .readInt env, stk), (v :: p') ++ s)
                = some ((.ret (.int v), stk), p' ++ s) := by simp [tstep]
            rw [trun_succ_some hstep] at h
            have key := ih (.ret (.int v), stk) p' s m h
            have hstep2 : tstep Γ ((.eval .readInt env, stk), v :: p')
                = some ((.ret (.int v), stk), p') := by simp [tstep]
            rw [trun_succ_some hstep2]
            exact key
      · have hr : ∀ env stk, cf ≠ (.eval .readInt env, stk) :=
          fun env stk hc => hr ⟨env, stk, hc⟩
        cases hstep : step Γ cf with
        | none =>
            have ht : tstep Γ (cf, p ++ s) = none := by
              rw [tstep_not_readInt Γ hr, hstep]; rfl
            rw [trun_succ_none ht] at h
            rw [Prod.mk.injEq] at h
            obtain ⟨hcf, hps⟩ := h
            have hp : p = [] := by
              have hh := congrArg List.length hps
              simp only [List.length_append] at hh
              exact List.length_eq_zero_iff.mp (by omega)
            subst hp; subst hcf
            have ht0 : tstep Γ (cf, ([] : List Int)) = none := by
              rw [tstep_not_readInt Γ hr, hstep]; rfl
            rw [trun_succ_none ht0]
        | some cf' =>
            have ht : tstep Γ (cf, p ++ s) = some (cf', p ++ s) := by
              rw [tstep_not_readInt Γ hr, hstep]; rfl
            rw [trun_succ_some ht] at h
            have key := ih cf' p s m h
            have ht2 : tstep Γ (cf, p) = some (cf', p) := by
              rw [tstep_not_readInt Γ hr, hstep]; rfl
            rw [trun_succ_some ht2]
            exact key

/-- Load a closed computation and its input trace into an initial traced
    configuration. -/
def tload (c : Comp) (ins : List Int) : TConf := (load c, ins)

/-- The outcome of a recorded run: the final configuration the machine reached,
    the prefix of the input it actually consumed (the recorded trace), and the
    leftover input it never read. -/
structure Recorded where
  result : Conf
  trace : List Int
  leftover : List Int

/-- Run the traced machine on the full input `ins` for `fuel` steps and report
    the final configuration, the consumed prefix, and the leftover. -/
def record (fuel : Nat) (Γ : Core) (c : Comp) (ins : List Int) : Recorded :=
  let r := trun fuel Γ (tload c ins)
  { result := r.1, trace := ins.take (ins.length - r.2.length), leftover := r.2 }

/-- Run the traced machine on a supplied input trace `t` for `fuel` steps and
    report the final configuration. -/
def replay (fuel : Nat) (Γ : Core) (c : Comp) (t : List Int) : Conf :=
  (trun fuel Γ (tload c t)).1

/--
REPLAY FAITHFULNESS. Replaying exactly the inputs that `record` consumed
reproduces the configuration `record` reached. In words: the traced machine's
result depends only on the sequence of integers it actually reads from
`readInt`, so feeding it that sequence (and nothing more) lands in the same final
configuration. This is the record/replay contract for the Prism core, the one
genuinely nondeterministic input channel of which is `readInt`.
-/
theorem replay_faithful (fuel : Nat) (Γ : Core) (c : Comp) (ins : List Int) :
    replay fuel Γ c (record fuel Γ c ins).trace = (record fuel Γ c ins).result := by
  obtain ⟨p, hp⟩ := trun_prefix Γ fuel (load c) ins
  -- hp : ins = p ++ (trun fuel Γ (load c, ins)).2
  have hsplit : trun fuel Γ (load c, p ++ (trun fuel Γ (load c, ins)).2)
      = ((trun fuel Γ (load c, ins)).1, (trun fuel Γ (load c, ins)).2) := by
    rw [← hp]
  have hreplay := trun_strip Γ fuel (load c) p (trun fuel Γ (load c, ins)).2
                    (trun fuel Γ (load c, ins)).1 hsplit
  -- hreplay : trun fuel Γ (load c, p) = ((trun fuel Γ (load c, ins)).1, [])
  have hlen : ins.length = p.length + (trun fuel Γ (load c, ins)).2.length := by
    have hh := congrArg List.length hp
    simpa [List.length_append] using hh
  have hl : ins.length - (trun fuel Γ (load c, ins)).2.length = p.length := by omega
  have htrace : ins.take (ins.length - (trun fuel Γ (load c, ins)).2.length) = p := by
    rw [hl, hp]; simp
  simp only [replay, record, tload]
  rw [htrace, hreplay]

/--
Value-level corollary: when the recorded run terminated at a value
configuration `(.ret v, [])`, replaying the recorded inputs reaches the same
value. -/
theorem replay_faithful_value (fuel : Nat) (Γ : Core) (c : Comp) (ins : List Int) (v : Rv)
    (h : (record fuel Γ c ins).result = (.ret v, [])) :
    replay fuel Γ c (record fuel Γ c ins).trace = (.ret v, []) := by
  rw [replay_faithful, h]

end Prism
