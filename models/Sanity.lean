import Prism
import CEK
import Dynamics
import Meta

/-
Sanity examples for the Prism core model (`Prism.lean`): worked small-step
reductions plus determinism on a concrete redex. The deconstructors and lens
answer add no new core, so the examples below (lens update, the same
rebuild under FBIP `reuse`, and view-pattern lowering) discharge the whole of
the soundness obligation they carry. `lake build` checks every one.

The second half (`CEK`/effects/metatheory) checks the expanded model: the CEK
oracle (`CEK.lean`) runs the same programs and reaches the same answers by `rfl`
(executable oracle agreement), the big-step spec drives the machine through
`bigstep_runs`, the effect metatheory (`Dynamics.lean`) decides handled vs
unhandled operations, and the substitution metatheory (`Meta.lean`) classifies
and uniquely-normalizes concrete terms.
-/

namespace Prism

def emptyΓ : Core := ⟨[]⟩

example : delta .add (.int 1) (.int 2) = some (.int 3) := rfl
example : delta .div (.int 7) (.int 0) = none := rfl

example : Step emptyΓ (.force (.thunk (.ret .unit))) (.ret .unit) := .forceThunk
example : Step emptyΓ (.ite (.bool true) (.ret (.int 1)) (.ret (.int 2))) (.ret (.int 1)) := .ifTrue
example : Step emptyΓ (.prim .add (.int 2) (.int 3)) (.ret (.int 5)) := .prim rfl

example :
    Steps emptyΓ (.app (.lam ["x"] (.ret (.var "x"))) [.int 7]) (.ret (.int 7)) :=
  .head .beta .refl

def incΓ : Core := ⟨[⟨"inc", ["n"], .prim .add (.var "n") (.int 1)⟩]⟩

example : Steps incΓ (.call "inc" [.int 41]) (.ret (.int 42)) :=
  .head (.call rfl) (.head (.prim rfl) .refl)

example :
    Steps emptyΓ
      (.case (.ctor "Some" 0 [.int 9]) [(.ctor "Some" [.var "y"], .ret (.var "y")),
                                        (.wild, .ret (.int 0))])
      (.ret (.int 9)) :=
  .head (.caseMatch rfl) .refl

example : Step emptyΓ (.drop (.int 7)) (.ret .unit) := .dropStep
example : Step emptyΓ (.reuse "tok" (.ctor "Cons" 0 [.int 1, .unit])) (.ret (.ctor "Cons" 0 [.int 1, .unit])) :=
  .reuseStep

example {b c : Comp} (h1 : Step emptyΓ (.prim .add (.int 2) (.int 3)) b)
    (h2 : Step emptyΓ (.prim .add (.int 2) (.int 3)) c) : b = c :=
  Step.deterministic h1 h2

-- s3 lens update: `{ v | x = 9 }` on `Vec2 { x = 3, y = 4 }` destructures the
-- record (a `ctor`) and rebuilds it with `x` replaced and `y` carried through
-- from the match. This is the whole nested-update primitive at one level.
example :
    Steps emptyΓ
      (.case (.ctor "Vec2" 0 [.int 3, .int 4])
             [(.ctor "Vec2" [.var "x", .var "y"],
               .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))])
      (.ret (.ctor "Vec2" 0 [.int 9, .int 4])) :=
  .head (.caseMatch rfl) .refl

-- The same rebuild under FBIP: a uniquely owned spine rebuilds by `reuse` of
-- the matched cell, which preserves the value (the pitch: a functional update
-- that compiles to a pointer write).
example :
    Steps emptyΓ
      (.case (.ctor "Vec2" 0 [.int 3, .int 4])
             [(.ctor "Vec2" [.var "x", .var "y"],
               .reuse "tok" (.ctor "Vec2" 0 [.int 9, .var "y"]))])
      (.ret (.ctor "Vec2" 0 [.int 9, .int 4])) :=
  .head (.caseMatch rfl) (.head .reuseStep .refl)

-- View-pattern lowering, shared by view/make and class-dispatched patterns:
-- `match b of First(n) => n; _ => 0` becomes a `call` to the synthesized view
-- then a `case` on its `Option` result. `view@First` here deconstructs a `Box`.
def viewΓ : Core :=
  ⟨[⟨"view@First", ["c"],
      .case (.var "c") [(.ctor "Box" [.var "v"], .ret (.ctor "Some" 0 [.var "v"]))]⟩]⟩

example :
    Steps viewΓ
      (.bind (.call "view@First" [.ctor "Box" 0 [.int 7]]) "r"
             (.case (.var "r") [(.ctor "Some" [.var "n"], .ret (.var "n")),
                                (.wild, .ret (.int 0))]))
      (.ret (.int 7)) :=
  .head (.bindCong (.call rfl))
    (.head (.bindCong (.caseMatch rfl))
      (.head .bindRet
        (.head (.caseMatch rfl) .refl)))

/- ===== CEK oracle: executable agreement with the substitution semantics ===== -/

-- The CEK machine runs `inc 41` to the same answer the substitution semantics
-- normalizes it to (cf. the `incΓ` example above), checked by computation.
example : run 20 incΓ (load (.call "inc" [.int 41])) = (.ret (.int 42), []) := rfl

-- Pure beta, matching the substitution `Steps` example.
example :
    run 20 emptyΓ (load (.app (.lam ["x"] (.ret (.var "x"))) [.int 7])) = (.ret (.int 7), []) := rfl

-- The s3 lens update under the CEK machine: same rebuilt record as the
-- substitution `case` example, now as a runtime `data` value.
example :
    run 20 emptyΓ
      (load (.case (.ctor "Vec2" 0 [.int 3, .int 4])
                   [(.ctor "Vec2" [.var "x", .var "y"],
                     .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))]))
      = (.ret (.data "Vec2" 0 [.int 9, .int 4]), []) := rfl

-- View-pattern lowering on the machine: same final value as the substitution run.
example :
    run 20 viewΓ
      (load (.bind (.call "view@First" [.ctor "Box" 0 [.int 7]]) "r"
                   (.case (.var "r") [(.ctor "Some" [.var "n"], .ret (.var "n")),
                                      (.wild, .ret (.int 0))])))
      = (.ret (.int 7), []) := rfl

/- ===== Algebraic effects on the machine (deep handlers, mask, multishot) ===== -/

-- A handler that resumes once: `handle (do ask) with { ask() => resume 5; return x => x }`.
example :
    run 30 emptyΓ
      (load (.handle (.doOp "ask" []) (some "x") (some (.ret (.var "x")))
                     [.mk "ask" [] "k" (.app (.ret (.var "k")) [.int 5])]))
      = (.ret (.int 5), []) := rfl

-- An abort handler that never resumes discards its continuation: result is 0.
example :
    run 30 emptyΓ
      (load (.handle (.doOp "abort" []) none none [.mk "abort" [] "k" (.ret (.int 0))]))
      = (.ret (.int 0), []) := rfl

-- A multishot handler invokes `resume` twice (true then false) and sums the two
-- continuation results: `flip` yields 1 on `true` and 0 on `false`, summing to 1.
-- This exercises deep, multishot continuation capture.
example :
    run 60 emptyΓ
      (load (.handle
              (.bind (.doOp "flip" []) "x" (.ite (.var "x") (.ret (.int 1)) (.ret (.int 0))))
              (some "r") (some (.ret (.var "r")))
              [.mk "flip" [] "k"
                  (.bind (.app (.ret (.var "k")) [.bool true]) "a"
                    (.bind (.app (.ret (.var "k")) [.bool false]) "b"
                      (.prim .add (.var "a") (.var "b"))))]))
      = (.ret (.int 1), []) := rfl

/- ===== Big-step spec drives the machine (forward simulation / adequacy) ===== -/

-- A big-step derivation of `inc 41`, fed through `load_runs` to obtain an actual
-- machine run -- the natural-semantics spec and the CEK oracle agree by theorem.
example : Runs incΓ (load (.call "inc" [.int 41])) (.ret (.int 42), []) :=
  load_runs (.callFull rfl rfl (by decide) (.prim rfl rfl rfl))

/- ===== Effect metatheory: handled vs unhandled (Dynamics.lean) ===== -/

def askStk : Stack := [.handle [.mk "ask" [] "k" (.ret (.int 5))] none none []]

-- `ask` is handled in `askStk`, so `perform` makes progress (never stuck).
example : (findHandler "ask" [] 0 [] askStk).isSome :=
  effect_progress (.here _ _ _ _ _ (by simp [handlerFor])) []

-- With nothing in scope, `perform` is stuck: the unhandled-effect error.
example : findHandler "ask" [] 0 [] [] = none :=
  effect_unhandled (by intro h; cases h) []

/- ===== Substitution metatheory on concrete terms (Meta.lean) ===== -/

-- Progress: `prim add true 1` is closed but ill-typed, and the classification
-- pins it as `Stuck` (no silent stuckness) rather than terminal or stepping.
example : Stuck emptyΓ (.prim .add (.bool true) (.int 1)) := by
  rcases progress emptyΓ (.prim .add (.bool true) (.int 1)) with t | ⟨_, hs⟩ | s
  · exact t.elim
  · cases hs with | prim hd => simp [delta] at hd
  · exact s

-- Unique normal form on a concrete redex: at most one terminal answer.
example {m n : Comp}
    (hm : Steps emptyΓ (.prim .add (.int 2) (.int 3)) m)
    (hn : Steps emptyΓ (.prim .add (.int 2) (.int 3)) n)
    (tm : Terminal m) (tn : Terminal n) : m = n :=
  Steps.unique_normal hm hn tm tn

end Prism
