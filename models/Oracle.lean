import Prism
import CEK
import Dynamics
import Meta

/-
Executable demonstration + example module for the Prism core model. This is the
ONLY module that carries `example`s and `main`; the proof libraries (`Prism`,
`CEK`, `Dynamics`, `Meta`) stay free of ad-hoc examples and IO. It is built as a
`lake exe oracle` that runs the CEK machine on a handful of programs and prints
their results, so the same definitions that the `example`s certify by `rfl` are
also runnable end to end.

The examples fall in two groups:
* substitution small-step (`Prism.lean`): worked reductions and determinism;
* the expanded model: CEK oracle runs that agree with the substitution answers
  by `rfl`, the big-step spec driving the machine via `bigstep_runs`, the effect
  metatheory deciding handled vs unhandled operations, and the `Meta` progress /
  unique-normal-form classification on concrete terms.
-/

namespace Prism

def emptyΓ : Core := ⟨[]⟩
def incΓ : Core := ⟨[⟨"inc", ["n"], .prim .add (.var "n") (.int 1)⟩]⟩
def viewΓ : Core :=
  ⟨[⟨"view@First", ["c"],
      .case (.var "c") [(.ctor "Box" [.var "v"], .ret (.ctor "Some" 0 [.var "v"]))]⟩]⟩

-- Programs reused by both the `example` certificates and `main`.
def incCall : Comp := .call "inc" [.int 41]
def betaProg : Comp := .app (.lam ["x"] (.ret (.var "x"))) [.int 7]
def vecProg : Comp :=
  .case (.ctor "Vec2" 0 [.int 3, .int 4])
        [(.ctor "Vec2" [.var "x", .var "y"], .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))]
def viewProg : Comp :=
  .bind (.call "view@First" [.ctor "Box" 0 [.int 7]]) "r"
        (.case (.var "r") [(.ctor "Some" [.var "n"], .ret (.var "n")),
                           (.wild, .ret (.int 0))])
-- `handle (do ask) with { ask() => resume 5; return x => x }`
def askProg : Comp :=
  .handle (.doOp "ask" []) (some "x") (some (.ret (.var "x")))
          [.mk "ask" [] "k" (.app (.ret (.var "k")) [.int 5])]
-- abort handler: never resumes, discards its continuation.
def abortProg : Comp :=
  .handle (.doOp "abort" []) none none [.mk "abort" [] "k" (.ret (.int 0))]
-- multishot: `flip` resumes twice (true then false) and sums the results.
def flipProg : Comp :=
  .handle
    (.bind (.doOp "flip" []) "x" (.ite (.var "x") (.ret (.int 1)) (.ret (.int 0))))
    (some "r") (some (.ret (.var "r")))
    [.mk "flip" [] "k"
        (.bind (.app (.ret (.var "k")) [.bool true]) "a"
          (.bind (.app (.ret (.var "k")) [.bool false]) "b"
            (.prim .add (.var "a") (.var "b"))))]

/- ===== Substitution small-step semantics (Prism.lean) ===== -/

example : delta .add (.int 1) (.int 2) = some (.int 3) := rfl
example : delta .div (.int 7) (.int 0) = none := rfl

example : Step emptyΓ (.force (.thunk (.ret .unit))) (.ret .unit) := .forceThunk
example : Step emptyΓ (.ite (.bool true) (.ret (.int 1)) (.ret (.int 2))) (.ret (.int 1)) := .ifTrue
example : Step emptyΓ (.prim .add (.int 2) (.int 3)) (.ret (.int 5)) := .prim rfl

example : Steps emptyΓ betaProg (.ret (.int 7)) := .head .beta .refl

example : Steps incΓ incCall (.ret (.int 42)) :=
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

-- s3 lens update: destructure the record (a `ctor`) and rebuild with `x` replaced.
example : Steps emptyΓ vecProg (.ret (.ctor "Vec2" 0 [.int 9, .int 4])) :=
  .head (.caseMatch rfl) .refl

-- The same rebuild under FBIP `reuse` of the matched cell.
example :
    Steps emptyΓ
      (.case (.ctor "Vec2" 0 [.int 3, .int 4])
             [(.ctor "Vec2" [.var "x", .var "y"],
               .reuse "tok" (.ctor "Vec2" 0 [.int 9, .var "y"]))])
      (.ret (.ctor "Vec2" 0 [.int 9, .int 4])) :=
  .head (.caseMatch rfl) (.head .reuseStep .refl)

-- View-pattern lowering: a `call` to the synthesized view then a `case` on its result.
example : Steps viewΓ viewProg (.ret (.int 7)) :=
  .head (.bindCong (.call rfl))
    (.head (.bindCong (.caseMatch rfl))
      (.head .bindRet
        (.head (.caseMatch rfl) .refl)))

/- ===== CEK oracle: executable agreement with the substitution semantics ===== -/

example : run 20 incΓ (load incCall) = (.ret (.int 42), []) := rfl
example : run 20 emptyΓ (load betaProg) = (.ret (.int 7), []) := rfl
example : run 20 emptyΓ (load vecProg) = (.ret (.data "Vec2" 0 [.int 9, .int 4]), []) := rfl
example : run 20 viewΓ (load viewProg) = (.ret (.int 7), []) := rfl

/- ===== Algebraic effects on the machine (deep handlers, multishot) ===== -/

example : run 30 emptyΓ (load askProg) = (.ret (.int 5), []) := rfl
example : run 30 emptyΓ (load abortProg) = (.ret (.int 0), []) := rfl
example : run 60 emptyΓ (load flipProg) = (.ret (.int 1), []) := rfl

/- ===== Big-step spec drives the machine (forward simulation / adequacy) ===== -/

example : Runs incΓ (load incCall) (.ret (.int 42), []) :=
  load_runs (.callFull rfl rfl (by decide) (.prim rfl rfl rfl))

/- ===== Effect metatheory: handled vs unhandled (Dynamics.lean) ===== -/

def askStk : Stack := [.handle [.mk "ask" [] "k" (.ret (.int 5))] none none []]

example : (findHandler "ask" [] 0 [] askStk).isSome :=
  effect_progress (.here _ _ _ _ _ (by simp [handlerFor])) []

example : findHandler "ask" [] 0 [] [] = none :=
  effect_unhandled (by intro h; cases h) []

/- ===== Substitution metatheory on concrete terms (Meta.lean) ===== -/

-- Progress pins `prim add true 1` (closed, ill-typed) as `Stuck`, not silently stuck.
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

/- ===== Executable entry point: run the CEK oracle and print results ===== -/

mutual
  def showRv : Rv → String
    | .int n => toString n
    | .float f => toString f
    | .bool b => toString b
    | .unit => "()"
    | .str s => "\"" ++ s ++ "\""
    | .closure _ _ _ => "<closure>"
    | .thunk _ _ => "<thunk>"
    | .data n _ args => n ++ "(" ++ showRvs args ++ ")"
    | .tuple args => "(" ++ showRvs args ++ ")"
    | .resume _ => "<resume>"
  def showRvs : List Rv → String
    | [] => ""
    | [x] => showRv x
    | x :: xs => showRv x ++ ", " ++ showRvs xs
end

def showState : MState → String
  | .ret w => showRv w
  | .eval _ _ => "<stuck>"

/-- Run a program for a fuel budget and render its final value. -/
def eval (Γ : Core) (fuel : Nat) (c : Comp) : String :=
  showState (run fuel Γ (load c)).1

def cases : List (String × Core × Comp) :=
  [ ("inc 41",          incΓ,    incCall),
    ("(\\x. x) 7",       emptyΓ,  betaProg),
    ("Vec2 lens { x=9 }", emptyΓ, vecProg),
    ("view@First",       viewΓ,   viewProg),
    ("handle ask=>5",    emptyΓ,  askProg),
    ("handle abort",     emptyΓ,  abortProg),
    ("flip (multishot)", emptyΓ,  flipProg) ]

def run! : IO Unit := do
  IO.println "Prism CEK oracle"
  for (name, Γ, prog) in cases do
    IO.println s!"  {name}  =>  {eval Γ 200 prog}"

end Prism

def main : IO Unit := Prism.run!
