import Prism
import CEK
import Dynamics
import Meta
import Json

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

/- ===== Rendering: match the Rust interpreter's `Rv::show` byte for byte ===== -/

private def stripTrailing (s : String) : String :=
  if s.any (· == '.') then
    String.ofList (s.toList.reverse.dropWhile (· == '0') |>.dropWhile (· == '.')).reverse
  else s

/-- Render a `Float` exactly as the runtime's `fmt_g` (C `printf` `%g`, 6 significant
    digits, round-half-to-even). Computed from the IEEE bits via exact big-integer
    arithmetic, so it is byte-identical to `prism run`'s float output. -/
def fmtG (d : Float) : String :=
  let bits := d.toBits
  let neg := (bits >>> 63) == 1
  let expBits := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if expBits == 0x7FF then
    (if frac == 0 then (if neg then "-inf" else "inf") else "nan")
  else
    let M : Nat := if expBits == 0 then frac else frac + 2 ^ 52
    if M == 0 then (if neg then "-0" else "0")
    else
      let E : Int := if expBits == 0 then -1074 else (expBits : Int) - 1075
      -- exact value = M * 2^E = num / 10^scale
      let num : Nat := if E ≥ 0 then M * 2 ^ E.toNat else M * 5 ^ (-E).toNat
      let scale : Nat := if E ≥ 0 then 0 else (-E).toNat
      let e10₀ : Int := ((toString num).length : Int) - 1 - (scale : Int)
      let q : Int := (scale : Int) - (6 - 1 - e10₀)
      let R₀ : Nat :=
        if q ≤ 0 then num * 10 ^ (-q).toNat
        else
          let p10 := 10 ^ q.toNat
          let quot := num / p10
          let rem := num % p10
          let half := p10 / 2
          if rem < half then quot
          else if rem > half then quot + 1
          else (if quot % 2 == 0 then quot else quot + 1)
      -- a rounding carry can bump to 7 digits (e.g. 999999.6 -> 1000000): renormalize
      let (R, e10) := if (toString R₀).length > 6 then (R₀ / 10, e10₀ + 1) else (R₀, e10₀)
      let digs : List Char := (toString R).toList
      let body :=
        if (-4 : Int) ≤ e10 ∧ e10 < 6 then
          if e10 ≥ 0 then
            let intPart := String.ofList (digs.take (e10 + 1).toNat)
            let fracPart := String.ofList (digs.drop (e10 + 1).toNat)
            stripTrailing (if fracPart == "" then intPart else intPart ++ "." ++ fracPart)
          else
            let zeros := String.ofList (List.replicate ((-e10).toNat - 1) '0')
            stripTrailing ("0." ++ zeros ++ String.ofList digs)
        else
          let mant := stripTrailing (String.ofList (digs.take 1) ++ "." ++ String.ofList (digs.drop 1))
          let estr := if e10.natAbs < 10 then "0" ++ toString e10.natAbs else toString e10.natAbs
          mant ++ "e" ++ (if e10 < 0 then "-" else "+") ++ estr
      (if neg then "-" else "") ++ body

mutual
  def showRv : Rv → String
    | .int n => toString n
    | .float f => fmtG f
    | .bool b => toString b
    | .unit => "()"
    | .str s => s
    | .closure _ _ _ => "<function>"
    | .thunk _ _ => "<function>"
    | .data n _ [] => n
    | .data n _ args => n ++ "(" ++ showRvs args ++ ")"
    | .tuple args => "(" ++ showRvs args ++ ")"
    | .resume _ => "<continuation>"
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

/- ===== JSON core-IR bridge endpoint =====
   Decode a `prism dump core-json` program (via `Json.lean`) and run its `main`,
   exactly as the interpreter does (`eval::run_io` evaluates the `main` function).
   This is the differential endpoint: feed it the same core the Rust interpreter
   runs and compare the rendered value. -/

/-- Evaluate the `main` function of a decoded core program. -/
def evalMain (Γ : Core) : String := eval Γ 100000 (.call "main" [])

def evalCoreJson (src : String) : Except String String :=
  Json.coreOfJson src |>.map evalMain

/- ===== Executable entry point ===== -/

def cases : List (String × Core × Comp) :=
  [ ("inc 41",          incΓ,    incCall),
    ("(\\x. x) 7",       emptyΓ,  betaProg),
    ("Vec2 lens { x=9 }", emptyΓ, vecProg),
    ("view@First",       viewΓ,   viewProg),
    ("handle ask=>5",    emptyΓ,  askProg),
    ("handle abort",     emptyΓ,  abortProg),
    ("flip (multishot)", emptyΓ,  flipProg) ]

def demo : IO Unit := do
  IO.println "Prism CEK oracle"
  for (name, Γ, prog) in cases do
    IO.println s!"  {name}  =>  {eval Γ 200 prog}"

end Prism

def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["eval", file] =>
      let src ← if file = "-" then (← IO.getStdin).readToEnd else IO.FS.readFile file
      match Prism.evalCoreJson src with
      | .ok v => IO.println v; return 0
      | .error e => IO.eprintln s!"oracle: {e}"; return 1
  | [] => Prism.demo; return 0
  | _ => IO.eprintln "usage: oracle [eval <file.json|->]"; return 1
