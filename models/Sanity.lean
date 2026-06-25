import Prism

/-
Sanity examples for the Prism core model (`Prism.lean`): worked small-step
reductions plus determinism on a concrete redex. The deconstructors and lens
answer add no new core, so the examples below (lens update, the same
rebuild under FBIP `reuse`, and view-pattern lowering) discharge the whole of
the soundness obligation they carry. `lake build` checks every one.
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

end Prism
