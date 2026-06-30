import CEK

/-
Differential certificates (the non-probabilistic, kernel-checked half of the
oracle). For each curated program, a `:= rfl` theorem proves that the
formally-verified CEK model (`CEK.lean`) evaluates it to *exactly* the value the
LIVE Rust interpreter produced -- the `=> ...` printed by `prism run` on the
matching `models/fixtures/<name>.pr` (see `diff_against_rust.sh`). Each program
here encodes the identical core IR as `models/fixtures/<name>.json`, so the same
case is checked three ways: kernel proof (here), the runtime Lean oracle, and the
runtime Rust interpreter.

The `rfl` is a Lean *kernel* certificate -- no `native_decide`, no extra axioms --
so a passing build is a machine-checked proof that the proven model agrees with
the recorded oracle output on every program below.
-/
namespace Prism.Cert

def incΓ : Core := ⟨[⟨"inc", ["n"], .prim .add (.var "n") (.int 1)⟩]⟩

def Γ0 : Core := ⟨[]⟩

-- prism run fixtures/inc.pr  =>  42
theorem inc : run 100 incΓ (load (.call "inc" [.int 41])) = (.ret (.int 42), []) := rfl

-- prism run fixtures/mul.pr  =>  42
theorem mul : run 100 Γ0 (load (.prim .mul (.int 6) (.int 7))) = (.ret (.int 42), []) := rfl

-- prism run fixtures/vec.pr  =>  Vec2(9, 4)
theorem vec : run 100 Γ0 (load (.case (.ctor "Vec2" 0 [.int 3, .int 4]) [(.ctor "Vec2" [.var "x", .var "y"], .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))])) = (.ret (.data "Vec2" 0 [.int 9, .int 4]), []) :=
  rfl

-- prism run fixtures/tup.pr  =>  (1, 2)
theorem tup : run 100 Γ0 (load (.ret (.tuple [.int 1, .int 2]))) = (.ret (.tuple [.int 1, .int 2]), []) :=
  rfl

-- prism run fixtures/ite.pr  =>  1
theorem ite : run 100 Γ0 (load (.ite (.bool true) (.ret (.int 1)) (.ret (.int 2)))) = (.ret (.int 1), []) :=
  rfl

end Prism.Cert
