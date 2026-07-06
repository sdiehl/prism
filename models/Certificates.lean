import CEK

/-
These are the kernel-checked fixture certificates. Each theorem says that the
Lean CEK machine evaluates the Core form of a fixture to the same result the Rust
interpreter produced.

The fixtures are recorded outside this file by source, generated `core-json`,
Core hash, and expected result. The theorem body is just `rfl`, which is the
point. If one of these stops compiling, the model and the compiler no longer
agree on that program.
-/
namespace Prism.Cert

-- Programs, as the erased essence of each fixture. `Γ0` is the empty function
-- environment, for the cases whose whole body is inlined into the query.
def Γ0 : Core := ⟨[]⟩

def incΓ : Core := ⟨[⟨"inc", ["n"], .prim .add (.var "n") (.int 1)⟩]⟩

def factΓ : Core := ⟨[⟨"fact", ["n"],
  .bind (.prim .le (.var "n") (.int 1)) "c"
    (.ite (.var "c")
      (.ret (.int 1))
      (.bind (.prim .sub (.var "n") (.int 1)) "m"
        (.bind (.call "fact" [.var "m"]) "r"
          (.prim .mul (.var "n") (.var "r")))))⟩]⟩

def askBody : Comp :=
  .handle
    (.bind (.doOp "ask" [.unit]) "x" (.prim .add (.var "x") (.int 1)))
    (some "x") (some (.ret (.var "x")))
    [.mk "ask" ["u"] "k" (.app (.ret (.var "k")) [.int 5])]

def multishotBody : Comp :=
  .handle
    (.bind (.doOp "coin" [.unit]) "x" (.ite (.var "x") (.ret (.int 1)) (.ret (.int 0))))
    (some "r") (some (.ret (.var "r")))
    [.mk "coin" ["u"] "k"
      (.bind (.app (.ret (.var "k")) [.bool true]) "a"
        (.bind (.app (.ret (.var "k")) [.bool false]) "b"
          (.prim .add (.var "a") (.var "b"))))]

def abortBody : Comp :=
  .handle
    (.bind (.doOp "abort" [.int 99]) "x" (.prim .add (.var "x") (.int 1)))
    (some "r") (some (.ret (.var "r")))
    [.mk "abort" ["code"] "k" (.ret (.var "code"))]

-- Expected outputs: exactly the value `prism run fixtures/<name>.pr` printed.
def output_inc : Conf := (.ret (.int 42), [])
def output_mul : Conf := (.ret (.int 42), [])
def output_vec : Conf := (.ret (.data "Vec2" 0 [.int 9, .int 4]), [])
def output_tup : Conf := (.ret (.tuple [.int 1, .int 2]), [])
def output_ite : Conf := (.ret (.int 1), [])
def output_fact : Conf := (.ret (.int 720), [])
def output_ask : Conf := (.ret (.int 6), [])
def output_multishot : Conf := (.ret (.int 1), [])
def output_abort : Conf := (.ret (.int 99), [])

-- Pure core: arithmetic, a called function, constructor + case, tuples, if.
/-- The checked `inc` example really runs to the recorded certificate output. -/
theorem inc : run 100 incΓ (load (.call "inc" [.int 41])) = output_inc := rfl
/-- The checked multiplication example really runs to the recorded output. -/
theorem mul : run 100 Γ0 (load (.prim .mul (.int 6) (.int 7))) = output_mul := rfl
/-- The checked vector-pattern example really runs to the recorded output. -/
theorem vec : run 100 Γ0 (load (.case (.ctor "Vec2" 0 [.int 3, .int 4])
  [(.ctor "Vec2" [.var "x", .var "y"], .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))])) = output_vec := rfl
/-- The checked tuple example really runs to the recorded output. -/
theorem tup : run 100 Γ0 (load (.ret (.tuple [.int 1, .int 2]))) = output_tup := rfl
/-- The checked conditional example really runs to the recorded output. -/
theorem ite : run 100 Γ0 (load (.ite (.bool true) (.ret (.int 1)) (.ret (.int 2)))) = output_ite := rfl

-- Effect fragment: self-recursion, and handlers that resume once (ask), twice
-- (multishot), or discard the continuation entirely (abort).
/-- The checked factorial example really runs to the recorded output. -/
theorem fact : run 500 factΓ (load (.call "fact" [.int 6])) = output_fact := rfl
/-- The checked single-shot handler example really runs to the recorded output. -/
theorem ask : run 500 Γ0 (load askBody) = output_ask := rfl
/-- The checked multishot handler example really runs to the recorded output. -/
theorem multishot : run 500 Γ0 (load multishotBody) = output_multishot := rfl
/-- The checked aborting handler example really runs to the recorded output. -/
theorem abort : run 500 Γ0 (load abortBody) = output_abort := rfl

end Prism.Cert
