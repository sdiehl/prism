import CEK

/-
Differential certificates: the kernel-checked half of the oracle. For each
curated program a `:= rfl` theorem proves the verified CEK model (`CEK.lean`)
evaluates it to exactly the value the live Rust interpreter printed for the
matching `models/fixtures/<name>.pr`, so every case is pinned three ways -- this
kernel proof, the runtime Lean oracle, and the Rust interpreter
(`diff_against_rust.sh`). The term below is the erased essence of each fixture;
its full `prism dump core-json` is committed as `models/fixtures/<name>.json`.

This is the load-bearing module. A passing `rfl` is a Lean *kernel* certificate
(no `native_decide`, no extra axioms) that the proven model and the compiler
agree on every program below. If it ever fails to compile, that is the rare red
build that is a mathematical event rather than a typo.
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
theorem inc : run 100 incΓ (load (.call "inc" [.int 41])) = output_inc := rfl
theorem mul : run 100 Γ0 (load (.prim .mul (.int 6) (.int 7))) = output_mul := rfl
theorem vec : run 100 Γ0 (load (.case (.ctor "Vec2" 0 [.int 3, .int 4])
  [(.ctor "Vec2" [.var "x", .var "y"], .ret (.ctor "Vec2" 0 [.int 9, .var "y"]))])) = output_vec := rfl
theorem tup : run 100 Γ0 (load (.ret (.tuple [.int 1, .int 2]))) = output_tup := rfl
theorem ite : run 100 Γ0 (load (.ite (.bool true) (.ret (.int 1)) (.ret (.int 2)))) = output_ite := rfl

-- Effect fragment: self-recursion, and handlers that resume once (ask), twice
-- (multishot), or discard the continuation entirely (abort).
theorem fact : run 500 factΓ (load (.call "fact" [.int 6])) = output_fact := rfl
theorem ask : run 500 Γ0 (load askBody) = output_ask := rfl
theorem multishot : run 500 Γ0 (load multishotBody) = output_multishot := rfl
theorem abort : run 500 Γ0 (load abortBody) = output_abort := rfl

end Prism.Cert
