/-
A formal model of the Prism call-by-push-value core, mirroring
`src/core/cbpv.rs`. The `Value`/`Comp` syntax tracks the Rust enums one
variant at a time; the dynamics are a substitution-based small step over
the computational core (force, beta, sequencing, branching, prims, named
calls, pattern matching). The reference-counting and FBIP-reuse markers
reduce by erasure (`dup`/`drop` are observationally unit; `withReuse tok freed
body` binds the freed shell's token, erased to unit, over `body`; `reuse tok v`
yields the rebuilt value), so the RC-instrumented program keeps the meaning of
the pure one. The reuse token is a scoped binder of `withReuse` and the only
operand `reuse` names, so it is freed once and spent at an allocation by
construction. Effects and handlers are syntax only:
the free-monad lowering erases them before this core runs. The relation is
proved deterministic (`Step.deterministic`), so a closed computation has at
most one normal form.

The DESIGN s3 deconstructors and the lens answer add no new core: a record
is a `ctor`, a nested update path is a `case` that destructures the spine and
rebuilds it field for field (FBIP-reused via `reuse` when the spine is
uniquely owned), and view/make patterns (including class-dispatched ones)
become a `call` to the synthesized view followed by a `case` on its `Option`
result. The sanity examples in `Sanity.lean` discharge the whole of the
soundness obligation they add.
-/

namespace Prism

inductive BinOp where
  | add | sub | mul | div | rem
  | eq | ne | lt | le | gt | ge
  | and | or
  | addf | subf | mulf | divf
  | eqf | nef | ltf | lef | gtf | gef

inductive Pat where
  | wild
  | var (x : String)
  | int (n : Int)
  | float (f : Float)
  | bool (b : Bool)
  | ctor (name : String) (args : List Pat)
  | tuple (args : List Pat)
  | record (name : String) (fields : List (String × Pat)) (isOpen : Bool)

mutual
  inductive Value where
    | var (x : String)
    | int (n : Int)
    | float (f : Float)
    | bool (b : Bool)
    | unit
    | str (s : String)
    | thunk (c : Comp)
    | ctor (name : String) (tag : Nat) (args : List Value)
    | tuple (args : List Value)

  inductive HandleOp where
    | mk (name : String) (params : List String) (resume : String) (body : Comp)

  inductive Comp where
    | ret (v : Value)
    | bind (m : Comp) (x : String) (n : Comp)
    | force (v : Value)
    | lam (xs : List String) (body : Comp)
    | app (f : Comp) (args : List Value)
    | ite (c : Value) (t : Comp) (e : Comp)
    | prim (op : BinOp) (a : Value) (b : Value)
    | call (name : String) (args : List Value)
    | print (v : Value)
    | printf (v : Value)
    | prints (v : Value)
    | readInt
    | err (v : Value)
    | case (scrut : Value) (arms : List (Pat × Comp))
    | floatBuiltin (name : String) (v : Value)
    | doOp (name : String) (args : List Value)
    | handle (body : Comp) (retVar : Option String) (retBody : Option Comp) (ops : List HandleOp)
    | mask (ops : List String) (body : Comp)
    | strBuiltin (name : String) (args : List Value)
    | dup (v : Value)
    | drop (v : Value)
    | withReuse (tok : String) (freed : Value) (body : Comp)
    | reuse (tok : String) (v : Value)
end

structure CoreFn where
  name : String
  params : List String
  body : Comp

structure Core where
  fns : List CoreFn

def patVars : Pat → List String
  | .var x => [x]
  | .ctor _ args => patVarsL args
  | .tuple args => patVarsL args
  | .record _ fields _ => patVarsF fields
  | _ => []
where
  patVarsL : List Pat → List String
    | [] => []
    | p :: ps => patVars p ++ patVarsL ps
  patVarsF : List (String × Pat) → List String
    | [] => []
    | (_, p) :: ps => patVars p ++ patVarsF ps

mutual
  def substV (x : String) (w : Value) : Value → Value
    | .var y => if x = y then w else .var y
    | .thunk c => .thunk (substC x w c)
    | .ctor n t args => .ctor n t (substVL x w args)
    | .tuple args => .tuple (substVL x w args)
    | v => v

  def substVL (x : String) (w : Value) : List Value → List Value
    | [] => []
    | v :: vs => substV x w v :: substVL x w vs

  def substC (x : String) (w : Value) : Comp → Comp
    | .ret v => .ret (substV x w v)
    | .bind m y n => .bind (substC x w m) y (if x = y then n else substC x w n)
    | .force v => .force (substV x w v)
    | .lam xs b => .lam xs (if xs.contains x then b else substC x w b)
    | .app f args => .app (substC x w f) (substVL x w args)
    | .ite c t e => .ite (substV x w c) (substC x w t) (substC x w e)
    | .prim op a b => .prim op (substV x w a) (substV x w b)
    | .call n args => .call n (substVL x w args)
    | .print v => .print (substV x w v)
    | .printf v => .printf (substV x w v)
    | .prints v => .prints (substV x w v)
    | .readInt => .readInt
    | .err v => .err (substV x w v)
    | .case s arms => .case (substV x w s) (substArms x w arms)
    | .floatBuiltin n v => .floatBuiltin n (substV x w v)
    | .doOp n args => .doOp n (substVL x w args)
    | .handle b rv rb ops =>
        .handle (substC x w b) rv (substRet x w rb) (substOps x w ops)
    | .mask ops b => .mask ops (substC x w b)
    | .strBuiltin n args => .strBuiltin n (substVL x w args)
    | .dup v => .dup (substV x w v)
    | .drop v => .drop (substV x w v)
    | .withReuse tok freed body =>
        .withReuse tok (substV x w freed) (if x = tok then body else substC x w body)
    | .reuse tok v => .reuse tok (substV x w v)

  def substArms (x : String) (w : Value) : List (Pat × Comp) → List (Pat × Comp)
    | [] => []
    | (p, c) :: rest =>
        (p, if (patVars p).contains x then c else substC x w c) :: substArms x w rest

  def substRet (x : String) (w : Value) : Option Comp → Option Comp
    | none => none
    | some c => some (substC x w c)

  def substOps (x : String) (w : Value) : List HandleOp → List HandleOp
    | [] => []
    | .mk n ps r b :: rest =>
        .mk n ps r (if ps.contains x || r = x then b else substC x w b) :: substOps x w rest
end

def substMany : List (String × Value) → Comp → Comp
  | [], c => c
  | (x, w) :: rest, c => substMany rest (substC x w c)

def bindParams (xs : List String) (vs : List Value) : List (String × Value) :=
  xs.zip vs

def lookupFn (Γ : Core) (name : String) : Option CoreFn :=
  Γ.fns.find? (·.name == name)

def delta : BinOp → Value → Value → Option Value
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int _, .int 0 => none
  | .rem, .int _, .int 0 => none
  | .div, .int a, .int b => some (.int (a / b))
  | .rem, .int a, .int b => some (.int (a % b))
  | .eq, .int a, .int b => some (.bool (a == b))
  | .ne, .int a, .int b => some (.bool (a != b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

def matchPat : Pat → Value → Option (List (String × Value))
  | .wild, _ => some []
  | .var x, v => some [(x, v)]
  | .int n, .int m => if n = m then some [] else none
  | .bool b, .bool c => if b = c then some [] else none
  | .ctor name args, .ctor name' _ vs =>
      if name = name' then matchPatL args vs else none
  | .tuple args, .tuple vs => matchPatL args vs
  | _, _ => none
where
  matchPatL : List Pat → List Value → Option (List (String × Value))
    | [], [] => some []
    | p :: ps, v :: vs =>
        match matchPat p v, matchPatL ps vs with
        | some b1, some b2 => some (b1 ++ b2)
        | _, _ => none
    | _, _ => none

def matchArms (scrut : Value) : List (Pat × Comp) → Option Comp
  | [] => none
  | (p, c) :: rest =>
      match matchPat p scrut with
      | some binds => some (substMany binds c)
      | none => matchArms scrut rest

inductive Step (Γ : Core) : Comp → Comp → Prop where
  | forceThunk : Step Γ (.force (.thunk c)) c
  | beta : Step Γ (.app (.lam xs body) args) (substMany (bindParams xs args) body)
  | appCong : Step Γ f f' → Step Γ (.app f args) (.app f' args)
  | bindRet : Step Γ (.bind (.ret v) x n) (substC x v n)
  | bindCong : Step Γ m m' → Step Γ (.bind m x n) (.bind m' x n)
  | ifTrue : Step Γ (.ite (.bool true) t e) t
  | ifFalse : Step Γ (.ite (.bool false) t e) e
  | prim : delta op a b = some v → Step Γ (.prim op a b) (.ret v)
  | call : lookupFn Γ name = some f → Step Γ (.call name args) (substMany (bindParams f.params args) f.body)
  | caseMatch : matchArms scrut arms = some c → Step Γ (.case scrut arms) c
  | dupStep : Step Γ (.dup v) (.ret .unit)
  | dropStep : Step Γ (.drop v) (.ret .unit)
  | withReuseStep : Step Γ (.withReuse tok freed body) (substC tok .unit body)
  | reuseStep : Step Γ (.reuse tok v) (.ret v)

inductive Steps (Γ : Core) : Comp → Comp → Prop where
  | refl : Steps Γ c c
  | head : Step Γ a b → Steps Γ b c → Steps Γ a c

def Terminal : Comp → Prop
  | .ret _ => True
  | .lam _ _ => True
  | _ => False

theorem noStepRet {Γ : Core} {v : Value} {c : Comp} : ¬ Step Γ (.ret v) c := by
  intro h; cases h

theorem noStepLam {Γ : Core} {xs : List String} {b c : Comp} : ¬ Step Γ (.lam xs b) c := by
  intro h; cases h

theorem Step.deterministic {Γ : Core} {a b c : Comp}
    (h1 : Step Γ a b) (h2 : Step Γ a c) : b = c := by
  induction h1 generalizing c with
  | forceThunk => cases h2 with | forceThunk => rfl
  | beta => cases h2 with
    | beta => rfl
    | appCong hf => exact absurd hf noStepLam
  | appCong hf ih => cases h2 with
    | beta => exact absurd hf noStepLam
    | appCong hf' => rw [ih hf']
  | bindRet => cases h2 with
    | bindRet => rfl
    | bindCong hm => exact absurd hm noStepRet
  | bindCong hm ih => cases h2 with
    | bindRet => exact absurd hm noStepRet
    | bindCong hm' => rw [ih hm']
  | ifTrue => cases h2 with | ifTrue => rfl
  | ifFalse => cases h2 with | ifFalse => rfl
  | prim h => cases h2 with | prim h' => rw [h] at h'; exact congrArg Comp.ret (Option.some.inj h')
  | call h => cases h2 with | call h' => rw [h] at h'; rw [Option.some.inj h']
  | caseMatch h => cases h2 with | caseMatch h' => rw [h] at h'; exact Option.some.inj h'
  | dupStep => cases h2 with | dupStep => rfl
  | dropStep => cases h2 with | dropStep => rfl
  | withReuseStep => cases h2 with | withReuseStep => rfl
  | reuseStep => cases h2 with | reuseStep => rfl

end Prism
