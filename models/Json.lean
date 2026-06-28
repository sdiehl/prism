import Prism
import Lean.Data.Json

/-
Consumer side of the differential-oracle bridge: decode the tagged JSON core IR
emitted by `prism dump core-json` (Rust `src/core/json.rs`) into `Prism.Core`,
so the verified CEK machine can run the exact core the compiler builds.

The schema is tagged by `"c"` (computations), `"v"` (values), `"p"` (patterns).
Decoders are `partial` -- they run only in the `oracle` executable, never in a
proof. IO/builtin nodes are mapped to the model's erased forms (the model lowers
effects away); genuinely unmodeled state (`ref` cells) is rejected, so only the
pure + effects fragment round-trips -- exactly where the model and interpreter
are meant to agree.
-/

namespace Prism.Json

open Lean (Json)

private def jStr (j : Json) (k : String) : Except String String :=
  (j.getObjVal? k) >>= (·.getStr?)

private def jOpt (j : Json) (k : String) : Option Json :=
  (j.getObjVal? k).toOption

def jBinOp : String → Except String BinOp
  | "add" => .ok .add | "sub" => .ok .sub | "mul" => .ok .mul
  | "div" => .ok .div | "rem" => .ok .rem
  | "eq" => .ok .eq | "ne" => .ok .ne
  | "lt" => .ok .lt | "le" => .ok .le | "gt" => .ok .gt | "ge" => .ok .ge
  | "and" => .ok .and | "or" => .ok .or
  | "addf" => .ok .addf | "subf" => .ok .subf | "mulf" => .ok .mulf | "divf" => .ok .divf
  | "eqf" => .ok .eqf | "nef" => .ok .nef
  | "ltf" => .ok .ltf | "lef" => .ok .lef | "gtf" => .ok .gtf | "gef" => .ok .gef
  | s => .error s!"unknown binop {s}"

def jStrList (j : Json) : Except String (List String) := do
  (← j.getArr?).toList.mapM (·.getStr?)

mutual
  partial def jValue (j : Json) : Except String Value := do
    match ← jStr j "v" with
    | "var" => return .var (← jStr j "x")
    | "int" => return .int (← (← j.getObjVal? "n").getInt?)
    | "float" => return .float (← (← j.getObjVal? "f").getNum?).toFloat
    | "bool" => return .bool (← (← j.getObjVal? "b").getBool?)
    | "unit" => return .unit
    | "str" => return .str (← jStr j "s")
    | "thunk" => return .thunk (← jComp (← j.getObjVal? "c"))
    | "ctor" =>
        return .ctor (← jStr j "name") (← (← j.getObjVal? "tag").getNat?)
                     (← jList jValue (← j.getObjVal? "args"))
    | "tuple" => return .tuple (← jList jValue (← j.getObjVal? "args"))
    | t => .error s!"unknown value tag {t}"

  partial def jPat (j : Json) : Except String Pat := do
    match ← jStr j "p" with
    | "wild" => return .wild
    | "var" => return .var (← jStr j "x")
    | "int" => return .int (← (← j.getObjVal? "n").getInt?)
    | "bool" => return .bool (← (← j.getObjVal? "b").getBool?)
    | "ctor" => return .ctor (← jStr j "name") (← jList jPat (← j.getObjVal? "args"))
    | "tuple" => return .tuple (← jList jPat (← j.getObjVal? "args"))
    | t => .error s!"unknown pat tag {t}"

  partial def jComp (j : Json) : Except String Comp := do
    match ← jStr j "c" with
    | "ret" => return .ret (← jValue (← j.getObjVal? "v"))
    | "bind" =>
        return .bind (← jComp (← j.getObjVal? "m")) (← jStr j "x") (← jComp (← j.getObjVal? "n"))
    | "force" => return .force (← jValue (← j.getObjVal? "v"))
    | "lam" => return .lam (← jStrList (← j.getObjVal? "xs")) (← jComp (← j.getObjVal? "body"))
    | "app" => return .app (← jComp (← j.getObjVal? "f")) (← jList jValue (← j.getObjVal? "args"))
    | "ite" =>
        return .ite (← jValue (← j.getObjVal? "cond")) (← jComp (← j.getObjVal? "t"))
                    (← jComp (← j.getObjVal? "e"))
    | "prim" =>
        return .prim (← jBinOp (← jStr j "op")) (← jValue (← j.getObjVal? "a"))
                     (← jValue (← j.getObjVal? "b"))
    | "call" => return .call (← jStr j "name") (← jList jValue (← j.getObjVal? "args"))
    | "case" => return .case (← jValue (← j.getObjVal? "scrut")) (← jArms (← j.getObjVal? "arms"))
    | "doOp" => return .doOp (← jStr j "name") (← jList jValue (← j.getObjVal? "args"))
    | "mask" => return .mask (← jStrList (← j.getObjVal? "ops")) (← jComp (← j.getObjVal? "body"))
    | "handle" =>
        let retVar := (jOpt j "retVar").bind (·.getStr?.toOption)
        let retBody ← match jOpt j "retBody" with
          | some b => some <$> jComp b
          | none => pure none
        return .handle (← jComp (← j.getObjVal? "body")) retVar retBody
                       (← jList jHandleOp (← j.getObjVal? "ops"))
    -- IO / builtins erased to the model's forms (effects are lowered away here).
    | "print" => return .print (← jValue (← j.getObjVal? "v"))
    | "printf" => return .printf (← jValue (← j.getObjVal? "v"))
    | "prints" => return .prints (← jValue (← j.getObjVal? "v"))
    | "printNl" => return .print .unit
    | "readInt" => return .readInt
    | "readLine" => return .readInt
    | "rand" => return .readInt
    | "srand" => return .drop (← jValue (← j.getObjVal? "v"))
    | "err" => return .err (← jValue (← j.getObjVal? "v"))
    | "floatBuiltin" => return .floatBuiltin (← jStr j "name") (← jValue (← j.getObjVal? "v"))
    | "strBuiltin" => return .strBuiltin (← jStr j "name") (← jList jValue (← j.getObjVal? "args"))
    | "dup" => return .dup (← jValue (← j.getObjVal? "v"))
    | "drop" => return .drop (← jValue (← j.getObjVal? "v"))
    | "withReuse" =>
        return .withReuse (← jStr j "tok") (← jValue (← j.getObjVal? "freed"))
                          (← jComp (← j.getObjVal? "body"))
    | "reuse" => return .reuse (← jStr j "tok") (← jValue (← j.getObjVal? "v"))
    | "refNew" | "refGet" | "refSet" =>
        .error "ref cells are outside the differential fragment the model covers"
    | t => .error s!"unknown comp tag {t}"

  partial def jHandleOp (j : Json) : Except String HandleOp := do
    return .mk (← jStr j "name") (← jStrList (← j.getObjVal? "params"))
               (← jStr j "resume") (← jComp (← j.getObjVal? "body"))

  partial def jArms (j : Json) : Except String (List (Pat × Comp)) := do
    let arr ← j.getArr?
    arr.toList.mapM fun a => do
      return (← jPat (← a.getObjVal? "pat"), ← jComp (← a.getObjVal? "body"))

  partial def jList {α : Type} (f : Json → Except String α) (j : Json) : Except String (List α) := do
    (← j.getArr?).toList.mapM f
end

def jCoreFn (j : Json) : Except String CoreFn := do
  return ⟨← jStr j "name", ← jStrList (← j.getObjVal? "params"), ← jComp (← j.getObjVal? "body")⟩

/-- Decode a whole `prism dump core-json` program into a `Core`. -/
def coreOfJson (src : String) : Except String Core := do
  let j ← Json.parse src
  return ⟨← (← (← j.getObjVal? "fns").getArr?).toList.mapM jCoreFn⟩

end Prism.Json
