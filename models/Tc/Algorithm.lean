import Tc.Syntax

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Prism
namespace Tc

inductive TcError where
  | unknownVar : String → TcError
  | kindMismatch : Kind → Kind → TcError
  | occursTy : Nat → Ty → TcError
  | occursRow : Nat → Row → TcError
  | rowMismatch : Row → Row → TcError
  | unsupported : String → TcError

abbrev TcM := Except TcError

mutual

def inferKind (Γ : KindEnv) : Ty → TcM Kind
  | .unit | .int | .i64 | .u64 | .bool | .float | .char | .str => pure .type
  | .nat _ => pure .nat
  | .var x =>
      match lookup x Γ with
      | some k => pure k
      | none => throw (.unknownVar x)
  | .row r => checkRow Γ r *> pure .row
  | .fun ps eff ret => do
      for p in ps do
        checkKind Γ p .type
      checkRow Γ eff
      checkKind Γ ret .type
      pure .type
  | .tuple fields => do
      for field in fields do
        checkKind Γ field .type
      pure .type
  | .forallE x body => do
      checkKind ((x, .type) :: Γ) body .type
      pure .type
  | .rowForall x body => do
      checkKind ((x, .row) :: Γ) body .type
      pure .type
  | .app f x => do
      let kf ← inferKind Γ f
      match kf with
      | .fun dom cod =>
          checkKind Γ x dom
          pure cod
      | other => throw (.kindMismatch (.fun .type .type) other)
  | .con _ _ =>
      throw (.unsupported "constructor kind lookup")
  | .exist _ =>
      throw (.unsupported "kinding unsolved type existential")

def checkKind (Γ : KindEnv) (t : Ty) (want : Kind) : TcM Unit := do
  let got ← inferKind Γ t
  if got = want then
    pure ()
  else
    throw (.kindMismatch want got)

def checkRow (Γ : KindEnv) : Row → TcM Unit
  | .empty => pure ()
  | .exist _ => pure ()
  | .var x =>
      match lookup x Γ with
      | some .row => pure ()
      | some k => throw (.kindMismatch .row k)
      | none => throw (.unknownVar x)
  | .extend _ args rest => do
      for arg in args do
        checkKind Γ arg .type
      checkRow Γ rest

end

structure Subst where
  ty : Nat → Option Ty
  row : Nat → Option Row

mutual

def applyTy (σ : Subst) : Ty → Ty
  | .fun ps eff ret => .fun (ps.map (applyTy σ)) (applyRow σ eff) (applyTy σ ret)
  | .con c args => .con c (args.map (applyTy σ))
  | .app f x => .app (applyTy σ f) (applyTy σ x)
  | .tuple fields => .tuple (fields.map (applyTy σ))
  | .row r => .row (applyRow σ r)
  | .forallE x body => .forallE x (applyTy σ body)
  | .rowForall x body => .rowForall x (applyTy σ body)
  | .exist n =>
      match σ.ty n with
      | some t => t
      | none => .exist n
  | other => other

def applyRow (σ : Subst) : Row → Row
  | .empty => .empty
  | .var x => .var x
  | .extend name args rest => .extend name (args.map (applyTy σ)) (applyRow σ rest)
  | .exist n =>
      match σ.row n with
      | some r => r
      | none => .exist n

end

inductive RowEq : Row → Row → Prop where
  | refl : RowEq r r
  | canonical :
      canonicalRow (rowLabels r) (rowTail r) =
        canonicalRow (rowLabels s) (rowTail s) →
      RowEq r s

inductive TyEq : Ty → Ty → Prop where
  | refl : TyEq t t
  | row :
      RowEq r s →
      TyEq (.row r) (.row s)

def unify (_t _u : Ty) : TcM Subst :=
  throw (.unsupported "type unification")

def unifyRow (_r _s : Row) : TcM Subst :=
  throw (.unsupported "row unification")

def inferExpr (_Γ : TermEnv) (_e : Expr) : TcM (Ty × Row) :=
  throw (.unsupported "expression inference")

/-- Abstract model of Rust `tc::check`. A real proof would replace this with an
extracted/verified model of `src/tc`, or avoid trusting it by checking emitted
certificates instead. -/
def rustTypecheck (_p : RustProgram) : TcM RustChecked :=
  throw (.unsupported "Rust typechecker model")

structure RustTcCert where
  scheme : String
  payload : String
deriving Repr

inductive CheckedProgram where
  | checked : CheckedProgram

def checkRustTcCert (_cert : RustTcCert) : TcM CheckedProgram :=
  throw (.unsupported "Rust typechecker certificate validation")

end Tc
end Prism
