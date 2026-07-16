import ModelSimp

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-
Experimental Prism typechecker proof scaffold: syntax and declarative judgments.

This module is deliberately outside `lakefile.toml`'s default targets. The files
under `models/Tc/` are a proof map, not a finished verification. They state the
objects and theorems an end-to-end soundness proof for Prism's Rust typechecker
would need; unresolved proof obligations are explicit `sorry` sites.
-/
namespace Prism
namespace Tc

inductive Kind where
  | type
  | row
  | nat
  | fun : Kind → Kind → Kind
deriving DecidableEq, Repr

mutual

inductive Ty where
  | unit
  | int
  | i64
  | u64
  | bool
  | float
  | char
  | str
  | var : String → Ty
  | exist : Nat → Ty
  | forallE : String → Ty → Ty
  | rowForall : String → Ty → Ty
  | fun : List Ty → Row → Ty → Ty
  | con : String → List Ty → Ty
  | app : Ty → Ty → Ty
  | tuple : List Ty → Ty
  | row : Row → Ty
  | nat : Nat → Ty

inductive Row where
  | empty
  | extend : String → List Ty → Row → Row
  | var : String → Row
  | exist : Nat → Row

end

abbrev KindEnv := List (String × Kind)
abbrev TermEnv := List (String × Ty)

def lookup {α : Type} (x : String) : List (String × α) → Option α
  | [] => none
  | (y, v) :: rest => if x = y then some v else lookup x rest

def rowLabels : Row → List (String × List Ty)
  | .empty => []
  | .var _ => []
  | .exist _ => []
  | .extend name args rest => (name, args) :: rowLabels rest

def rowTail : Row → Row
  | .extend _ _ rest => rowTail rest
  | tail => tail

def labelKey (l : String × List Ty) : String :=
  l.fst

/-- Placeholder for Rust's `EffRow::canonical`: sort labels by the canonical
wire/hash rendering, deduplicate equal labels, and fold over a terminal tail.

The scaffold does not model sorting/deduplication yet, but it does preserve the
basic row shape: labels are folded over the supplied tail instead of collapsing
every row to empty. -/
def canonicalRow (labels : List (String × List Ty)) (tail : Row) : Row :=
  labels.foldr (fun label acc => .extend label.fst label.snd acc) tail

def NoDupLabels (r : Row) : Prop :=
  (rowLabels r).Pairwise (fun a b => labelKey a ≠ labelKey b)

mutual

inductive HasKind : KindEnv → Ty → Kind → Prop where
  | unit : HasKind Γ .unit .type
  | int : HasKind Γ .int .type
  | i64 : HasKind Γ .i64 .type
  | u64 : HasKind Γ .u64 .type
  | bool : HasKind Γ .bool .type
  | float : HasKind Γ .float .type
  | char : HasKind Γ .char .type
  | str : HasKind Γ .str .type
  | natLit : HasKind Γ (.nat n) .nat
  | var :
      lookup x Γ = some k →
      HasKind Γ (.var x) k
  | row :
      RowWF Γ r →
      HasKind Γ (.row r) .row
  | fun :
      (∀ t, t ∈ ps → HasKind Γ t .type) →
      RowWF Γ eff →
      HasKind Γ ret .type →
      HasKind Γ (.fun ps eff ret) .type
  | tuple :
      (∀ t, t ∈ fields → HasKind Γ t .type) →
      HasKind Γ (.tuple fields) .type
  | con :
      (ctorKind : Kind) →
      SpineHasKind Γ ctorKind args .type →
      HasKind Γ (.con ctor args) .type
  | app :
      HasKind Γ f (.fun a b) →
      HasKind Γ x a →
      HasKind Γ (.app f x) b
  | forallE :
      HasKind ((x, .type) :: Γ) body .type →
      HasKind Γ (.forallE x body) .type
  | rowForall :
      HasKind ((x, .row) :: Γ) body .type →
      HasKind Γ (.rowForall x body) .type

inductive RowWF : KindEnv → Row → Prop where
  | empty : RowWF Γ .empty
  | var :
      lookup x Γ = some .row →
      RowWF Γ (.var x)
  | exist :
      RowWF Γ (.exist n)
  | extend :
      (∀ t, t ∈ args → HasKind Γ t .type) →
      RowWF Γ rest →
      RowWF Γ (.extend name args rest)

inductive SpineHasKind : KindEnv → Kind → List Ty → Kind → Prop where
  | done :
      SpineHasKind Γ k [] k
  | step :
      HasKind Γ arg dom →
      SpineHasKind Γ cod rest out →
      SpineHasKind Γ (.fun dom cod) (arg :: rest) out

end

inductive Expr where
  | var : String → Expr
  | int : Int → Expr
  | bool : Bool → Expr
  | lam : String → Ty → Expr → Expr
  | app : Expr → Expr → Expr
  | letE : String → Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr

inductive HasType : TermEnv → Expr → Ty → Row → Prop where
  | int :
      HasType Γ (.int n) .int .empty
  | bool :
      HasType Γ (.bool b) .bool .empty
  | var :
      lookup x Γ = some τ →
      HasType Γ (.var x) τ .empty
  | lam :
      HasType ((x, τ) :: Γ) body ρ eff →
      HasType Γ (.lam x τ body) (.fun [τ] eff ρ) .empty
  | app :
      HasType Γ f (.fun [arg] eff ret) effF →
      HasType Γ x arg effX →
      HasType Γ (.app f x) ret
        (canonicalRow (rowLabels effF ++ rowLabels effX ++ rowLabels eff) .empty)
  | letE :
      HasType Γ e τ eff1 →
      HasType ((x, τ) :: Γ) body ρ eff2 →
      HasType Γ (.letE x e body) ρ
        (canonicalRow (rowLabels eff1 ++ rowLabels eff2) .empty)
  | ite :
      HasType Γ c .bool effC →
      HasType Γ t τ effT →
      HasType Γ e τ effE →
      HasType Γ (.ite c t e) τ
        (canonicalRow (rowLabels effC ++ rowLabels effT ++ rowLabels effE) .empty)

/-- Abstract enough to state the full typechecker theorem without reifying the
whole surface AST yet. Later work should replace these string lists with a real
resolved/desugared `Program<CorePhase>` representation. -/
structure Program where
  decls : List String
  effects : List String
  classes : List String
  instances : List String
deriving Repr

/-- The Lean analogue of Rust's `tc::Checked`: initially abstract, but the final
proof must refine each field to match Rust's side tables (`env`, `data`, `ctors`,
`field_res`, `path_res`, `span_types`, `dicts`, and so on). -/
structure Checked where
  env : TermEnv
  kinds : KindEnv
  spanTypes : List (Nat × Ty)
  dictSites : List (Nat × String)
  fieldRes : List (Nat × String)
  pathRes : List (Nat × String)
  opGrades : List (String × String)

structure RustProgram where
  payload : String
deriving Repr

structure RustChecked where
  payload : String
deriving Repr

inductive InputWellFormed : Program → Prop where
  | assumed : InputWellFormed p

inductive CheckedValid : Program → Checked → Prop where
  | assumed : CheckedValid p c

inductive ProgramWellTyped : Program → Checked → Prop where
  | checked :
      InputWellFormed p →
      CheckedValid p c →
      ProgramWellTyped p c

inductive RepresentsProgram : RustProgram → Program → Prop where
  | assumed : RepresentsProgram rp p

inductive RepresentsChecked : RustChecked → Checked → Prop where
  | assumed : RepresentsChecked rc c

end Tc
end Prism
