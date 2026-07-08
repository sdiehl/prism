import Tc.Soundness

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Prism
namespace Tc

/-!
End-to-end theorem shapes for the two plausible verification strategies.

1. Certificate path (pragmatic): Rust is an untrusted proof producer. Lean checks
   a certificate and the theorem says accepted certificates imply well-typedness.

2. Direct implementation path (research-scale): model or extract enough Rust that
   `rustTypecheck` itself has a refinement theorem. This is the "full proof of
   just the typechecker" boundary.
-/

inductive CertRepresentsProgram : RustTcCert → Program → Prop where
  | assumed : CertRepresentsProgram cert p

inductive CertRepresentsChecked : RustTcCert → Checked → Prop where
  | assumed : CertRepresentsChecked cert c

inductive CertValid : RustTcCert → Program → Checked → Prop where
  | checked :
      CertRepresentsProgram cert p →
      CertRepresentsChecked cert c →
      ProgramWellTyped p c →
      CertValid cert p c

theorem checkRustTcCert_sound
    (cert : RustTcCert) (p : Program) (c : Checked) :
    checkRustTcCert cert = Except.ok CheckedProgram.checked →
    CertRepresentsProgram cert p →
    CertRepresentsChecked cert c →
    ProgramWellTyped p c := by
  sorry

theorem certificate_path_end_to_end
    (cert : RustTcCert) (p : Program) (c : Checked) :
    checkRustTcCert cert = Except.ok CheckedProgram.checked →
    CertRepresentsProgram cert p →
    CertRepresentsChecked cert c →
    CertValid cert p c := by
  intro hCheck hProg hChecked
  exact CertValid.checked hProg hChecked
    (checkRustTcCert_sound cert p c hCheck hProg hChecked)

/-!
Direct Rust-proof boundary.

This is the expensive theorem: it needs either an extraction/model of Rust's
`src/tc` implementation or a verification framework that can prove the Rust code
refines the declarative judgments. The input boundary is intentionally after
resolve/desugar/NodeId assignment; proving parser/resolver/desugar correctness is
separate work.
-/

inductive RustInputWellFormed : RustProgram → Prop where
  | assumed : RustInputWellFormed rp

inductive RustCheckedRepresentsAccepted :
    RustProgram → RustChecked → Program → Checked → Prop where
  | assumed :
      RustInputWellFormed rp →
      RepresentsProgram rp p →
      RepresentsChecked rc c →
      RustCheckedRepresentsAccepted rp rc p c

theorem rust_representation_preserves_wellformed_input
    (rp : RustProgram) (p : Program) :
    RustInputWellFormed rp →
    RepresentsProgram rp p →
    InputWellFormed p := by
  sorry

theorem rust_checked_side_tables_represent_valid_checked
    (rp : RustProgram) (rc : RustChecked) (p : Program) (c : Checked) :
    rustTypecheck rp = Except.ok rc →
    RustCheckedRepresentsAccepted rp rc p c →
    CheckedValid p c := by
  sorry

theorem rust_typechecker_subsystems_sound
    (rp : RustProgram) (rc : RustChecked) (p : Program) (c : Checked) :
    rustTypecheck rp = Except.ok rc →
    RustCheckedRepresentsAccepted rp rc p c →
    DeclsWellTyped p c ∧
      ClassesCoherent p c ∧
      DictionariesValid p c ∧
      PatternsSound p c ∧
      EffectsSound p c ∧
      HandlerGradesSound p c ∧
      SideTablesValid p c := by
  sorry

/-- Full proof shape for just the Rust typechecker.

No parser, resolver, desugar, elaborator, optimizer, runtime, or codegen claim is
included. The theorem starts from the resolved/desugared Rust program value and
ends at the Lean declarative typing judgment plus validity of the `Checked`
artifact that elaboration will consume.
-/
theorem rust_typechecker_sound
    (rp : RustProgram) (rc : RustChecked) (p : Program) (c : Checked) :
    rustTypecheck rp = Except.ok rc →
    RustCheckedRepresentsAccepted rp rc p c →
    ProgramWellTyped p c := by
  intro hAccept hRep
  cases hRep with
  | assumed hRustInput hProg hChecked =>
      have hInput : InputWellFormed p :=
        rust_representation_preserves_wellformed_input rp p hRustInput hProg
      have hValid : CheckedValid p c :=
        rust_checked_side_tables_represent_valid_checked rp rc p c hAccept
          (RustCheckedRepresentsAccepted.assumed hRustInput hProg hChecked)
      exact ProgramWellTyped.checked hInput hValid

end Tc
end Prism
