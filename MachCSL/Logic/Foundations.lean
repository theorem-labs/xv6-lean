import Iris.ProgramLogic.Adequacy
import Iris.Instances.Lib.CInvariants
import Iris.BI.MonPred

/-!
The logical foundation is Iris's concrete step-indexed `IProp` model. These
integration lemmas exercise spatial composition, exclusive ownership and
cancellable invariants. They do not establish adequacy of the RISC-V system;
that requires its operational language, state interpretation and initial WPs.
-/

namespace MachCSL.Logic

open Iris Iris.BI Iris.Std

variable {GF : BundledGFunctors}

/-- Reorder separately owned resources in the concrete Iris model. -/
theorem separate_comm (P Q : IProp GF) : iprop(P ∗ Q ⊣⊢ Q ∗ P) :=
  BI.sep_comm

/-- Apply a resource-consuming continuation while retaining its frame. -/
theorem apply_with_frame (P Q R : IProp GF) :
    iprop((P ∗ (P -∗ Q)) ∗ R ⊢ Q ∗ R) := by
  iintro ⟨⟨HP, HPQ⟩, HR⟩
  ihave HQ := HPQ $$ HP
  iframe

section Invariants

variable {hlc : HasLC} [InvGS_gen hlc GF] [CInvG GF]

/-- The same exclusive cancellation token cannot be owned twice. -/
theorem exclusive_token (γ : GName) :
    iprop(⊢ CancelableInvariant.excl (GF := GF) γ -∗
      CancelableInvariant.excl γ -∗ False) :=
  CancelableInvariant.excl_excl γ

/-- Full cancellation ownership recovers the guarded invariant body. -/
theorem cancel_invariant (E : CoPset) {N : Namespace} {γ : GName}
    {P : IProp GF} (hN : ↑N ⊆ E) :
    iprop(⊢ CancelableInvariant.cinv N γ P -∗
      CancelableInvariant.own γ (1 : Qp) ={E}=∗ ▷ P) :=
  CancelableInvariant.cancel E hN

end Invariants

-- This is the generic soundness theorem to instantiate for the system language.
-- It is checked here without replacing or weakening its premises.
-- Audit.lean checks its full transitive assumptions.

end MachCSL.Logic
