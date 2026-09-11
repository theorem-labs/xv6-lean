import MachCSL.Logic.ObservationInvariantSpec
import MachCSL.Logic.PowerGhostProofs

namespace MachCSL.Logic.ObservationInvariant
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : PowerGhost.Capacity GF)

instance ledger_persistent N γ R : Persistent (ledger capacity N γ R) := by
  unfold ledger
  infer_instance
instance trivial_persistent N γ : Persistent (trivial capacity N γ) := by
  unfold trivial
  infer_instance

theorem allocate (N : Namespace) (E : CoPset) (γ : GName)
    (R : List Observation → IProp GF) (history : List Observation) :
    iprop(⊢ PowerGhost.obsFrag capacity γ history -∗ R history ={E}=∗ ledger capacity N γ R) := by
  iintro Hfrag HR
  unfold ledger
  iapply inv_alloc
  iintro !>
  unfold PowerGhost.obsLedger
  iexists history
  iframe

theorem update (N : Namespace) (E : CoPset) (γ : GName)
    (R : List Observation → IProp GF) (timeless : ∀ history, Timeless (R history))
    (mask : (↑N : CoPset) ⊆ E) (history next : List Observation) (S : IProp GF)
    (step : iprop(⊢ R history -∗ S ={E \ ↑N}=∗ R next ∗ S)) :
    iprop(⊢ ledger capacity N γ R -∗ PowerGhost.obsAuth capacity γ history -∗ S ={E}=∗
      PowerGhost.obsAuth capacity γ next ∗ S) := by
  letI := timeless
  iintro #Hinv Ha HS
  iunfold ledger at Hinv
  iunfold inv at Hinv
  imod Hinv $$ %E [] with ⟨Hbody, Hclose⟩
  · ipureintro; exact mask
  · imod Hbody
    iunfold PowerGhost.obsLedger at Hbody
    icases Hbody with ⟨%stored, Hfrag, HR⟩
    ihave %eq := PowerGhost.obs_agree capacity γ history stored $$ Ha Hfrag
    subst stored
    imod step $$ HR HS with ⟨HR, HS⟩
    imod PowerGhost.obs_update capacity γ history next $$ Ha Hfrag with ⟨Ha, Hfrag⟩
    imod Hclose $$ [Hfrag HR] with _
    · iintro !>
      unfold PowerGhost.obsLedger
      iexists next
      iframe
    · imodintro
      iframe

theorem trivial_update (N : Namespace) (E : CoPset) (γ : GName)
    (history next : List Observation) (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ trivial capacity N γ -∗ PowerGhost.obsAuth capacity γ history ={E}=∗
      PowerGhost.obsAuth capacity γ next) := by
  iintro Hinv Ha
  unfold trivial
  imod update capacity N E γ (fun _ => iprop(True)) (fun _ => inferInstance) mask history next iprop(True)
    (by iintro _ H; imodintro; iframe) $$ Hinv Ha [] with ⟨Ha, _⟩
  · itrivial
  · imodintro
    iexact Ha

theorem observationInvariantSpec : ObservationInvariantSpec capacity :=
  ⟨allocate capacity, update capacity, trivial_update capacity⟩

end MachCSL.Logic.ObservationInvariant
