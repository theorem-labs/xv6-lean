import MachCSL.Logic.SupervisorReadProofs

namespace MachCSL.Logic.SupervisorRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- No subordinate access implementation remains a premise of the native contract. -/
theorem nativeSpec : Spec capacity := actual capacity


/-- The plain physical read returns the same optional reservation fragment.
The actual nonexclusive node step never creates or clears a snapshot. -/
theorem wp_checked_read_reservation (shares : Shares) (rs : RegisterFile) (kind : Kind)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 8) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (access kind))
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : Result → SailM Unit) rr post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program kind address >>= continuation)) post) := by
  iintro Hcert Hregs Hrun Hword Hresv Hcontinue
  iapply wp_checked_read capacity shares rs kind address config range disabled region matched grant
    image fixed whole gen era cpu ξ dq word continuation post $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  iapply Hcontinue $$ %view Hregs Hrun Hword Hresv Hreceipt

end MachCSL.Logic.SupervisorRead
