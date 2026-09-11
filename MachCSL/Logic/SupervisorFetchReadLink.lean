import MachCSL.Logic.SupervisorFetchReadProofs

namespace MachCSL.Logic.SupervisorFetchRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Exact width specialization; alignment is only at the fetched width. -/
theorem wp_fetch2 (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64)
    (aligned : is_aligned_paddr (.Physaddr address) 2 = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 2) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 2 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 16)
    (continuation : Result 2 → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 2 dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 2 dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address 2 >>= continuation)) post) := by
  exact wp_checked_fetch capacity shares rs address 2 (by simp [Supported]) aligned config range
    disabled region matched grant image fixed whole gen era cpu ξ dq word continuation post

/-- Exact width specialization; alignment is only at the fetched width. -/
theorem wp_fetch4 (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 32)
    (continuation : Result 4 → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address 4 >>= continuation)) post) := by
  exact wp_checked_fetch capacity shares rs address 4 (by simp [Supported]) aligned config range
    disabled region matched grant image fixed whole gen era cpu ξ dq word continuation post

/-- Both physical fetch widths preserve the incoming optional reservation. -/
theorem wp_fetch_reservation (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (n : Nat) (width : Supported n)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec (8 * n))
    (continuation : Result n → SailM Unit) rr post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address n >>= continuation)) post) := by
  iintro Hcert Hregs Hrun Hword Hresv Hcontinue
  iapply wp_checked_fetch capacity shares rs address n width aligned config range disabled region matched grant
    image fixed whole gen era cpu ξ dq word continuation post $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  iapply Hcontinue $$ %view Hregs Hrun Hword Hresv Hreceipt

end MachCSL.Logic.SupervisorFetchRead
