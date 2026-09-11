import MachCSL.Logic.SupervisorRead4Plan
import MachCSL.Logic.SupervisorFetchReadProofs

namespace MachCSL.Logic.SupervisorRead4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open SupervisorFetchRead
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_checked_read (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).readable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 32)
    (continuation : Result → SailM Unit) post :
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
        (.hart gen cpu (program address >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  obtain ⟨tail, cut, success, _error⟩ := checked_boundary shares rs address config range
    disabled region matched grant aligned
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs 4 (request address 4)
    (program address) tail cut (SupervisorPhysical.device_ram address 4 range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (request address 4).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

theorem actual : Spec capacity := ⟨wp_checked_read capacity⟩

end MachCSL.Logic.SupervisorRead4
