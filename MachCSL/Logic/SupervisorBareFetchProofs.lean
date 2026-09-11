import MachCSL.Logic.SupervisorBareFetchSpec
import MachCSL.Logic.SupervisorBareFetchPlan
import MachCSL.Logic.SupervisorFetchReadProofs

namespace MachCSL.Logic.SupervisorBareFetch
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open SupervisorFetchRead

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorBare.footprint, SupervisorFetchRead.footprint]

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_fetch_bytes (shares : Shares) (rs : RegisterFile) (bare : SupervisorBare.Config rs)
    (start address : BitVec 64) (n : Nat) (width : Supported n)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec (8 * n))
    (continuation : FetchBytes_Result n → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.FetchBytes_Success word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program start address n >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  obtain ⟨tail, cut, success, _error⟩ := fetch_boundary shares rs bare start address n width config range
    disabled region matched grant aligned
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs n (request address n)
    (program start address n) tail cut (SupervisorPhysical.device_ram address n range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (request address n).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

theorem actual : Spec capacity := ⟨wp_fetch_bytes capacity⟩

end MachCSL.Logic.SupervisorBareFetch
