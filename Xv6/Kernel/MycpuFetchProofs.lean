import Xv6.Kernel.MycpuFetchSpec
import Xv6.Kernel.MycpuFetchPlan
import MachCSL.Logic.SupervisorBareFetchProofs
import Xv6.Kernel.MycpuBootResourcesSharing

namespace Xv6.Kernel.MycpuFetch
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorBareFetch.footprint,
    SupervisorBare.footprint, SupervisorFetchRead.footprint]

theorem footprint_length (shares : Shares) : (footprint shares).length = 9 := rfl

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_fetch (shares : Shares) (rs : RegisterFile) (i : Fin 14) (region : PMA_Region)
    (config : Config rs i region)
    image fixed whole gen era cpu ξ dq (continuation : FetchResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
      window capacity era ξ dq i -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
        window capacity era ξ dq i -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (result i))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (fetch () >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  obtain ⟨tail, cut, success, _error⟩ := fetch_cut shares rs i region config
  have gate := SupervisorFetchRead.Boundary.fold capacity (footprint shares) (footprint_unique shares) rs
    (MycpuFetchBytes.width i) (SupervisorFetchRead.request (MycpuDecode.address i) (MycpuFetchBytes.width i))
    (fetch ()) tail cut (SupervisorPhysical.device_ram _ _ (address_range i)) (by rfl)
    image fixed whole gen era cpu ξ dq (MycpuFetchBytes.word i) continuation post
  rw [show (SupervisorFetchRead.request (MycpuDecode.address i) (MycpuFetchBytes.width i)).pa =
    MycpuDecode.address i from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

/-- Concrete boot span supplies the actual fetched word without giving up the
other overlapping windows or upgrading discarded timestamp fractions. -/
theorem wp_fetch_shared (shares : Shares) (rs : RegisterFile) (i : Fin 14) (region : PMA_Region)
    (config : Config rs i region)
    image fixed whole gen era cpu ξ (continuation : FetchResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
      shared capacity era -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
        shared capacity era -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (result i))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (fetch () >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun #Hspan Hfinish
  ihave Hcontext := MycpuBootResources.discarded_context
    (MycpuBootResources.storeCapacity capacity.era) (MycpuBootResources.storeNames era) ξ $$ Hspan
  ihave ⟨Hword, _⟩ := MycpuBootResources.fetch_access
    (MycpuBootResources.storeCapacity capacity.era) (MycpuBootResources.storeNames era) ξ .discard i $$ Hcontext
  isimp only [MycpuBootResources.fetchWindow, MycpuBootResources.storeCapacity,
    MycpuBootResources.storeNames] at Hword
  iapply wp_fetch capacity shares rs i region config image fixed whole gen era cpu ξ .discard continuation post
    $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun _ Hreceipt
  iapply Hfinish $$ %view Hregs Hrun Hspan Hreceipt

end Xv6.Kernel.MycpuFetch
