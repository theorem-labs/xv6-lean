import MachCSL.Logic.SupervisorRead4Defs

namespace MachCSL.Logic.SupervisorRead4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64)
    (_aligned : is_aligned_paddr (.Physaddr address) 4 = true) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 4) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (_grant : (override_PMA region.attributes .PBMT_PMA).readable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 32)
    (continuation : Result → SailM Unit) post,
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
        (.hart gen cpu (program address >>= continuation)) post)

end MachCSL.Logic.SupervisorRead4
