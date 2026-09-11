import MachCSL.Logic.SupervisorFetchReadDefs

namespace MachCSL.Logic.SupervisorFetchRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (n : Nat) (_width : Supported n)
    (_aligned : is_aligned_paddr (.Physaddr address) n = true) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address n) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (_grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec (8 * n))
    (continuation : Result n → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address n >>= continuation)) post)

end MachCSL.Logic.SupervisorFetchRead
