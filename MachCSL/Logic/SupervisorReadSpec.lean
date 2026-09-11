import MachCSL.Logic.SupervisorReadDefs

namespace MachCSL.Logic.SupervisorRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (rs : RegisterFile) (kind : Kind)
    (address : BitVec 64) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 8) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (_grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (access kind))
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program kind address >>= continuation)) post)

end MachCSL.Logic.SupervisorRead
