import MachCSL.Logic.SupervisorWriteDefs

namespace MachCSL.Logic.SupervisorWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions TsoContextReadWP

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  write : ∀ (shares : Shares) (rs : RegisterFile) (address : BitVec 64),
    Machine.SupervisorPmp.TorRam rs → SupervisorPhysical.RamRange address 8 →
    rs .htif_tohost_base = none →
    ∀ region : PMA_Region,
    matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region →
    (override_PMA region.attributes .PBMT_PMA).writable = true →
    ∀ image fixed whole gen era cpu ξ (old new : BitVec 64) rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address new >>= continuation)) post)

end MachCSL.Logic.SupervisorWrite
