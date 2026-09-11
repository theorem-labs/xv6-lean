import MachCSL.Logic.SupervisorPteWriteDefs

namespace MachCSL.Logic.SupervisorPteWrite
open Iris Iris.BI MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  write : ∀ shares rs address region, Config rs address region →
    ∀ image fixed whole gen era cpu (reserved physical new : BitVec 64) floors sets
      (continuation : Result → SailM Unit) post,
    (∀ j, j < 8 → nthByte new j ∈ sets j) →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot address 8 reserved)) -∗
      TsoPinnedWriteWP.pinWindow capacity era address physical (.own 1) floors sets -∗
      ▷ (∀ time, cells capacity era cpu rs shares -∗
        TsoPinnedWriteWP.storedWindow capacity era address new time floors sets -∗
        Tso.History.logElem capacity.era.history era.logEntries (time - 1)
          ⟨snapshot address 8 new, hartAgent cpu⟩ -∗ ⌜0 < time⌝ -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (write_pte_conditional (.Physaddr address) 8 new >>= continuation)) post)

end MachCSL.Logic.SupervisorPteWrite
