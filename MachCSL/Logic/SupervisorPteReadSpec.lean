import MachCSL.Logic.SupervisorPteReadDefs

namespace MachCSL.Logic.SupervisorPteRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  plain : ∀ shares rs address region, Config rs address region →
    ∀ image fixed whole gen era cpu dq value bound (reference : BitVec 64) rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era address 8 dq value bound (PteCanonical.slotSet reference) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon reference⌝ -∗
        ⌜PteCanonical.nonleaf reference = true → word = reference⌝ -∗
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era address 8 dq value bound (PteCanonical.slotSet reference) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (read_pte (.Physaddr address) 8 >>= continuation)) post)
  exclusive : ∀ shares rs address region, Config rs address region →
    ∀ image fixed whole gen era cpu dq (word : BitVec 64) bound sets rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.slot capacity era address 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (MachCSL.Memory.snapshot address 8 word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (read_pte_exclusive (.Physaddr address) 8 >>= continuation)) post)

end MachCSL.Logic.SupervisorPteRead
