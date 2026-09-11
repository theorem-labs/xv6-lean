import MachCSL.Logic.TsoContextBytesWriteWPDefs

namespace MachCSL.Logic.TsoContextBytesWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextBytesReadWP

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  write : ∀ image fixed whole gen era cpu ξ (n : Nat) (req : MemoryWriteWP.WriteRequest n)
    (old new : BitVec (8 * n)) k rr post,
    n ≤ 2^64 → req.value = some new → deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ window capacity era ξ req.pa n (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ window capacity era ξ req.pa n (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem n req) k)) post)

end MachCSL.Logic.TsoContextBytesWriteWP
