import MachCSL.Logic.TsoContextWriteWPDefs

namespace MachCSL.Logic.TsoContextWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextReadWP

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  write : ∀ image fixed whole gen era cpu ξ (req : MemoryWriteWP.WriteRequest 8)
    (old new : BitVec 64) k rr post,
    req.value = some new → deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) k)) post)

end MachCSL.Logic.TsoContextWriteWP
