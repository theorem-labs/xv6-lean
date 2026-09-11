import MachCSL.Logic.TsoContextBytesReadWPDefs

namespace MachCSL.Logic.TsoContextBytesReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ image fixed whole gen era cpu ξ n (req : MemoryReadWP.ReadRequest n) k dq word post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ window capacity era ξ req.pa n dq word -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ window capacity era ξ req.pa n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.readMem n req) k)) post)

end MachCSL.Logic.TsoContextBytesReadWP
