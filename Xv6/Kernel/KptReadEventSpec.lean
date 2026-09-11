import Xv6.Kernel.KptReadEventDefs

namespace Xv6.Kernel.KptReadEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- One actual ordinary read event, opening and closing the shared invariant
within the native read premise. No slot or restoration callback is supplied
by the caller. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  read : ∀ image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0 level,
    PtTree.Maps tree vpn p2 p1 p0 →
    ∀ (req : MemoryReadWP.ReadRequest 8), req.pa = address tree vpn p2 p1 level →
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    ∀ B rr (continuation : MemoryReadWP.ReadResult 8 → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
      KptShared.bound capacity era B -∗ TsoPinnedReadWP.credential capacity.machine era cpu B -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜ReadFact (reference p2 p1 p0 level) word⌝ -∗
        KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
        KptShared.bound capacity era B -∗ TsoPinnedReadWP.credential capacity.machine era cpu B -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) continuation)) post)

end Xv6.Kernel.KptReadEvent
