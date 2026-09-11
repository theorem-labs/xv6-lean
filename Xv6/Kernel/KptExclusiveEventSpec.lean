import Xv6.Kernel.KptExclusiveEventDefs

namespace Xv6.Kernel.KptExclusiveEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Both contracts restore the actual state resources. The public event rule
has no caller-supplied slot, bound, boot credential or restoration callback. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  current : ∀ era (g : State) cpu (N : Namespace) (E : CoPset) root tree vpn p2 p1 p0,
    (↑N : CoPset) ⊆ E → PtTree.Maps tree vpn p2 p1 p0 →
    iprop(⊢ clients capacity era N root tree -∗
      MemoryExclusiveWP.readBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
        (TsoRead.advanceView g cpu g.log.length) -∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) g.log.length
      ={E}=∗ ∃ word,
        ⌜readBytes g.memory (PtTree.addr0 p1 vpn) 8 = some word ∧ ReadFact p0 word⌝ ∗
        MemoryExclusiveWP.readBundle capacity.machine.era era g ∗
        Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
          (TsoRead.advanceView g cpu g.log.length) ∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) g.log.length ∗
        clients capacity era N root tree)
  read : ∀ image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0,
    PtTree.Maps tree vpn p2 p1 p0 →
    ∀ (req : MemoryExclusiveWP.ReadRequest 8), req.pa = PtTree.addr0 p1 vpn →
    deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    ∀ rr (continuation : MemoryExclusiveWP.ReadResult 8 → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜ReadFact p0 word⌝ -∗
        clients capacity era N root tree -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
          (some (snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryExclusiveWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (word, none)))) post) -∗
      MemoryExclusiveWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) continuation)) post)

end Xv6.Kernel.KptExclusiveEvent
