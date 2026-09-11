import Xv6.Kernel.KptWriteEventDefs

namespace Xv6.Kernel.KptWriteEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- The resource update restores the full shared invariant and actual state
interpretation. The event rule invokes it inside the successful event's later. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  update : ∀ era (g : State) cpu (N : Namespace) (E : CoPset) root tree vpn p2 p1 p0,
    (↑N : CoPset) ⊆ E → PtTree.Maps tree vpn p2 p1 p0 →
    ∀ (req : MemoryWriteWP.WriteRequest 8) (new : BitVec 64),
    req.pa = PtTree.addr0 p1 vpn → PteCanonical.canon new = PteCanonical.canon p0 →
    iprop(⊢ clients capacity era N root tree -∗
      MemoryWriteWP.writeBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g
      ={E}=∗
        MemoryWriteWP.writeBundle capacity.machine.era era (MemoryWriteWP.writeState g cpu req new) ∗
        Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
          (MemoryWriteWP.writeState g cpu req new) ∗
        Tso.History.logElem capacity.machine.era.history era.logEntries g.log.length
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ ∗ clients capacity era N root tree)
  write : ∀ image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0,
    PtTree.Maps tree vpn p2 p1 p0 →
    ∀ (req : MemoryWriteWP.WriteRequest 8) (reserved new : BitVec 64),
    req.pa = PtTree.addr0 p1 vpn → req.value = some new →
    deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    PteCanonical.canon new = PteCanonical.canon p0 →
    ∀ (continuation : MemoryWriteWP.WriteResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      ▷ (∀ time, ⌜0 < time⌝ -∗ clients capacity era N root tree -∗
        Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) continuation)) post)

end Xv6.Kernel.KptWriteEvent
