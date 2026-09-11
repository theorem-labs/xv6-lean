import Xv6.Kernel.Sv39TreeWalkDefs

namespace Xv6.Kernel.Sv39TreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Native direct-slot contracts. No caller-supplied memory success or
register/control-fold oracle appears; the only WP premise is the genuine
residual-program continuation. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  pointer : ∀ shares rs (base : PtTree.PPN) (raw : PtTree.Word),
    PtTree.Valid raw → PtTree.Pointer raw →
    ∀ vpn (level : Fin 3), 0 < level.val →
    ∀ region, SupervisorPteRead.Config rs (PtTree.slotAddress base (PtTree.index level.val vpn)) region →
    ∀ access mxr doSum global image fixed whole gen era cpu bound dq values rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era (PtTree.slotAddress base (PtTree.index level.val vpn))
        8 dq values bound (PteCanonical.slotSet raw) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era (PtTree.slotAddress base (PtTree.index level.val vpn))
          8 dq values bound (PteCanonical.slotSet raw) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.nextBase raw)
            (level.val - 1) (global || PtTree.globalBit raw) () >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum base level.val global () >>= continuation)) post)
  walk : ∀ shares rs tree vpn p2 p1 regions, Config rs tree vpn p2 p1 regions →
    ∀ ppn permission referenceA referenceD,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum global image fixed whole gen era cpu bound dq values rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era tree vpn p2 p1 ppn permission bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        slots capacity era tree vpn p2 p1 ppn permission bound dq values -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (output vpn p2 p1 ppn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program tree vpn access mxr doSum global >>= continuation)) post)

end Xv6.Kernel.Sv39TreeWalk
