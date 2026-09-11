import Xv6.Kernel.KptTreeWalkDefs

namespace Xv6.Kernel.KptTreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Actual shared PTE wrapper and three-read walk contracts. No direct slot,
read-value premise, register-plan premise or restoration callback is exposed. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  pte : ∀ shares rs tree vpn p2 p1 p0 (level : Fin 3),
    PtTree.Maps tree vpn p2 p1 p0 →
    ∀ region, SupervisorPteRead.Config rs (KptReadEvent.address tree vpn p2 p1 level) region →
    ∀ image fixed whole gen era cpu (N : Namespace) root bound rr
      (continuation : SupervisorPteRead.Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜KptReadEvent.ReadFact (KptReadEvent.reference p2 p1 p0 level) word⌝ -∗
        cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (read_pte (.Physaddr (KptReadEvent.address tree vpn p2 p1 level)) 8 >>= continuation)) post)
  walk : ∀ shares rs tree vpn p2 p1 regions, Config rs tree vpn p2 p1 regions →
    ∀ ppn permission referenceA referenceD,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum global image fixed whole gen era cpu (N : Namespace) root bound rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (output vpn p2 p1 ppn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program tree vpn access mxr doSum global >>= continuation)) post)

end Xv6.Kernel.KptTreeWalk
