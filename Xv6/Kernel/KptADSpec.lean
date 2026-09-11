import Xv6.Kernel.KptADDefs

namespace Xv6.Kernel.KptAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Shared event clients, explicit hardware facts and genuine final
continuations only: no physical slots, successful responses or access oracles. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  read : ∀ shares rs address region, SupervisorPteRead.Config rs address region →
    ∀ image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0,
    PtTree.Maps tree vpn p2 p1 p0 → address = PtTree.addr0 p1 vpn →
    ∀ rr (continuation : SupervisorPteRead.Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view observed, ⌜PteCanonical.canon observed = PteCanonical.canon p0⌝ -∗
        cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
          (some (snapshot address 8 observed)) -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok observed))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (read_pte_exclusive (.Physaddr address) 8 >>= continuation)) post)
  write : ∀ shares rs address region, SupervisorPteWrite.Config rs address region →
    ∀ image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0,
    PtTree.Maps tree vpn p2 p1 p0 → address = PtTree.addr0 p1 vpn →
    ∀ (reserved new : BitVec 64), PteCanonical.canon new = PteCanonical.canon p0 →
    ∀ (continuation : SupervisorPteWrite.Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (some (snapshot address 8 reserved)) -∗
      ▷ (∀ time, ⌜0 < time⌝ -∗ cells capacity era cpu rs shares -∗
        clients capacity era N root tree -∗
        Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
          ⟨snapshot address 8 new, hartAgent cpu⟩ -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (write_pte_conditional (.Physaddr address) 8 new >>= continuation)) post)
  update : ∀ shares rs address region, Config rs address region →
    ∀ (N : Namespace) root tree vpn p2 p1 (ppn : BitVec 44) permission a d cachedA cachedD,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) → address = PtTree.addr0 p1 vpn →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access → ∀ mxr doSum,
    ∀ image fixed whole gen era cpu rr (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree address
        (KptLeaf.word ppn permission cachedA cachedD) (KptLeaf.word ppn permission a d)
        rr access continuation post -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program vpn address (KptLeaf.word ppn permission cachedA cachedD)
          access mxr doSum >>= continuation)) post)

end Xv6.Kernel.KptAD
