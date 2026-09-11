import Xv6.Kernel.KptHitDefs

namespace Xv6.Kernel.KptHit
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- The caller owns the resident TLB cell and a shared canonical snapshot.
The full enabled A/D program is discharged internally by native shared events. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  hit : ∀ shares rs asid tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD region,
    Config rs (PtTree.addr0 p1 vpn) region →
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    TlbCoherence.Coherent asid tree (rs .tlb) →
    (rs .tlb)[TlbCoherence.index vpn]? =
      some (some (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))) →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum image fixed whole gen era cpu (N : Namespace) root rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptAD.clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      (∀ branch : Branch, KptAD.guarded branch iprop(
        ⌜KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
          (KptLeaf.word ppn permission referenceA referenceD) access (KptAD.enabled rs) branch⌝ -∗
        resources capacity era cpu rs shares asid N root tree vpn
          (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
          (PtTree.addr0 p1 vpn) rr branch -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (result ppn branch))) post)) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program asid vpn
          (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
          access mxr doSum >>= continuation)) post)

end Xv6.Kernel.KptHit
