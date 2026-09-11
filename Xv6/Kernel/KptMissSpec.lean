import Xv6.Kernel.KptMissDefs

namespace Xv6.Kernel.KptMiss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  factor : ∀ asid tree vpn access mxr doSum,
    program asid tree vpn access mxr doSum =
      KptTreeWalk.program tree vpn access mxr doSum false >>= afterWalk asid vpn access mxr doSum
  after_update : ∀ asid vpn p2 p1 ppn permission a d branch,
    afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false a d) (KptAD.result branch) =
      (match branch with
      | .disabled => pure (result ppn branch)
      | _ => do
          add_to_TLB 39 asid vpn ppn (fillWord (KptLeaf.word ppn permission a d) branch)
            (.Physaddr (PtTree.addr0 p1 vpn)) 0
            (PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission a d))
          pure (result ppn branch))
  fill_variant : ∀ ppn permission referenceA referenceD cachedA cachedD access enabled branch,
    KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch →
    TlbCoherence.Variant (KptLeaf.word ppn permission referenceA referenceD)
      (fillWord (KptLeaf.word ppn permission cachedA cachedD) branch)
  coherent : ∀ asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD access enabled branch,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    TlbCoherence.Coherent asid tree (rs .tlb) →
    KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch →
    TlbCoherence.Coherent asid tree
      (after rs asid vpn p2 p1 ppn (KptLeaf.word ppn permission cachedA cachedD) branch .tlb)

/-- Full actual miss over supplied persistent shared-tree clients. No
physical leaf word, direct slot, read result or successful callback is input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  miss : ∀ shares rs asid tree vpn p2 p1 regions, Config rs tree vpn p2 p1 regions →
    ∀ ppn permission referenceA referenceD,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    TlbCoherence.Coherent asid tree (rs .tlb) →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum image fixed whole gen era cpu (N : Namespace) root bound rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree bound asid vpn p2 p1 ppn
        permission referenceA referenceD access rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program asid tree vpn access mxr doSum >>= continuation)) post)

end Xv6.Kernel.KptMiss
