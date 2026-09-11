import Xv6.Kernel.KptMissRules

namespace Xv6.Kernel.KptMiss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

/-- Called after the branch's event guards have been consumed. Coherence
is derived from the actual branch facts; no physical word is fixed in advance. -/
theorem wp_finish shares rs asid tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD
    access branch
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (coherent : TlbCoherence.Coherent asid tree (rs .tlb))
    (facts : KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access (KptAD.enabled rs) branch)
    image fixed whole gen era cpu (N : Namespace) root bound rr view2 view1 view0
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs [(.tlb, .own 1)] -∗
      clients capacity era cpu N root tree bound -∗
      KptTreeWalk.receipts capacity era cpu view2 view1 view0 -∗
      (resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn
          (KptLeaf.word ppn permission cachedA cachedD) rr view2 view1 view0 branch -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (result ppn branch))) post) -∗
      KptAD.clientResources capacity era cpu rs shares N root tree (PtTree.addr0 p1 vpn) rr branch -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false cachedA cachedD)
          (KptAD.result branch) >>= continuation)) post) := by
  iintro #Hcert Htlb #Hclients Hwalk Hfinish Had
  iunfold KptAD.clientResources at Had
  icases Had with ⟨Hregs,_,Hresv,Hreceipt⟩
  ihave Hregs := (cells_ad capacity era cpu rs shares).mpr $$ [Hregs Htlb]
  · iframe Hregs Htlb
  iapply wp_after_update capacity shares rs asid vpn p2 p1 ppn permission cachedA cachedD branch
    image fixed whole gen era cpu continuation post $$ Hcert Hregs
  iintro Hregs
  iapply Hfinish $$ [Hregs Hresv Hwalk Hreceipt]
  iunfold resources
  iframe Hregs Hclients Hresv Hwalk Hreceipt
  ipureintro
  exact coherent_after asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD
    access (KptAD.enabled rs) branch mapped coherent facts

end Xv6.Kernel.KptMiss
