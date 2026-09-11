import Xv6.Kernel.KptHitRules

namespace Xv6.Kernel.KptHit
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (ad : KptAD.Spec capacity)
include ad

/-- Permission, the complete native shared A/D update and actual cached-entry
refresh compose on the same six register cells and canonical snapshot. -/
theorem wp_hit shares rs asid tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD region
    (config : Config rs (PtTree.addr0 p1 vpn) region)
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (before : TlbCoherence.Coherent asid tree (rs .tlb))
    (resident : (rs .tlb)[TlbCoherence.index vpn]? =
      some (some (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))))
    access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum image fixed whole gen era cpu (N : Namespace) root rr
    (continuation : Result → SailM Unit) post :
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
          access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [program_eq asid vpn p2 p1 ppn permission cachedA cachedD access supported allowed,
    BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hclients Hresv Hfinish
  ihave ⟨Hregs,Htlb⟩ := (cells_ad capacity era cpu rs shares).mp $$ Hregs
  iapply ad.update shares rs (PtTree.addr0 p1 vpn) region config N root tree vpn p2 p1
    ppn permission referenceA referenceD cachedA cachedD mapped rfl access supported allowed mxr doSum
    image fixed whole gen era cpu rr
    (fun response => Sv39Hit.afterUpdate vpn (TlbCoherence.index vpn)
      (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD)) response >>= continuation) post
    $$ Hcert Hregs Hclients Hresv
  iunfold KptAD.finish
  iintro %branch
  ihave Hfinish := Hfinish $$ %branch
  cases branch <;> simp only [KptAD.guarded]
  all_goals first | iintro !> !> | iintro !> | skip
  all_goals
    iintro %facts Had
    iunfold KptAD.clientResources at Had
    icases Had with ⟨Hregs,Hclients,Hresv,Hreceipt⟩
    ihave Hregs := (cells_ad capacity era cpu rs shares).mpr $$ [Hregs Htlb]
    · iframe Hregs Htlb
    iapply wp_resume capacity shares rs asid vpn p2 p1 ppn permission cachedA cachedD _
      image fixed whole gen era cpu continuation post $$ Hcert Hregs
    iintro Hregs
    iapply Hfinish $$ %facts [Hregs Hclients Hresv Hreceipt]
    iunfold resources
    iframe Hregs Hclients Hresv Hreceipt
    ipureintro
    exact coherent asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD
      access (KptAD.enabled rs) _ before resident facts

theorem actual : Spec capacity := ⟨wp_hit capacity ad⟩

end Xv6.Kernel.KptHit
