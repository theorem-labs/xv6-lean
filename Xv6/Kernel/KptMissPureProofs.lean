import Xv6.Kernel.KptMissSpec
import Xv6.Kernel.Sv39MissFactor
import Xv6.Kernel.TlbCoherenceLink
import Xv6.Kernel.KptLeafLink

namespace Xv6.Kernel.KptMiss
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem program_factor asid tree vpn access mxr doSum :
    program asid tree vpn access mxr doSum =
      KptTreeWalk.program tree vpn access mxr doSum false >>= afterWalk asid vpn access mxr doSum :=
  Sv39Miss.program_eq asid (Sv39TreeWalk.geometry tree 0#64 0#64 0#44) vpn access mxr doSum

theorem after_update asid vpn p2 p1 ppn permission a d branch :
    afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false a d) (KptAD.result branch) =
      (match branch with
      | .disabled => pure (result ppn branch)
      | _ => do
          add_to_TLB 39 asid vpn ppn (fillWord (KptLeaf.word ppn permission a d) branch)
            (.Physaddr (PtTree.addr0 p1 vpn)) 0
            (PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission a d))
          pure (result ppn branch)) := by
  cases branch <;> rfl

theorem after_walk asid vpn p2 p1 ppn permission a d access mxr doSum :
    afterWalk asid vpn access mxr doSum (.Ok (KptTreeWalk.output vpn p2 p1 ppn permission false a d, ())) =
      KptAD.program vpn (PtTree.addr0 p1 vpn) (KptLeaf.word ppn permission a d) access mxr doSum >>=
        afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false a d) := rfl

theorem fill_variant ppn permission referenceA referenceD cachedA cachedD access enabled branch
    (facts : KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch) :
    TlbCoherence.Variant (KptLeaf.word ppn permission referenceA referenceD)
      (fillWord (KptLeaf.word ppn permission cachedA cachedD) branch) := by
  apply (TlbCoherence.variant_iff_canon _ _).mpr
  cases branch with
  | cached | disabled => simp only [fillWord, KptLeaf.word_canonical]
  | reread observed => exact facts.2.2.1
  | written observed new => exact facts.2.2.2.2

/-- The actual fill uses the walk's old PPN and global fields. Canonical
agreement proves that they equal those of the independently chosen word. -/
theorem fill_coherent asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD word
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (coherent : TlbCoherence.Coherent asid tree (rs .tlb))
    (variant : TlbCoherence.Variant (KptLeaf.word ppn permission referenceA referenceD) word) :
    TlbCoherence.Coherent asid tree
      (Sv39Tlb.after rs asid vpn ppn word (.Physaddr (PtTree.addr0 p1 vpn))
        (PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission cachedA cachedD)) .tlb) := by
  have cachedVariant : TlbCoherence.Variant (KptLeaf.word ppn permission cachedA cachedD) word := by
    apply (TlbCoherence.variant_iff_canon _ _).mpr
    have same := (TlbCoherence.variant_iff_canon _ _).mp variant
    simpa only [KptLeaf.word_canonical] using same
  obtain ⟨a,d,eq⟩ := cachedVariant
  have ppnSame : PtTree.nextBase word = ppn := by
    rw [eq, TlbCoherence.nextBase_setAD]
    exact KptLeaf.word_ppn ppn permission cachedA cachedD
  have globalSame : PtTree.globalAfter false p2 p1 word =
      PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission cachedA cachedD) := by
    rw [eq]
    simp only [PtTree.globalAfter, PtTree.global_setAD]
  change TlbCoherence.Coherent asid tree
    (Sv39Tlb.filled (rs .tlb) asid vpn ppn word (.Physaddr (PtTree.addr0 p1 vpn))
      (PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission cachedA cachedD)))
  rw [← globalSame, ← ppnSame]
  exact TlbCoherence.fill asid tree (rs .tlb) vpn p2 p1 _ word mapped variant coherent

theorem coherent_after asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD access enabled branch
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (coherent : TlbCoherence.Coherent asid tree (rs .tlb))
    (facts : KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch) :
    TlbCoherence.Coherent asid tree
      (after rs asid vpn p2 p1 ppn (KptLeaf.word ppn permission cachedA cachedD) branch .tlb) := by
  have variant := fill_variant ppn permission referenceA referenceD cachedA cachedD access enabled branch facts
  cases branch with
  | disabled => exact coherent
  | cached | reread _ | written _ _ =>
    exact fill_coherent asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD _ mapped coherent variant

end Xv6.Kernel.KptMiss
