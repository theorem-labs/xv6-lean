import Xv6.Kernel.KptHitSpec
import Xv6.Kernel.Sv39HitLink

namespace Xv6.Kernel.KptHit
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem program_eq asid vpn p2 p1 ppn permission a d access
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access) mxr doSum :
    program asid vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) access mxr doSum =
      KptAD.program vpn (PtTree.addr0 p1 vpn) (KptLeaf.word ppn permission a d) access mxr doSum >>=
        Sv39Hit.afterUpdate vpn (TlbCoherence.index vpn)
          (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) := by
  unfold program
  rw [Sv39Hit.raw_factor]
  have permitted : Sv39Hit.permission (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d))
      access mxr doSum = pure (.PTE_Check_Success ()) := by
    unfold Sv39Hit.permission
    change check_PTE_permission access .Supervisor mxr doSum
      (PteCanonical.flags (KptLeaf.word ppn permission a d))
      (ext_bits_of_PTE (KptLeaf.word ppn permission a d)) () = _
    rw [KptLeaf.word_flags, KptLeaf.word_ext]
    exact KptLeaf.permission_eq permission a d access supported allowed mxr doSum
  rw [permitted, BootPmp.sail_pure_bind, Sv39Hit.entry_update]

theorem result_eq asid vpn p2 p1 ppn permission a d branch :
    Sv39Hit.updateValue vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d))
      (KptAD.result branch) = result ppn branch := by
  have ppnEq : tlb_get_ppn 39 (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) vpn = ppn := by
    rw [TlbCoherence.get_ppn]
    exact KptLeaf.word_ppn ppn permission a d
  cases branch <;> simp only [KptAD.result, Sv39Hit.updateValue, result, ppnEq]

theorem update_variant asid vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD access enabled branch
    (facts : KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch) :
    Sv39Hit.UpdateVariant (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
      (KptAD.result branch) := by
  cases branch with
  | cached => trivial
  | disabled => trivial
  | reread observed =>
    change TlbCoherence.Variant (KptLeaf.word ppn permission cachedA cachedD) observed
    apply (TlbCoherence.variant_iff_canon _ _).mpr
    exact facts.2.2.1.trans (by rw [KptLeaf.word_canonical, KptLeaf.word_canonical])
  | written observed new =>
    change TlbCoherence.Variant (KptLeaf.word ppn permission cachedA cachedD) new
    apply (TlbCoherence.variant_iff_canon _ _).mpr
    exact facts.2.2.2.2.trans (by rw [KptLeaf.word_canonical, KptLeaf.word_canonical])

theorem coherent asid tree rs vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD access enabled branch
    (before : TlbCoherence.Coherent asid tree (rs .tlb))
    (resident : (rs .tlb)[TlbCoherence.index vpn]? =
      some (some (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))))
    (facts : KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
      (KptLeaf.word ppn permission referenceA referenceD) access enabled branch) :
    TlbCoherence.Coherent asid tree
      (after rs vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD)) branch .tlb) :=
  Sv39Hit.coherent_resume asid tree rs vpn _ (KptAD.result branch) before resident
    (update_variant asid vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD access enabled branch facts)

end Xv6.Kernel.KptHit
