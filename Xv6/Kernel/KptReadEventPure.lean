import Xv6.Kernel.KptReadEventSpec
import MachCSL.Machine.PteCanonicalLink
import MachCSL.Logic.TsoPinnedReadWPDefs

namespace Xv6.Kernel.KptReadEvent
open MachCSL.Machine MachCSL.Logic

theorem readFact_refl (word : PtTree.Word) : ReadFact word word := ⟨rfl, fun _ => rfl⟩

theorem readFact_leaf (reference word : PtTree.Word) (leaf : PtTree.Leaf reference)
    (same : PteCanonical.canon word = PteCanonical.canon reference) : ReadFact reference word := by
  refine ⟨same, ?_⟩
  intro pointer
  change PteCanonical.nonleaf reference = false at leaf
  rw [leaf] at pointer
  contradiction

theorem readFact_allowed (reference current word : PtTree.Word) (relation : ReadFact reference current)
    (allowed : TsoPinnedReadWP.Allowed 8 (PteCanonical.slotSet current) word) : ReadFact reference word := by
  refine ⟨(PteCanonical.canonical_read current word allowed).trans relation.1, ?_⟩
  intro pointer
  have same := relation.2 pointer
  subst current
  exact PteCanonical.exact_nonleaf reference word pointer allowed

theorem mapped_leaf tree vpn p2 p1 p0 (mapped : PtTree.Maps tree vpn p2 p1 p0) : PtTree.Leaf p0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,leaf,_⟩ := mapped
  exact leaf

end Xv6.Kernel.KptReadEvent
