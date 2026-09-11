import Xv6.Kernel.TlbWindowSpec
import Xv6.Kernel.TlbCoherenceLink

namespace Xv6.Kernel.TlbWindow
open TlbCoherence MachCSL.Machine

theorem previous asid previous current tlb (coherent : TlbCoherence.Coherent asid previous tlb) :
    Coherent asid previous current tlb := fun query ent found => Or.inl (coherent query ent found)

theorem current asid previous current tlb (coherent : TlbCoherence.Coherent asid current tlb) :
    Coherent asid previous current tlb := fun query ent found => Or.inr (coherent query ent found)

theorem swap asid previous current tlb (coherent : Coherent asid previous current tlb) :
    Coherent asid current previous tlb := fun query ent found => (coherent query ent found).symm

theorem collapse asid tree tlb : Coherent asid tree tree tlb ↔ TlbCoherence.Coherent asid tree tlb :=
  ⟨fun coherent query ent found => (coherent query ent found).elim id id, previous asid tree tree tlb⟩

variable (coherence : TlbCoherence.Spec)

include coherence in
theorem canon_current asid previous current other tlb
    (same : PtTree.canon current = PtTree.canon other)
    (coherent : Coherent asid previous current tlb) : Coherent asid previous other tlb := by
  intro query ent found
  rcases coherent query ent found with old | now
  · exact Or.inl old
  · exact Or.inr (coherence.cache_canon asid current other query ent same now)

include coherence in
theorem canon_previous asid previous other current tlb
    (same : PtTree.canon previous = PtTree.canon other)
    (coherent : Coherent asid previous current tlb) : Coherent asid other current tlb :=
  swap asid current other tlb
    (canon_current coherence asid current previous other tlb same (swap asid previous current tlb coherent))

theorem fill_current asid previous current tlb vpn p2 p1 p0 word
    (mapped : PtTree.Maps current vpn p2 p1 p0) (variant : Variant p0 word)
    (coherent : Coherent asid previous current tlb) :
    Coherent asid previous current (filled tlb asid vpn p2 p1 word) := by
  intro query ent found
  by_cases same : index query = index vpn
  · rw [same] at found
    have selected := Sv39Tlb.selected tlb asid vpn (PtTree.nextBase word) word
      (.Physaddr (PtTree.addr0 p1 vpn)) (PtTree.globalAfter false p2 p1 word)
    change (filled tlb asid vpn p2 p1 word)[index vpn]? = some (some (entry asid vpn p2 p1 word)) at selected
    rw [selected] at found
    have eq := Option.some.inj (Option.some.inj found)
    obtain ⟨a,d,rfl⟩ := variant
    exact Or.inr ⟨vpn,p2,p1,p0,a,d,mapped,same.symm,eq.symm⟩
  · apply coherent query ent
    simpa only [filled, Sv39Tlb.other _ _ _ _ _ _ _ _ same] using found

theorem fill_previous asid previous current tlb vpn p2 p1 p0 word
    (mapped : PtTree.Maps previous vpn p2 p1 p0) (variant : Variant p0 word)
    (coherent : Coherent asid previous current tlb) :
    Coherent asid previous current (filled tlb asid vpn p2 p1 word) :=
  swap asid current previous _
    (fill_current asid current previous tlb vpn p2 p1 p0 word mapped variant
      (swap asid previous current tlb coherent))

include coherence in
theorem set_leaf_current asid previous current tlb vpn p2 p1 p0 a d
    (mapped : PtTree.Maps current vpn p2 p1 p0) (coherent : Coherent asid previous current tlb) :
    Coherent asid previous (PtTree.setLeaf current vpn (PteCanonical.setAD p0 a d)) tlb :=
  canon_current coherence asid previous current _ tlb
    (PtTree.canon_set_leaf current vpn p2 p1 p0 a d mapped).symm coherent

include coherence in
theorem set_leaf_previous asid previous current tlb vpn p2 p1 p0 a d
    (mapped : PtTree.Maps previous vpn p2 p1 p0) (coherent : Coherent asid previous current tlb) :
    Coherent asid (PtTree.setLeaf previous vpn (PteCanonical.setAD p0 a d)) current tlb :=
  canon_previous coherence asid previous _ current tlb
    (PtTree.canon_set_leaf previous vpn p2 p1 p0 a d mapped).symm coherent

include coherence in
theorem actual : Spec := ⟨previous, current, swap, collapse, canon_current coherence,
  canon_previous coherence, fill_current, fill_previous, set_leaf_current coherence, set_leaf_previous coherence⟩

end Xv6.Kernel.TlbWindow
