import Xv6.Kernel.PtTreeMapProofs
import Xv6.Kernel.PtTreeVariantProofs

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem maps_canon (t : Tree) (vpn : VPN) (p2 p1 p0 : Word)
    (hm : Maps t vpn p2 p1 p0) : Maps (canon t) vpn p2 p1 (PteCanonical.canon p0) := by
  obtain ⟨c1, c0, hc1, hc0, hp2, hp1, hp0, hb1, hb0, hv2, hn2, hv1, hn1,
    hv0, hl0, napot, pbmt⟩ := hm
  refine ⟨canonLevel1 c1, canonLevel0 c0, ?_⟩
  refine ⟨?_, ?_, hp2, hp1, congrArg PteCanonical.canon hp0, hb1, hb0,
    hv2, hn2, hv1, hn1, (canon_valid_leaf p0 hl0).mpr hv0, (canon_leaf p0).mpr hl0,
    (canon_napot p0).mpr napot, (canon_pbmt p0).mpr pbmt⟩
  · change (children t (index 2 vpn)).map canonLevel1 = some (canonLevel1 c1)
    rw [hc1]; rfl
  · change (children c1 (index 1 vpn)).map canonLevel0 = some (canonLevel0 c0)
    rw [hc0]; rfl

theorem maps_canon_inv (t : Tree) (vpn : VPN) (p2 p1 w : Word)
    (hm : Maps (canon t) vpn p2 p1 w) :
    ∃ p0, Maps t vpn p2 p1 p0 ∧ w = PteCanonical.canon p0 := by
  obtain ⟨d1, d0, hd1, hd0, hp2, hp1, hw, hb1, hb0, hv2, hn2, hv1, hn1,
    hv0, hl0, napot, pbmt⟩ := hm
  obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.mp hd1
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hd0
  let p0 := entries c0 (index 0 vpn)
  change PteCanonical.canon p0 = w at hw
  subst w
  have leaf := (canon_leaf p0).mp hl0
  refine ⟨p0, ⟨c1, c0, hc1, hc0, hp2, hp1, rfl, hb1, hb0, hv2, hn2, hv1, hn1,
    (canon_valid_leaf p0 leaf).mp hv0, leaf, (canon_napot p0).mp napot,
    (canon_pbmt p0).mp pbmt⟩, rfl⟩

theorem maps_across (t t' : Tree) (vpn : VPN) (p2 p1 p0 : Word)
    (same : canon t = canon t') (hm : Maps t vpn p2 p1 p0) :
    ∃ q0, Maps t' vpn p2 p1 q0 ∧ PteCanonical.canon q0 = PteCanonical.canon p0 := by
  obtain ⟨q0, hq, eq⟩ := maps_canon_inv t' vpn p2 p1 (PteCanonical.canon p0)
    (same ▸ maps_canon t vpn p2 p1 p0 hm)
  exact ⟨q0, hq, eq.symm⟩

theorem canonLevel0_update (t : Tree) (i : Index) (w : Word)
    (same : PteCanonical.canon w = PteCanonical.canon (entries t i)) :
    canonLevel0 (updateEntry t i w) = canonLevel0 t := by
  unfold canonLevel0
  apply congrArg (fun e => Tree.node (base t) e (children t))
  funext j
  by_cases eq : j = i
  · subst j; simpa only [entries_updateEntry, ite_true] using same
  · simp only [entries_updateEntry, if_neg eq]

theorem canonLevel1_update (t c c' : Tree) (i : Index)
    (child : children t i = some c) (same : canonLevel0 c' = canonLevel0 c) :
    canonLevel1 (updateChild t i (some c')) = canonLevel1 t := by
  unfold canonLevel1
  apply congrArg (fun cs => Tree.node (base t) (entries t) cs)
  funext j
  by_cases eq : j = i
  · subst j; simp only [children_updateChild, ite_true, child, Option.map_some, same]
  · simp only [children_updateChild, if_neg eq]

theorem canon_update (t c c' : Tree) (i : Index)
    (child : children t i = some c) (same : canonLevel1 c' = canonLevel1 c) :
    canon (updateChild t i (some c')) = canon t := by
  unfold canon
  apply congrArg (fun cs => Tree.node (base t) (entries t) cs)
  funext j
  by_cases eq : j = i
  · subst j; simp only [children_updateChild, ite_true, child, Option.map_some, same]
  · simp only [children_updateChild, if_neg eq]

theorem canon_set_leaf (t : Tree) (vpn : VPN) (p2 p1 p0 : Word) (a d : BitVec 1)
    (hm : Maps t vpn p2 p1 p0) : canon (setLeaf t vpn (PteCanonical.setAD p0 a d)) = canon t := by
  obtain ⟨c1, c0, hc1, hc0, _, _, hp0, _⟩ := hm
  simp only [setLeaf, hc1, hc0]
  apply canon_update _ _ _ _ hc1
  apply canonLevel1_update _ _ _ _ hc0
  apply canonLevel0_update
  rw [hp0, PteCanonical.canon_variant]

end Xv6.Kernel.PtTree
