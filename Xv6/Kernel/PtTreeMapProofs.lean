import Xv6.Kernel.PtTreeGeometry
import Xv6.Kernel.PtTreeWordProofs

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem maps_det (t : Tree) (vpn : VPN) (p2 p1 p0 q2 q1 q0 : Word)
    (hp : Maps t vpn p2 p1 p0) (hq : Maps t vpn q2 q1 q0) :
    p2 = q2 ∧ p1 = q1 ∧ p0 = q0 := by
  obtain ⟨c1, c0, hc1, hc0, hp2, hp1, hp0, _⟩ := hp
  obtain ⟨d1, d0, hd1, hd0, hq2, hq1, hq0, _⟩ := hq
  have e1 := Option.some.inj (hc1.symm.trans hd1)
  subst d1
  have e0 := Option.some.inj (hc0.symm.trans hd0)
  subst d0
  exact ⟨hp2.symm.trans hq2, hp1.symm.trans hq1, hp0.symm.trans hq0⟩

theorem maps_blocks_excl (t : Tree) (vpn : VPN) (p2 p1 p0 : Word)
    (hm : Maps t vpn p2 p1 p0) (hb : Blocks t vpn) : False := by
  obtain ⟨c1, c0, hc1, hc0, hp2, hp1, hp0, _, _, _, _, _, _, valid0, _⟩ := hm
  rcases hb with ⟨hn, _⟩ | ⟨d1, hd1, hn, _⟩ | ⟨d1, d0, hd1, hd0, _, _, _, _, _, _, invalid0⟩
  · rw [hc1] at hn; contradiction
  · have e1 := Option.some.inj (hc1.symm.trans hd1)
    subst d1
    rw [hc0] at hn; contradiction
  · have e1 := Option.some.inj (hc1.symm.trans hd1)
    subst d1
    have e0 := Option.some.inj (hc0.symm.trans hd0)
    subst d0
    exact valid_invalid p0 valid0 (hp0 ▸ invalid0)

@[simp] theorem base_updateEntry (t : Tree) (i : Index) (w : Word) :
    base (updateEntry t i w) = base t := rfl
@[simp] theorem children_updateEntry (t : Tree) (i : Index) (w : Word) :
    children (updateEntry t i w) = children t := rfl
@[simp] theorem entries_updateEntry (t : Tree) (i j : Index) (w : Word) :
    entries (updateEntry t i w) j = if j = i then w else entries t j := rfl
@[simp] theorem base_updateChild (t : Tree) (i : Index) (c : Option Tree) :
    base (updateChild t i c) = base t := rfl
@[simp] theorem entries_updateChild (t : Tree) (i : Index) (c : Option Tree) :
    entries (updateChild t i c) = entries t := rfl
@[simp] theorem children_updateChild (t : Tree) (i j : Index) (c : Option Tree) :
    children (updateChild t i c) j = if j = i then c else children t j := rfl

theorem set_leaf_maps_self (t : Tree) (vpn : VPN) (p2 p1 p0 w : Word)
    (hm : Maps t vpn p2 p1 p0) (valid : Valid w) (leaf : Leaf w)
    (napot : NoNapot w) (pbmt : PbmtZero w) : Maps (setLeaf t vpn w) vpn p2 p1 w := by
  obtain ⟨c1, c0, hc1, hc0, hp2, hp1, hp0, hb1, hb0, hv2, hn2, hv1, hn1, _⟩ := hm
  simp only [setLeaf, hc1, hc0]
  refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w)),
    updateEntry c0 (index 0 vpn) w, ?_⟩
  simp only [children_updateChild, entries_updateChild, entries_updateEntry,
    base_updateChild, base_updateEntry]
  exact ⟨by trivial, by trivial, hp2, hp1, rfl, hb1, hb0, hv2, hn2, hv1, hn1, valid, leaf, napot, pbmt⟩

theorem set_leaf_maps_other (t : Tree) (vpn vpn' : VPN) (q2 q1 q0 w : Word)
    (different : vpn' ≠ vpn) (hm : Maps t vpn' q2 q1 q0) :
    Maps (setLeaf t vpn w) vpn' q2 q1 q0 := by
  obtain ⟨c1, c0, hc1, hc0, hq2, hq1, hq0, hb1, hb0, rest⟩ := hm
  unfold setLeaf
  split
  · exact ⟨c1, c0, hc1, hc0, hq2, hq1, hq0, hb1, hb0, rest⟩
  · rename_i d1 hd1
    split
    · exact ⟨c1, c0, hc1, hc0, hq2, hq1, hq0, hb1, hb0, rest⟩
    · rename_i d0 hd0
      by_cases e2 : index 2 vpn' = index 2 vpn
      · have same1 : c1 = d1 := Option.some.inj ((e2 ▸ hc1).symm.trans hd1)
        subst d1
        by_cases e1 : index 1 vpn' = index 1 vpn
        · have same0 : c0 = d0 := Option.some.inj ((e1 ▸ hc0).symm.trans hd0)
          subst d0
          have e0 : index 0 vpn' ≠ index 0 vpn := fun h => different (index_injective vpn' vpn e2 e1 h)
          refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w)),
            updateEntry c0 (index 0 vpn) w, ?_⟩
          simp only [children_updateChild, entries_updateChild, entries_updateEntry,
            base_updateChild, base_updateEntry, if_pos e2, if_pos e1, if_neg e0]
          exact ⟨by trivial, by trivial, hq2, hq1, hq0, hb1, hb0, rest⟩
        · refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry d0 (index 0 vpn) w)), c0, ?_⟩
          simp only [children_updateChild, entries_updateChild, base_updateChild, if_pos e2, if_neg e1]
          exact ⟨by trivial, hc0, hq2, hq1, hq0, hb1, hb0, rest⟩
      · refine ⟨c1, c0, ?_⟩
        simp only [children_updateChild, entries_updateChild, if_neg e2]
        exact ⟨hc1, hc0, hq2, hq1, hq0, hb1, hb0, rest⟩

theorem set_leaf_blocks (t : Tree) (vpn vpn' : VPN) (p2 p1 p0 w : Word)
    (hm : Maps t vpn p2 p1 p0) (hb : Blocks t vpn') : Blocks (setLeaf t vpn w) vpn' := by
  obtain ⟨c1, c0, hc1, hc0, _, _, hp0, _, _, _, _, _, _, valid0, _⟩ := hm
  simp only [setLeaf, hc1, hc0]
  rcases hb with ⟨hn, invalid⟩ | ⟨d1, hd1, hn, rest⟩ |
    ⟨d1, d0, hd1, hd0, hv2, hp2, hv1, hp1, hb1, hb0, invalid⟩
  · have e2 : index 2 vpn' ≠ index 2 vpn := by
      intro eq; rw [eq, hc1] at hn; contradiction
    apply Or.inl
    simpa only [children_updateChild, entries_updateChild, if_neg e2] using And.intro hn invalid
  · by_cases e2 : index 2 vpn' = index 2 vpn
    · have same1 := Option.some.inj ((e2 ▸ hd1).symm.trans hc1)
      subst d1
      have e1 : index 1 vpn' ≠ index 1 vpn := by
        intro eq; rw [eq, hc0] at hn; contradiction
      apply Or.inr; apply Or.inl
      refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w)), ?_⟩
      simp only [children_updateChild, entries_updateChild, base_updateChild, if_pos e2, if_neg e1]
      exact ⟨by trivial, hn, rest⟩
    · apply Or.inr; apply Or.inl
      refine ⟨d1, ?_⟩
      simpa only [children_updateChild, entries_updateChild, if_neg e2] using And.intro hd1 ⟨hn, rest⟩
  · by_cases e2 : index 2 vpn' = index 2 vpn
    · have same1 := Option.some.inj ((e2 ▸ hd1).symm.trans hc1)
      subst d1
      by_cases e1 : index 1 vpn' = index 1 vpn
      · have same0 := Option.some.inj ((e1 ▸ hd0).symm.trans hc0)
        subst d0
        have e0 : index 0 vpn' ≠ index 0 vpn := by
          intro eq
          exact valid_invalid p0 valid0 (by simpa only [eq, hp0] using invalid)
        apply Or.inr; apply Or.inr
        refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w)),
          updateEntry c0 (index 0 vpn) w, ?_⟩
        simp only [children_updateChild, entries_updateChild, entries_updateEntry,
          base_updateChild, base_updateEntry, if_pos e2, if_pos e1, if_neg e0]
        exact ⟨by trivial, by trivial, hv2, hp2, hv1, hp1, hb1, hb0, invalid⟩
      · apply Or.inr; apply Or.inr
        refine ⟨updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w)), d0, ?_⟩
        simp only [children_updateChild, entries_updateChild, base_updateChild, if_pos e2, if_neg e1]
        exact ⟨by trivial, hd0, hv2, hp2, hv1, hp1, hb1, hb0, invalid⟩
    · apply Or.inr; apply Or.inr
      refine ⟨d1, d0, ?_⟩
      simp only [children_updateChild, entries_updateChild, if_neg e2]
      exact ⟨hd1, hd0, hv2, hp2, hv1, hp1, hb1, hb0, invalid⟩

end Xv6.Kernel.PtTree
