import Xv6.Kernel.TlbCoherenceWordProofs

namespace Xv6.Kernel.TlbCoherence
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem all_slots asid tree tlb : Coherent asid tree tlb ↔
    ∀ i : Fin 64, ∀ ent, tlb[i.val]? = some (some ent) →
      CacheOf asid tree (BitVec.ofNat 27 i.val) ent := by
  constructor
  · intro coherent i ent atIndex
    exact coherent _ ent (by simpa only [index_surjective] using atIndex)
  · intro slots query ent atIndex
    obtain ⟨vpn,p2,p1,p0,a,d,mapped,hash,same⟩ :=
      slots ⟨index query, Sv39Tlb.index_bound query⟩ ent atIndex
    exact ⟨vpn,p2,p1,p0,a,d,mapped,hash.trans (index_surjective ⟨index query, Sv39Tlb.index_bound query⟩),same⟩

theorem empty asid tree tlb (vacant : ∀ query, tlb[index query]? = some none) :
    Coherent asid tree tlb := by
  intro query ent found
  rw [vacant] at found
  cases found

theorem cache_match asid tree query ent queryAsid (cached : CacheOf asid tree query ent)
    (matched : match_TLB_Entry ent queryAsid (query.signExtend 45) = true) :
    ∃ p2 p1 p0 a d, PtTree.Maps tree query p2 p1 p0 ∧
      ent = entry asid query p2 p1 (PteCanonical.setAD p0 a d) := by
  obtain ⟨vpn,p2,p1,p0,a,d,mapped,_,rfl⟩ := cached
  have same := (entry_match _ _ _ _ _ _ _).mp matched |>.2
  subst vpn
  exact ⟨p2,p1,p0,a,d,mapped,rfl⟩

theorem cache_properties asid tree query ent (cached : CacheOf asid tree query ent) :
    ent.asid = asid ∧ ent.levelMask = 0#45 ∧ ent.ppn = PtTree.nextBase ent.pte ∧
    PtTree.Valid ent.pte ∧ PtTree.Leaf ent.pte ∧ PtTree.NoNapot ent.pte ∧ PtTree.PbmtZero ent.pte := by
  obtain ⟨vpn,p2,p1,p0,a,d,mapped,_,rfl⟩ := cached
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,valid,leaf,napot,pbmt⟩ := mapped
  refine ⟨rfl,rfl,rfl,?_,?_,?_,?_⟩
  · exact (PtTree.set_ad_valid_leaf p0 a d leaf).mpr valid
  · exact (PtTree.leaf_setAD p0 a d).mpr leaf
  · simpa only [entry, Sv39Tlb.entry, PtTree.NoNapot, PtTree.ext_setAD] using napot
  · simpa only [entry, Sv39Tlb.entry, PtTree.PbmtZero, PtTree.ext_setAD] using pbmt

theorem cache_canon asid tree other query ent (same : PtTree.canon tree = PtTree.canon other)
    (cached : CacheOf asid tree query ent) : CacheOf asid other query ent := by
  obtain ⟨vpn,p2,p1,p0,a,d,mapped,hash,rfl⟩ := cached
  obtain ⟨q0,mapped',canonical⟩ := PtTree.maps_across tree other vpn p2 p1 p0 same mapped
  have variant : Variant q0 (PteCanonical.setAD p0 a d) :=
    (variant_iff_canon _ _).mpr ((PteCanonical.canon_variant p0 a d).trans canonical.symm)
  obtain ⟨a',d',eq⟩ := variant
  exact ⟨vpn,p2,p1,q0,a',d',mapped',hash,congrArg (entry asid vpn p2 p1) eq⟩

theorem coherent_canon asid tree other tlb (same : PtTree.canon tree = PtTree.canon other)
    (coherent : Coherent asid tree tlb) : Coherent asid other tlb :=
  fun query ent found => cache_canon asid tree other query ent same (coherent query ent found)

theorem fill asid tree old vpn p2 p1 p0 word (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (variant : Variant p0 word) (coherent : Coherent asid tree old) :
    Coherent asid tree (filled old asid vpn p2 p1 word) := by
  intro query ent found
  by_cases same : index query = index vpn
  · rw [same] at found
    have selected := Sv39Tlb.selected old asid vpn (PtTree.nextBase word) word
      (.Physaddr (PtTree.addr0 p1 vpn)) (PtTree.globalAfter false p2 p1 word)
    change (filled old asid vpn p2 p1 word)[index vpn]? = some (some (entry asid vpn p2 p1 word)) at selected
    rw [selected] at found
    have eq := Option.some.inj (Option.some.inj found)
    obtain ⟨a,d,rfl⟩ := variant
    exact ⟨vpn,p2,p1,p0,a,d,mapped,same.symm,eq.symm⟩
  · apply coherent query ent
    simpa only [filled, Sv39Tlb.other _ _ _ _ _ _ _ _ same] using found

theorem fill_self asid tree old vpn p2 p1 p0 (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (coherent : Coherent asid tree old) : Coherent asid tree (filled old asid vpn p2 p1 p0) :=
  fill asid tree old vpn p2 p1 p0 p0 mapped (variant_refl p0) coherent

theorem cache_set_leaf asid tree query ent vpn p2 p1 p0 a d
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (cached : CacheOf asid tree query ent) :
    CacheOf asid (PtTree.setLeaf tree vpn (PteCanonical.setAD p0 a d)) query ent :=
  cache_canon asid tree _ query ent (PtTree.canon_set_leaf tree vpn p2 p1 p0 a d mapped).symm cached

theorem coherent_set_leaf asid tree tlb vpn p2 p1 p0 a d
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (coherent : Coherent asid tree tlb) :
    Coherent asid (PtTree.setLeaf tree vpn (PteCanonical.setAD p0 a d)) tlb :=
  coherent_canon asid tree _ tlb (PtTree.canon_set_leaf tree vpn p2 p1 p0 a d mapped).symm coherent

theorem refresh asid tree old vpn ent word (coherent : Coherent asid tree old)
    (found : old[index vpn]? = some (some ent)) (variant : Variant ent.pte word) :
    Coherent asid tree (refreshed old (index vpn) ent word) := by
  intro query current atIndex
  by_cases same : index query = index vpn
  · have selected : (refreshed old (index vpn) ent word)[index vpn]? =
        some (some (tlb_set_pte (k_n := 8) ent word)) := by
      simp [refreshed, _root_.Sail.vectorUpdate, Sv39Tlb.index_bound]
    rw [same,selected] at atIndex
    have eq := Option.some.inj (Option.some.inj atIndex)
    subst current
    obtain ⟨origin,p2,p1,p0,a,d,mapped,hash,rfl⟩ := coherent vpn ent found
    change Variant (PteCanonical.setAD p0 a d) word at variant
    rw [set_pte_entry _ _ _ _ _ _ variant]
    have combined : Variant p0 word := (variant_iff_canon _ _).mpr
      (((variant_iff_canon _ _).mp variant).trans (PteCanonical.canon_variant p0 a d))
    obtain ⟨a',d',rfl⟩ := combined
    exact ⟨origin,p2,p1,p0,a',d',mapped,hash.trans same.symm,rfl⟩
  · apply coherent query current
    simpa [refreshed, _root_.Sail.vectorUpdate, Ne.symm same] using atIndex

theorem lookup_hit asid tree tlb query queryAsid idx ent
    (coherent : Coherent asid tree tlb)
    (found : lookupValue tlb queryAsid query = some (idx,ent)) :
    idx = index query ∧ ∃ p2 p1 p0 a d, PtTree.Maps tree query p2 p1 p0 ∧
      ent = entry asid query p2 p1 (PteCanonical.setAD p0 a d) := by
  unfold lookupValue at found
  split at found
  · contradiction
  · rename_i current selected
    split at found
    · rename_i matched
      have pair := Option.some.inj found
      cases pair
      refine ⟨rfl,cache_match asid tree query ent queryAsid (coherent query ent ?_) matched⟩
      rw [Vector.getElem?_eq_getElem (Sv39Tlb.index_bound query)]
      simpa only [getElem!_pos tlb (index query) (Sv39Tlb.index_bound query)] using congrArg some selected
    · contradiction

theorem lookup_blocked asid tree tlb query queryAsid (coherent : Coherent asid tree tlb)
    (blocked : PtTree.Blocks tree query) : lookupValue tlb queryAsid query = none := by
  cases eq : lookupValue tlb queryAsid query with
  | none => rfl
  | some pair =>
    obtain ⟨_,p2,p1,p0,a,d,mapped,_⟩ := lookup_hit asid tree tlb query queryAsid pair.1 pair.2 coherent eq
    exact False.elim (PtTree.maps_blocks_excl tree query p2 p1 p0 mapped blocked)

end Xv6.Kernel.TlbCoherence
