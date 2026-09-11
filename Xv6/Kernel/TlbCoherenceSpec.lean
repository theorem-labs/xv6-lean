import Xv6.Kernel.TlbCoherenceDefs

namespace Xv6.Kernel.TlbCoherence
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Exact source provenance and concrete model-tag/field obligations.
The constructed nativeSpec is exported by TlbCoherenceLink. -/
structure Spec : Prop where
  index_surjective : ∀ i : Fin 64, index (BitVec.ofNat 27 i.val) = i.val
  all_slots : ∀ asid tree tlb, Coherent asid tree tlb ↔
    ∀ i : Fin 64, ∀ ent, tlb[i.val]? = some (some ent) →
      CacheOf asid tree (BitVec.ofNat 27 i.val) ent
  empty : ∀ asid tree tlb,
    (∀ query, tlb[index query]? = some none) → Coherent asid tree tlb
  variant_iff_canon : ∀ current cached, Variant current cached ↔
    PteCanonical.canon cached = PteCanonical.canon current
  entry_match : ∀ storedAsid vpn p2 p1 word queryAsid query,
    match_TLB_Entry (entry storedAsid vpn p2 p1 word) queryAsid (query.signExtend 45) = true ↔
      (PtTree.globalAfter false p2 p1 word = true ∨ storedAsid = queryAsid) ∧ vpn = query
  cache_match : ∀ asid tree query ent queryAsid, CacheOf asid tree query ent →
    match_TLB_Entry ent queryAsid (query.signExtend 45) = true →
    ∃ p2 p1 p0 a d, PtTree.Maps tree query p2 p1 p0 ∧
      ent = entry asid query p2 p1 (PteCanonical.setAD p0 a d)
  cache_properties : ∀ asid tree query ent, CacheOf asid tree query ent →
    ent.asid = asid ∧ ent.levelMask = 0#45 ∧ ent.ppn = PtTree.nextBase ent.pte ∧
    PtTree.Valid ent.pte ∧ PtTree.Leaf ent.pte ∧ PtTree.NoNapot ent.pte ∧ PtTree.PbmtZero ent.pte
  cache_canon : ∀ asid tree other query ent, PtTree.canon tree = PtTree.canon other →
    CacheOf asid tree query ent → CacheOf asid other query ent
  coherent_canon : ∀ asid tree other tlb, PtTree.canon tree = PtTree.canon other →
    Coherent asid tree tlb → Coherent asid other tlb
  fill : ∀ asid tree old vpn p2 p1 p0 word,
    PtTree.Maps tree vpn p2 p1 p0 → Variant p0 word → Coherent asid tree old →
    Coherent asid tree (filled old asid vpn p2 p1 word)
  fill_self : ∀ asid tree old vpn p2 p1 p0,
    PtTree.Maps tree vpn p2 p1 p0 → Coherent asid tree old →
    Coherent asid tree (filled old asid vpn p2 p1 p0)
  cache_set_leaf : ∀ asid tree query ent vpn p2 p1 p0 a d,
    PtTree.Maps tree vpn p2 p1 p0 → CacheOf asid tree query ent →
    CacheOf asid (PtTree.setLeaf tree vpn (PteCanonical.setAD p0 a d)) query ent
  coherent_set_leaf : ∀ asid tree tlb vpn p2 p1 p0 a d,
    PtTree.Maps tree vpn p2 p1 p0 → Coherent asid tree tlb →
    Coherent asid (PtTree.setLeaf tree vpn (PteCanonical.setAD p0 a d)) tlb
  set_pte_entry : ∀ asid vpn p2 p1 old word, Variant old word →
    tlb_set_pte (k_n := 8) (entry asid vpn p2 p1 old) word = entry asid vpn p2 p1 word
  refresh : ∀ asid tree old vpn ent word,
    Coherent asid tree old → old[index vpn]? = some (some ent) → Variant ent.pte word →
    Coherent asid tree (refreshed old (index vpn) ent word)
  lookup_hit : ∀ asid tree tlb query queryAsid idx ent,
    Coherent asid tree tlb → lookupValue tlb queryAsid query = some (idx, ent) →
    idx = index query ∧ ∃ p2 p1 p0 a d, PtTree.Maps tree query p2 p1 p0 ∧
      ent = entry asid query p2 p1 (PteCanonical.setAD p0 a d)
  lookup_blocked : ∀ asid tree tlb query queryAsid,
    Coherent asid tree tlb → PtTree.Blocks tree query → lookupValue tlb queryAsid query = none
  get_pte : ∀ asid vpn p2 p1 word, tlb_get_pte 8 (entry asid vpn p2 p1 word) = word
  get_level : ∀ asid vpn p2 p1 word, tlb_get_level 39 (entry asid vpn p2 p1 word) = 0
  get_ppn : ∀ asid vpn p2 p1 word query,
    tlb_get_ppn 39 (entry asid vpn p2 p1 word) query = PtTree.nextBase word

/-- Actual register-only plans retain the lookup read, fill callback read,
and hit-refresh write. They do not execute translate_TLB_hit. -/
structure PlanSpec : Prop where
  lookup : ∀ rs asid vpn, RegisterPlan.Returns Sv39Tlb.footprint rs
    (lookup_TLB 39 asid vpn) (lookupValue (rs .tlb) asid vpn) rs
  fill : ∀ rs asid vpn p2 p1 word, RegisterPlan.Returns Sv39Tlb.footprint rs
    (add_to_TLB 39 asid vpn (PtTree.nextBase word) word (.Physaddr (PtTree.addr0 p1 vpn))
      0 (PtTree.globalAfter false p2 p1 word)) () (fillAfter rs asid vpn p2 p1 word)
  refresh : ∀ rs idx ent word, idx < 64 → RegisterPlan.Returns Sv39Tlb.footprint rs
    (write_TLB idx (tlb_set_pte (k_n := 8) ent word)) () (refreshAfter rs idx ent word)
  pbmt : ∀ rs asid vpn p2 p1 word, PtTree.PbmtZero word →
    RegisterPlan.Returns [] rs (tlb_get_pbmt (entry asid vpn p2 p1 word)) .PBMT_PMA rs

end Xv6.Kernel.TlbCoherence
