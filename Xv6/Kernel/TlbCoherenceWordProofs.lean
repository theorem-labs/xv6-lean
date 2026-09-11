import Xv6.Kernel.TlbCoherenceSpec
import Xv6.Kernel.PtTreeLink
import Xv6.Kernel.Sv39TlbLink
import MachCSL.Machine.PteCanonicalLink

namespace Xv6.Kernel.TlbCoherence
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem index_surjective (i : Fin 64) : index (BitVec.ofNat 27 i.val) = i.val := by
  change ((BitVec.ofNat 27 i.val).extractLsb 5 0).toNat = i.val
  simp [Nat.mod_eq_of_lt (show i.val < 2^27 by omega)]

theorem variant_iff_canon (current cached : PtTree.Word) : Variant current cached ↔
    PteCanonical.canon cached = PteCanonical.canon current := by
  constructor
  · rintro ⟨a,d,rfl⟩
    exact PteCanonical.canon_variant current a d
  · exact PteCanonical.canon_inv current cached

theorem variant_refl (word : PtTree.Word) : Variant word word := variant_iff_canon _ _ |>.mpr rfl

theorem tag_injective (vpn query : PtTree.VPN) (same : vpn.signExtend 45 = query.signExtend 45) :
    vpn = query := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  have bit := congrArg (fun w : BitVec 45 => w.getLsbD i) same
  simpa only [BitVec.getLsbD_signExtend, show i < 45 by omega, decide_true,
    bound, if_true, Bool.true_and] using bit

theorem entry_match storedAsid vpn p2 p1 word queryAsid query :
    match_TLB_Entry (entry storedAsid vpn p2 p1 word) queryAsid (query.signExtend 45) = true ↔
      (PtTree.globalAfter false p2 p1 word = true ∨ storedAsid = queryAsid) ∧ vpn = query := by
  have tags : vpn.signExtend 45 = query.signExtend 45 ↔ vpn = query :=
    ⟨tag_injective vpn query, fun same => congrArg (BitVec.signExtend 45) same⟩
  simp only [match_TLB_Entry, entry, Sv39Tlb.entry, BitVec.not_zero, BitVec.and_allOnes,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, tags]
  rfl

theorem nextBase_setAD (word : PtTree.Word) (a d : BitVec 1) :
    PtTree.nextBase (PteCanonical.setAD word a d) = PtTree.nextBase word := by
  change _root_.Sail.BitVec.extractLsb (PteCanonical.setAD word a d) 53 10 =
    _root_.Sail.BitVec.extractLsb word 53 10
  exact PteCanonical.ppn_unchanged word a d

theorem set_pte_entry asid vpn p2 p1 old word (variant : Variant old word) :
    tlb_set_pte (k_n := 8) (entry asid vpn p2 p1 old) word = entry asid vpn p2 p1 word := by
  obtain ⟨a,d,rfl⟩ := variant
  unfold entry Sv39Tlb.entry tlb_set_pte
  rw [nextBase_setAD]
  simp only [PtTree.globalAfter, PtTree.global_setAD]
  rfl

theorem get_pte asid vpn p2 p1 word : tlb_get_pte 8 (entry asid vpn p2 p1 word) = word := by
  change word.extractLsb' 0 64 = word
  exact BitVec.extractLsb'_eq_self

set_option maxRecDepth 10000 in
theorem get_level asid vpn p2 p1 word : tlb_get_level 39 (entry asid vpn p2 p1 word) = 0 := by
  simp only [tlb_get_level, entry, Sv39Tlb.entry]
  simp [ForIn.forIn, ForIn'.forIn', IntRange.forIn', IntRange.forIn'.loop.eq_1,
    Membership.mem, _root_.Sail.BitVec.access]

theorem get_ppn asid vpn p2 p1 word query :
    tlb_get_ppn 39 (entry asid vpn p2 p1 word) query = PtTree.nextBase word := by
  unfold tlb_get_ppn entry Sv39Tlb.entry
  simp [zero_extend, sign_extend, trunc, _root_.Sail.BitVec.zeroExtend, _root_.Sail.BitVec.truncate,
    BitVec.setWidth_setWidth_of_le]

end Xv6.Kernel.TlbCoherence
