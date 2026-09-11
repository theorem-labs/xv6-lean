import Xv6.Kernel.Sv39WalkSpec
import Xv6.Kernel.KptLeafLink

namespace Xv6.Kernel.Sv39Walk
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

private theorem append_bit (x : BitVec 44) (y : BitVec 10) (i : Nat) :
    (BitVec.append x y).getLsbD i = if i < 10 then y.getLsbD i else x.getLsbD (i - 10) :=
  @BitVec.getLsbD_append 44 10 i x y

theorem pointer_flags (ppn : BitVec 44) : PteCanonical.flags (pointer ppn) = 1#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h10 : i < 10 := by omega
  have h64 : i < 64 := by omega
  simp only [PteCanonical.flags, Mk_PTE_Flags, _root_.Sail.BitVec.extractLsb, pointer,
    BitVec.zeroExtend, BitVec.getLsbD_extractLsb, BitVec.getLsbD_setWidth, append_bit]
  simp [hi, h10, h64]

theorem pointer_ppn (ppn : BitVec 44) : PPN_of_PTE (pointer ppn) = ppn := by
  change (pointer ppn).extractLsb 53 10 = ppn
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 44 at hi
  have h64 : 10 + i < 64 := by omega
  have h10 : ¬10 + i < 10 := by omega
  simp only [pointer, BitVec.zeroExtend, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_setWidth, append_bit, hi, h10, h64]
  simp [hi]

theorem pointer_ext (ppn : BitVec 44) : ext_bits_of_PTE (pointer ppn) = 0#10 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h64 : 54 + i < 64 := by omega
  simp only [ext_bits_of_PTE, Mk_PTE_Ext, _root_.Sail.BitVec.length,
    _root_.Sail.BitVec.extractLsb, pointer, BitVec.zeroExtend]
  simp [hi, h64]

theorem pointer_nonleaf (ppn : BitVec 44) : PteCanonical.nonleaf (pointer ppn) = true := by
  unfold PteCanonical.nonleaf
  rw [pointer_flags]
  rfl

theorem pointer_valid (rs : RegisterFile) (ppn : BitVec 44) : RegisterPlan.Returns [] rs
    (pte_is_invalid (PteCanonical.flags (pointer ppn)) (ext_bits_of_PTE (pointer ppn))) false rs := by
  rw [pointer_flags, pointer_ext]
  unfold pte_is_invalid
  simp only [currentlyEnabled]
  apply RegisterPlan.Plan.readAny
  intro environment1
  apply RegisterPlan.Plan.readAny
  intro isa1
  apply RegisterPlan.Plan.readAny
  intro isa2
  apply RegisterPlan.Plan.readAny
  intro environment2
  apply RegisterPlan.Plan.readAny
  intro isa3
  exact .pure ⟨rfl, rfl⟩

theorem leaf_variant (ppn : BitVec 44) (permission : KptLeaf.Permission) (w : BitVec 64)
    (same : PteCanonical.canon w = PteCanonical.canon (KptLeaf.word ppn permission false false)) :
    ∃ a d, w = KptLeaf.word ppn permission a d := by
  obtain ⟨a, d, hw⟩ := PteCanonical.canon_inv (KptLeaf.word ppn permission false false) w same
  rcases PteCanonical.bit1_cases a with rfl | rfl <;>
    rcases PteCanonical.bit1_cases d with rfl | rfl
  · exact ⟨false, false, hw.trans (KptLeaf.word_setAD ppn permission false false false false)⟩
  · exact ⟨false, true, hw.trans (KptLeaf.word_setAD ppn permission false false false true)⟩
  · exact ⟨true, false, hw.trans (KptLeaf.word_setAD ppn permission false false true false)⟩
  · exact ⟨true, true, hw.trans (KptLeaf.word_setAD ppn permission false false true true)⟩

theorem address_value (ppn : BitVec 44) (idx : BitVec 9) :
    (addressAt ppn idx).toNat = ppn.toNat * 4096 + idx.toNat * 8 := by
  have low : (BitVec.append idx 0#3).toNat = idx.toNat * 8 := by
    erw [@BitVec.toNat_append 9 3 idx 0#3]
    simp [Nat.shiftLeft_eq]
  change (BitVec.setWidth 64 (BitVec.append ppn (BitVec.append idx 0#3))).toNat = _
  erw [BitVec.toNat_setWidth_of_le (by decide), @BitVec.toNat_append 44 12 ppn (BitVec.append idx 0#3)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.append idx 0#3).isLt ppn.toNat, low]
  simp [Nat.shiftLeft_eq]

theorem address_aligned (ppn : BitVec 44) (idx : BitVec 9) :
    is_aligned_paddr (.Physaddr (addressAt ppn idx)) 8 = true := by
  change ((Int.tmod ((addressAt ppn idx).toNat : Int) 8) == 0) = true
  change ((((addressAt ppn idx).toNat % 8 : Nat) : Int) == 0) = true
  rw [address_value]
  simp [Nat.add_mod, Nat.mul_mod]

theorem pureSpec : PureSpec :=
  ⟨pointer_flags, pointer_ppn, pointer_ext, pointer_nonleaf, pointer_valid,
    address_value, address_aligned, leaf_variant⟩

end Xv6.Kernel.Sv39Walk
