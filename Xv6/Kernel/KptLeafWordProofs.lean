import Xv6.Kernel.KptLeafSpec
import MachCSL.Machine.PteCanonicalLink

namespace Xv6.Kernel.KptLeaf
open MachCSL.Machine LeanPaperStock.Functions

private theorem append_bit (x : BitVec 44) (y : BitVec 10) (i : Nat) :
    (BitVec.append x y).getLsbD i = if i < 10 then y.getLsbD i else x.getLsbD (i - 10) :=
  @BitVec.getLsbD_append 44 10 i x y

theorem word_flags (ppn : BitVec 44) (permission : Permission) (a d : Bool) :
    PteCanonical.flags (word ppn permission a d) = flagByte permission a d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h10 : i < 10 := by omega
  have h64 : i < 64 := by omega
  simp only [PteCanonical.flags, Mk_PTE_Flags, _root_.Sail.BitVec.extractLsb, word,
    BitVec.zeroExtend, BitVec.getLsbD_extractLsb, BitVec.getLsbD_setWidth, append_bit, hi]
  simp [hi, h10, h64]

theorem word_ppn (ppn : BitVec 44) (permission : Permission) (a d : Bool) :
    PPN_of_PTE (word ppn permission a d) = ppn := by
  change (word ppn permission a d).extractLsb 53 10 = ppn
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 44 at hi
  have h64 : 10 + i < 64 := by omega
  have h10 : ¬10 + i < 10 := by omega
  simp only [word, BitVec.zeroExtend, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_setWidth, append_bit, hi, h10, h64]
  simp [hi]

theorem word_ext (ppn : BitVec 44) (permission : Permission) (a d : Bool) :
    ext_bits_of_PTE (word ppn permission a d) = 0#10 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h64 : 54 + i < 64 := by omega
  simp only [ext_bits_of_PTE, Mk_PTE_Ext, _root_.Sail.BitVec.length,
    _root_.Sail.BitVec.extractLsb, word, BitVec.zeroExtend]
  simp [hi, h64]

theorem flag_nonleaf (permission : Permission) (a d : Bool) :
    pte_is_non_leaf (flagByte permission a d) = false := by
  cases permission <;> cases a <;> cases d <;> decide

theorem word_leaf (ppn : BitVec 44) (permission : Permission) (a d : Bool) :
    PteCanonical.Leaf (word ppn permission a d) := by
  unfold PteCanonical.Leaf PteCanonical.nonleaf
  rw [word_flags, flag_nonleaf]

theorem word_bit (ppn : BitVec 44) (permission : Permission) (a d : Bool)
    (i : Nat) (hi : i < 64) :
    (word ppn permission a d).getLsbD i =
      if i < 10 then (flagByte permission a d).getLsbD i else ppn.getLsbD (i - 10) := by
  simp only [word, BitVec.zeroExtend, BitVec.getLsbD_setWidth, append_bit]
  by_cases h10 : i < 10 <;> simp [hi, h10]

theorem word_setAD (ppn : BitVec 44) (permission : Permission) (a d a' d' : Bool) :
    PteCanonical.setAD (word ppn permission a d) (if a' then 1#1 else 0#1)
      (if d' then 1#1 else 0#1) = word ppn permission a' d' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [PteCanonical.setAD_bit _ _ _ _ hi, word_bit _ _ _ _ _ hi,
    word_bit _ _ _ _ _ hi]
  by_cases low : i < 10
  · have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases permission <;> cases a <;> cases d <;> cases a' <;> cases d' <;> rfl
  · have h6 : i ≠ 6 := by omega
    have h7 : i ≠ 7 := by omega
    simp [low, h6, h7]

theorem word_canonical (ppn : BitVec 44) (permission : Permission) (a d : Bool) :
    PteCanonical.canon (word ppn permission a d) = word ppn permission false false :=
  word_setAD ppn permission a d false false

theorem wordSpec : WordSpec :=
  ⟨word_flags, word_ppn, word_ext, word_leaf, word_setAD, word_canonical⟩

end Xv6.Kernel.KptLeaf
