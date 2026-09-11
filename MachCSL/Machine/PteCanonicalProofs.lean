import MachCSL.Machine.PteCanonicalSpec
import MachCSL.Machine.PteCanonicalBits

namespace MachCSL.Machine.PteCanonical
open LeanPaperStock.Functions MachCSL.Memory

theorem nthByte_bit {width : Nat} (w : BitVec width) (j k : Nat) (hk : k < 8) :
    (nthByte w j).getLsbD k = w.getLsbD (8 * j + k) := by
  simp only [nthByte, BitVec.getLsbD_ofNat, hk, decide_true, Bool.true_and,
    ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  rfl

theorem high_byte (w : BitVec 64) (a d : BitVec 1) (j : Nat) (positive : 0 < j) (hj : j < 8) :
    nthByte (setAD w a d) j = nthByte w j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [nthByte_bit _ _ _ hk, nthByte_bit _ _ _ hk, setAD_bit _ _ _ _ (by omega)]
  simp [show 8 * j + k ≠ 6 by omega, show 8 * j + k ≠ 7 by omega]

theorem bit1_cases (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  have bound := a.isLt
  have values : a.toNat = 0 ∨ a.toNat = 1 := by omega
  rcases values with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

theorem adByte0_mem (w : BitVec 64) (b : Byte) :
    b ∈ adByte0 w ↔
      b = nthByte (setAD w 0#1 0#1) 0 ∨ b = nthByte (setAD w 0#1 1#1) 0 ∨
      b = nthByte (setAD w 1#1 0#1) 0 ∨ b = nthByte (setAD w 1#1 1#1) 0 := by
  simp [adByte0]
  simp only [eq_comm]

theorem adByte0_variant (w : BitVec 64) (a d : BitVec 1) :
    nthByte (setAD w a d) 0 ∈ adByte0 w := by
  rw [adByte0_mem]
  rcases bit1_cases a with rfl | rfl <;> rcases bit1_cases d with rfl | rfl <;> simp

theorem adByte0_inv (w : BitVec 64) (b : Byte) (h : b ∈ adByte0 w) :
    ∃ a d, b = nthByte (setAD w a d) 0 := by
  rw [adByte0_mem] at h
  rcases h with h | h | h | h
  · exact ⟨0#1, 0#1, h⟩
  · exact ⟨0#1, 1#1, h⟩
  · exact ⟨1#1, 0#1, h⟩
  · exact ⟨1#1, 1#1, h⟩

theorem family_variant (w : BitVec 64) (a d : BitVec 1) (j : Nat) (leaf : Leaf w) (hj : j < 8) :
    slotSet (setAD w a d) j = slotSet w j := by
  change nonleaf w = false at leaf
  unfold slotSet
  rw [nonleaf_variant]
  by_cases zero : j = 0
  · simp [zero, leaf, adByte0, setAD_absorb]
  · simp [zero, high_byte w a d j (by omega) hj]

theorem slot_mem_variant (w : BitVec 64) (a d : BitVec 1) (j : Nat) (leaf : Leaf w) (hj : j < 8) :
    nthByte (setAD w a d) j ∈ slotSet w j := by
  change nonleaf w = false at leaf
  unfold slotSet
  by_cases zero : j = 0
  · subst j
    simpa [leaf] using adByte0_variant w a d
  · simp [zero, high_byte w a d j (by omega) hj]

theorem nonleaf_singleton (w : BitVec 64) (j : Nat) (h : nonleaf w = true) :
    slotSet w j = {nthByte w j} := by
  by_cases zero : j = 0 <;> simp [slotSet, h, zero]

theorem exact_nonleaf (w w' : BitVec 64) (h : nonleaf w = true)
    (mem : ∀ j, j < 8 → nthByte w' j ∈ slotSet w j) : w' = w := by
  apply bv_eq_of_bytes (n := 8)
  intro j hj
  have equal : nthByte w j = nthByte w' j := by
    simpa [nonleaf_singleton w j h] using mem j hj
  exact equal.symm

theorem bytes_variant (w w' : BitVec 64) (a d : BitVec 1)
    (low : nthByte w' 0 = nthByte (setAD w a d) 0)
    (high : ∀ j, 0 < j → j < 8 → nthByte w' j = nthByte w j) : w' = setAD w a d := by
  apply bv_eq_of_bytes (n := 8)
  intro j hj
  by_cases zero : j = 0
  · subst j; exact low
  · rw [high j (by omega) hj, high_byte w a d j (by omega) hj]

theorem canonical_read (w w' : BitVec 64)
    (mem : ∀ j, j < 8 → nthByte w' j ∈ slotSet w j) : canon w' = canon w := by
  cases h : nonleaf w with
  | true => rw [exact_nonleaf w w' h mem]
  | false =>
    have low : nthByte w' 0 ∈ adByte0 w := by simpa [slotSet, h] using mem 0 (by decide)
    obtain ⟨a, d, low⟩ := adByte0_inv w _ low
    have high : ∀ j, 0 < j → j < 8 → nthByte w' j = nthByte w j := by
      intro j positive hj
      have equal : nthByte w j = nthByte w' j := by
        simpa [slotSet, show j ≠ 0 by omega] using mem j hj
      exact equal.symm
    rw [bytes_variant w w' a d low high, canon_variant]

theorem family_read (w w' : BitVec 64) (leaf : Leaf w)
    (mem : ∀ j, j < 8 → nthByte w' j ∈ slotSet w j) :
    ∀ j, j < 8 → slotSet w' j = slotSet w j := by
  obtain ⟨a, d, rfl⟩ := canon_inv w w' (canonical_read w w' mem)
  exact fun j hj => family_variant w a d j leaf hj

theorem update_variant (w w' : BitVec 64) (access : MemoryAccessType mem_payload)
    (h : update_PTE_Bits w access = some w') : ∃ a d, w' = setAD w a d := by
  have result (b : Bool) (d : BitVec 1)
      (found : (if b then some (setAD w 1#1 d) else none) = some w') :
      ∃ a d, w' = setAD w a d := by
    cases b with
    | false => cases found
    | true => exact ⟨1#1, d, (Option.some.inj found).symm⟩
  exact result _ _ h

theorem writeback (w w' : BitVec 64) (access : MemoryAccessType mem_payload)
    (h : update_PTE_Bits w access = some w') (leaf : Leaf w) : WritebackOK w w' := by
  obtain ⟨a, d, rfl⟩ := update_variant w w' access h
  exact ⟨leaf, fun j hj => slot_mem_variant w a d j leaf hj⟩

theorem actual : Spec :=
  ⟨setAD_bit, setAD_absorb, canon_variant, canon_inv, nonleaf_variant, high_byte,
    family_variant, writeback, exact_nonleaf, canonical_read, family_read⟩

end MachCSL.Machine.PteCanonical
