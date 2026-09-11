import MachCSL.Machine.PteCanonicalDefs

namespace MachCSL.Machine.PteCanonical
open LeanPaperStock.Functions MachCSL.Memory

theorem setAD_bit (w : BitVec 64) (a d : BitVec 1) (i : Nat) (hi : i < 64) :
    (setAD w a d).getLsbD i =
      if i = 6 then a.getLsbD 0 else if i = 7 then d.getLsbD 0 else w.getLsbD i := by
  simp only [setAD, flags, Mk_PTE_Flags, _update_PTE_Flags_A, _update_PTE_Flags_D,
    _root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange',
    _root_.Sail.BitVec.extractLsb, BitVec.zeroExtend, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_extractLsb]
  split <;> rename_i h6
  · subst i; simp
  · split <;> rename_i h7
    · subst i; simp
    · have low : i < 6 ∨ 8 ≤ i := by omega
      rcases low with low | low
      · have h8 : i < 8 := by omega
        have h7 : i < 7 := by omega
        simp [hi, low, h8, h7]
      · have h8 : ¬ i < 8 := by omega
        simp [hi, h8]


theorem setAD_absorb (w : BitVec 64) (a d a' d' : BitVec 1) :
    setAD (setAD w a d) a' d' = setAD w a' d' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [setAD_bit _ _ _ _ hi, setAD_bit _ _ _ _ hi, setAD_bit _ _ _ _ hi]
  split <;> simp_all

theorem canon_variant (w : BitVec 64) (a d : BitVec 1) :
    canon (setAD w a d) = canon w := setAD_absorb w a d 0#1 0#1

theorem flags_a (w : BitVec 64) : (_get_PTE_Flags_A (flags w)).getLsbD 0 = w.getLsbD 6 := by
  simp [flags, Mk_PTE_Flags, _get_PTE_Flags_A, _root_.Sail.BitVec.extractLsb]

theorem flags_d (w : BitVec 64) : (_get_PTE_Flags_D (flags w)).getLsbD 0 = w.getLsbD 7 := by
  simp [flags, Mk_PTE_Flags, _get_PTE_Flags_D, _root_.Sail.BitVec.extractLsb]

theorem setAD_refl (w : BitVec 64) :
    setAD w (_get_PTE_Flags_A (flags w)) (_get_PTE_Flags_D (flags w)) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [setAD_bit _ _ _ _ hi, flags_a, flags_d]
  split <;> simp_all

theorem canon_inv (w w' : BitVec 64) (h : canon w' = canon w) :
    ∃ a d, w' = setAD w a d := by
  refine ⟨_get_PTE_Flags_A (flags w'), _get_PTE_Flags_D (flags w'), ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [setAD_bit _ _ _ _ hi, flags_a, flags_d]
  have bit := congrArg (fun v : BitVec 64 => v.getLsbD i) h
  simp only [canon, setAD_bit _ _ _ _ hi] at bit
  split <;> simp_all
  split <;> simp_all

theorem extract_unchanged (w : BitVec 64) (a d : BitVec 1) (lo hi : Nat)
    (ordered : lo ≤ hi) (bound : hi < 64) (apart : hi < 6 ∨ 7 < lo) :
    _root_.Sail.BitVec.extractLsb (setAD w a d) hi lo =
      _root_.Sail.BitVec.extractLsb w hi lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  simp only [_root_.Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb]
  by_cases valid : lo + i < 64
  · rw [setAD_bit _ _ _ _ valid]
    have h6 : lo + i ≠ 6 := by omega
    have h7 : lo + i ≠ 7 := by omega
    simp [h6, h7]
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt valid]

theorem nonleaf_variant (w : BitVec 64) (a d : BitVec 1) :
    nonleaf (setAD w a d) = nonleaf w := by
  have get (j : Nat) (hj : j < 4) : (setAD w a d).getLsbD j = w.getLsbD j := by
    rw [setAD_bit _ _ _ _ (by omega)]
    simp [show j ≠ 6 by omega, show j ≠ 7 by omega]
  have extract (j : Nat) (hj : j < 4) :
      _root_.Sail.BitVec.extractLsb (flags (setAD w a d)) j j =
        _root_.Sail.BitVec.extractLsb (flags w) j j := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [flags, Mk_PTE_Flags, _root_.Sail.BitVec.extractLsb, get j hj]
  simp only [nonleaf, pte_is_non_leaf, _get_PTE_Flags_X, _get_PTE_Flags_W, _get_PTE_Flags_R,
    extract 3 (by decide), extract 2 (by decide), extract 1 (by decide)]

end MachCSL.Machine.PteCanonical
