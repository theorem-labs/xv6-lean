import Xv6.Fs.BitmapArithmeticProofs

/-! Mathematical 64-bit zero-extension/shift bridges for BitmapEnc arithmetic.
These are value equalities, not machine-instruction WPs. -/
namespace Xv6.Fs.BitmapArithmetic
open BitmapEncoding

def byteWord (used : BlockSet) (j : Int) : BitVec 64 :=
  (bitmapByte used j).zeroExtend 64

def bitMask (k : Int) : BitVec 64 := 1#64 <<< k.toNat

theorem byteWord_toNat (used : BlockSet) (j : Int) :
    (byteWord used j).toNat = (bitmapByte used j).toNat :=
  BitVec.toNat_setWidth_of_le (by decide)

theorem byteWord_bit (used : BlockSet) (j : Int) (i : Nat) :
    (byteWord used j).getLsbD i = (bitmapByte used j).getLsbD i := by
  change (byteWord used j).toNat.testBit i = (bitmapByte used j).toNat.testBit i
  rw [byteWord_toNat]

theorem bitMask_toNat (k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (bitMask k).toNat = 2 ^ k.toNat := by
  have fits : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  simp [bitMask, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt fits]

theorem bitMask_unsigned (k : Int) (bound : 0 ≤ k ∧ k < 8) :
    ((bitMask k).toNat : Int) = (2 : Int) ^ k.toNat := by
  rw [bitMask_toNat k bound]
  simp

theorem bitMask_bit (k : Int) (bound : 0 ≤ k ∧ k < 8) (i : Nat) :
    (bitMask k).getLsbD i = decide (k.toNat = i) := by
  change (bitMask k).toNat.testBit i = _
  rw [bitMask_toNat k bound, Nat.testBit_two_pow]

/-- A full machine-word shift operand denotes the same mask under the source
0≤k<8 guard; the shift count has not been silently truncated or changed. -/
theorem bitMask_word_shift (k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (1#64 <<< BitVec.ofInt 64 k) = bitMask k := by
  have count : (BitVec.ofInt 64 k).toNat = k.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt bound.1 (by omega)]
  change (1#64 <<< (BitVec.ofInt 64 k).toNat) = _
  rw [count]
  rfl

theorem word_test (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (byteWord used j &&& bitMask k) =
      if decide (8 * j + k ∈ used) then bitMask k else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, byteWord_toNat, bitMask_toNat k bound,
    byte_and_nat used j k.toNat (by omega)]
  simp only [Int.toNat_of_nonneg bound.1]
  split <;> simp_all [bitMask_toNat k bound]

theorem word_set (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (byteWord used j ||| bitMask k) = byteWord (used ∪ {8 * j + k}) j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, byteWord_toNat, bitMask_toNat k bound, byteWord_toNat]
  simpa only [Int.toNat_of_nonneg bound.1] using byte_or_nat used j k.toNat (by omega)

/-- The 64-bit complement equals the source infinite integer complement after
AND with the zero-extended byte; no high complement bits can enter the result. -/
theorem word_clear (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (byteWord used j &&& ~~~(bitMask k)) = byteWord (used \ {8 * j + k}) j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, byteWord_bit, bitMask_bit k bound, byteWord_bit]
  simp only [hi, decide_true, Bool.true_and]
  have h := congrArg (fun n : Nat => n.testBit i) (byte_diff_nat used j k.toNat (by omega))
  simpa only [BitVec.getLsbD, FromMathlib.Nat.testBit_ldiff, Nat.testBit_two_pow,
    Int.toNat_of_nonneg bound.1] using h

/-- The unsigned 64-bit result is exactly the source integer AND. -/
theorem word_test_unsigned (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    ((byteWord used j &&& bitMask k).toNat : Int) =
      FromMathlib.Int.land ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) := by
  rw [word_test used j k bound, bitmapByte_land_pow2 used j k bound]
  split <;> simp [bitMask_unsigned k bound]

theorem word_set_unsigned (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    ((byteWord used j ||| bitMask k).toNat : Int) =
      FromMathlib.Int.lor ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) := by
  rw [word_set used j k bound, byteWord_toNat, bitmapByte_lor_pow2 used j k bound]

/-- This connects finite-word complement directly to the source's unbounded
integer complement, after masking the zero-extended byte. -/
theorem word_clear_unsigned (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    ((byteWord used j &&& ~~~(bitMask k)).toNat : Int) =
      FromMathlib.Int.land ((bitmapByte used j).toNat : Int) (~~~((2 : Int) ^ k.toNat)) := by
  rw [word_clear used j k bound, byteWord_toNat, bitmapByte_ldiff_pow2 used j k bound]

theorem word_test_zero_iff (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    (byteWord used j &&& bitMask k) = 0#64 ↔ 8 * j + k ∉ used := by
  rw [word_test used j k bound]
  have nonzero : bitMask k ≠ 0#64 := by
    intro zero
    have h := congrArg BitVec.toNat zero
    rw [bitMask_toNat k bound] at h
    have pos := Nat.two_pow_pos k.toNat
    simp only [BitVec.toNat_zero] at h
    omega
  simp [nonzero]

theorem word_set_block (used : BlockSet) (block : Int) :
    (byteWord used (block / 8) ||| bitMask (block % 8)) =
      byteWord (used ∪ {block}) (block / 8) := by
  simpa only [bit_split] using word_set used (block / 8) (block % 8)
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem word_test_block_zero_iff (used : BlockSet) (block : Int) :
    (byteWord used (block / 8) &&& bitMask (block % 8)) = 0#64 ↔ block ∉ used := by
  simpa only [bit_split] using word_test_zero_iff used (block / 8) (block % 8)
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem word_clear_block (used : BlockSet) (block : Int) :
    (byteWord used (block / 8) &&& ~~~(bitMask (block % 8))) =
      byteWord (used \ {block}) (block / 8) := by
  simpa only [bit_split] using word_clear used (block / 8) (block % 8)
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

end Xv6.Fs.BitmapArithmetic
