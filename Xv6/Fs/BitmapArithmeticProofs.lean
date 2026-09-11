import Xv6.Fs.BitmapEncodingProofs
import Iris.Std.BitOp

/-! Exact BitmapEnc.v integer AND/OR/complement laws. Byte positions remain
signed; the nonnegative signed bit position is converted only for exponentiation. -/
namespace Xv6.Fs.BitmapArithmetic
open BitmapEncoding

theorem byte_and_nat (used : BlockSet) (j : Int) (k : Nat) (bound : k < 8) :
    (bitmapByte used j).toNat &&& 2 ^ k =
      if decide (8 * j + (k : Int) ∈ used) then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases same : k = i
  · subst i
    change ((bitmapByte used j).getLsbD k && decide (k = k)) = _
    rw [bitmapByte_bit used j k bound]
    split <;> simp_all
  · simp only [same, decide_false, Bool.and_false]
    split <;> simp [same]

theorem byte_or_nat (used : BlockSet) (j : Int) (k : Nat) (bound : k < 8) :
    (bitmapByte used j).toNat ||| 2 ^ k =
      (bitmapByte (used ∪ {8 * j + (k : Int)}) j).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  change ((bitmapByte used j).getLsbD i || decide (k = i)) =
    (bitmapByte (used ∪ {8 * j + (k : Int)}) j).getLsbD i
  by_cases low : i < 8
  · rw [bitmapByte_bit used j i low, bitmapByte_bit _ j i low]
    simp [show ((k : Int) = (i : Int)) ↔ k = i by omega]
  · rw [bitmapByte_high used j i (by omega), bitmapByte_high _ j i (by omega)]
    simp [show k ≠ i by omega]

theorem byte_diff_nat (used : BlockSet) (j : Int) (k : Nat) (_bound : k < 8) :
    FromMathlib.Nat.ldiff (bitmapByte used j).toNat (2 ^ k) =
      (bitmapByte (used \ {8 * j + (k : Int)}) j).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [FromMathlib.Nat.testBit_ldiff, Nat.testBit_two_pow]
  change ((bitmapByte used j).getLsbD i && !decide (k = i)) =
    (bitmapByte (used \ {8 * j + (k : Int)}) j).getLsbD i
  by_cases low : i < 8
  · rw [bitmapByte_bit used j i low, bitmapByte_bit _ j i low]
    simp [show ((k : Int) = (i : Int)) ↔ k = i by omega]
  · rw [bitmapByte_high used j i (by omega), bitmapByte_high _ j i (by omega)]
    simp

theorem bitmapByte_land_pow2 (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    FromMathlib.Int.land ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) =
      if decide (8 * j + k ∈ used) then (2 : Int) ^ k.toNat else 0 := by
  rw [show (2 : Int) ^ k.toNat = ((2 ^ k.toNat : Nat) : Int) by simp]
  have h := congrArg (fun n : Nat => (n : Int)) (byte_and_nat used j k.toNat (by omega))
  simpa only [FromMathlib.Int.land, FromMathlib.Int.lor, Int.not, Int.toNat_of_nonneg bound.1, apply_ite, Int.natCast_zero] using h

theorem bitmapByte_lor_pow2 (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    FromMathlib.Int.lor ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) =
      ((bitmapByte (used ∪ {8 * j + k}) j).toNat : Int) := by
  rw [show (2 : Int) ^ k.toNat = ((2 ^ k.toNat : Nat) : Int) by simp]
  have h := congrArg (fun n : Nat => (n : Int)) (byte_or_nat used j k.toNat (by omega))
  simpa only [FromMathlib.Int.land, FromMathlib.Int.lor, Int.not, Int.toNat_of_nonneg bound.1] using h

theorem bitmapByte_ldiff_pow2 (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    FromMathlib.Int.land ((bitmapByte used j).toNat : Int) (~~~((2 : Int) ^ k.toNat)) =
      ((bitmapByte (used \ {8 * j + k}) j).toNat : Int) := by
  rw [show (2 : Int) ^ k.toNat = ((2 ^ k.toNat : Nat) : Int) by simp]
  rw [show ~~~((2 ^ k.toNat : Nat) : Int) = Int.negSucc (2 ^ k.toNat) from rfl]
  have h := congrArg (fun n : Nat => (n : Int)) (byte_diff_nat used j k.toNat (by omega))
  simpa only [FromMathlib.Int.land, FromMathlib.Int.lor, Int.not, Int.toNat_of_nonneg bound.1] using h

theorem test_zero_iff (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    FromMathlib.Int.land ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) = 0 ↔
      8 * j + k ∉ used := by
  rw [bitmapByte_land_pow2 used j k bound]
  have nonzero : (2 : Int) ^ k.toNat ≠ 0 := Int.pow_ne_zero (by decide)
  simp [nonzero]

theorem test_nonzero_iff (used : BlockSet) (j k : Int) (bound : 0 ≤ k ∧ k < 8) :
    FromMathlib.Int.land ((bitmapByte used j).toNat : Int) ((2 : Int) ^ k.toNat) ≠ 0 ↔
      8 * j + k ∈ used := by
  simp only [ne_eq, test_zero_iff used j k bound, Classical.not_not]

/-- The signed quotient/remainder form also covers negative block indices. -/
theorem test_block_zero_iff (used : BlockSet) (block : Int) :
    FromMathlib.Int.land ((bitmapByte used (block / 8)).toNat : Int)
      ((2 : Int) ^ (block % 8).toNat) = 0 ↔ block ∉ used := by
  simpa only [bit_split] using test_zero_iff used (block / 8) (block % 8)
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

end Xv6.Fs.BitmapArithmetic
