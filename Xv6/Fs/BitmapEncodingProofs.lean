import Xv6.Fs.BitmapEncodingDefs
import Xv6.Fs.BitmapProofs

namespace Xv6.Fs.BitmapEncoding

theorem bitsToInt_nonnegative (bits : List Bool) : 0 ≤ bitsToInt bits := by
  induction bits with
  | nil => decide
  | cons b rest ih => cases b <;> simp only [bitsToInt] <;> omega

theorem bitsToInt_bound (bits : List Bool) : bitsToInt bits < (2 : Int) ^ bits.length := by
  induction bits with
  | nil => decide
  | cons b rest ih =>
    cases b <;> simp only [bitsToInt, List.length_cons, Int.pow_succ] <;> omega

theorem bitsToInt_testBit (bits : List Bool) (k : Nat) :
    (bitsToInt bits).toNat.testBit k = bits[k]?.getD false := by
  induction bits generalizing k with
  | nil => simp [bitsToInt]
  | cons b rest ih =>
    have nonneg := bitsToInt_nonnegative rest
    cases k with
    | zero =>
      cases b <;> simp only [bitsToInt, List.getElem?_cons_zero, Option.getD_some,
        Nat.testBit_zero, decide_eq_false_iff_not, decide_eq_true_eq] <;> omega
    | succ k =>
      cases b <;> simp only [bitsToInt, List.getElem?_cons_succ, Nat.testBit_succ]
      · have eq : (2 * bitsToInt rest).toNat / 2 = (bitsToInt rest).toNat := by omega
        rw [eq, ih]
      · have eq : (2 * bitsToInt rest + 1).toNat / 2 = (bitsToInt rest).toNat := by omega
        rw [eq, ih]

theorem byteBits_length (used : BlockSet) (j : Int) : (byteBits used j).length = 8 := by
  simp only [byteBits, List.length_map, List.length_range]

theorem byteBits_lookup (used : BlockSet) (j : Int) (k : Nat) (bound : k < 8) :
    (byteBits used j)[k]? = some (decide (8 * j + (k : Int) ∈ used)) := by
  simp only [byteBits, List.getElem?_map, List.getElem?_range bound, Option.map_some]

theorem bitmapByte_unsigned (used : BlockSet) (j : Int) :
    ((bitmapByte used j).toNat : Int) = bitsToInt (byteBits used j) := by
  have hn := bitsToInt_nonnegative (byteBits used j)
  have hb := bitsToInt_bound (byteBits used j)
  rw [byteBits_length] at hb
  unfold bitmapByte
  rw [BitVec.toNat_ofInt]
  change (((bitsToInt (byteBits used j)) % (2 ^ 8 : Int)).toNat : Int) = _
  rw [Int.emod_eq_of_lt hn hb, Int.toNat_of_nonneg hn]

theorem bitmapByte_bit (used : BlockSet) (j : Int) (k : Nat) (bound : k < 8) :
    (bitmapByte used j).getLsbD k = decide (8 * j + (k : Int) ∈ used) := by
  have hu := congrArg Int.toNat (bitmapByte_unsigned used j)
  simp only [Int.toNat_natCast] at hu
  change (bitmapByte used j).toNat.testBit k = _
  rw [hu, bitsToInt_testBit, byteBits_lookup used j k bound]
  rfl

theorem bitmapByte_high (used : BlockSet) (j : Int) (k : Nat) (bound : 8 ≤ k) :
    (bitmapByte used j).getLsbD k = false := BitVec.getLsbD_of_ge _ _ bound

theorem bitmapByte_ext (left right : BlockSet) (j : Int)
    (same : ∀ k : Int, 0 ≤ k ∧ k < 8 → (8 * j + k ∈ left ↔ 8 * j + k ∈ right)) :
    bitmapByte left j = bitmapByte right j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bitmapByte_bit left j k hk, bitmapByte_bit right j k hk]
  simp only [same (k : Int) ⟨by omega, by omega⟩]

theorem bitmapBytes_length (n : Nat) (used : BlockSet) : (bitmapBytes n used).length = n := by
  simp only [bitmapBytes, List.length_map, List.length_range]

theorem bitmapBytes_lookup (n : Nat) (used : BlockSet) (j : Nat) (bound : j < n) :
    (bitmapBytes n used)[j]? = some (bitmapByte used (j : Int)) := by
  simp only [bitmapBytes, List.getElem?_map, List.getElem?_range bound, Option.map_some]

theorem bitmapBytes_lookup_out (n : Nat) (used : BlockSet) (j : Nat) (bound : n ≤ j) :
    (bitmapBytes n used)[j]? = none := List.getElem?_eq_none (by rw [bitmapBytes_length]; exact bound)

theorem bit_split (b : Int) : 8 * (b / 8) + b % 8 = b := by omega

theorem bit_byte (j k : Int) (bound : 0 ≤ k ∧ k < 8) : (8 * j + k) / 8 = j := by omega

theorem bit_offset (j k : Int) (bound : 0 ≤ k ∧ k < 8) : (8 * j + k) % 8 = k := by omega

theorem bitmapBytes_bit (n : Nat) (used : BlockSet) (b : Int)
    (bound : 0 ≤ b ∧ b < 8 * (n : Int)) :
    bitmapBit (bitmapBytes n used) b = decide (b ∈ used) := by
  unfold bitmapBit
  rw [bitmapBytes_lookup n used (b / 8).toNat (by omega), Option.getD_some]
  rw [Int.toNat_of_nonneg (by omega), bitmapByte_bit used (b / 8) (b % 8).toNat (by omega)]
  rw [Int.toNat_of_nonneg (by omega), bit_split]

/-- Full byte identity, including bits beyond a filesystem's advertised size. -/
theorem bitmapBytes_roundtrip (n : Nat) (bytes : List (BitVec 8)) (length : bytes.length = n) :
    bitmapBytes n (bitmapSet n bytes) = bytes := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [bitmapBytes_lookup n _ j hj, List.getElem?_eq_getElem (by omega)]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [bitmapByte_bit _ _ k hk]
    have range : 0 ≤ 8 * (j : Int) + (k : Int) ∧
        8 * (j : Int) + (k : Int) < 8 * (n : Int) := by omega
    have hb : bitmapBit bytes (8 * (j : Int) + (k : Int)) = bytes[j].getLsbD k := by
      unfold bitmapBit
      rw [bit_byte _ _ ⟨by omega, by omega⟩, bit_offset _ _ ⟨by omega, by omega⟩]
      simp only [Int.toNat_natCast]
      rw [List.getElem?_eq_getElem (show j < bytes.length by omega), Option.getD_some]
    have member := bitmapSet_mem n bytes (8 * (j : Int) + (k : Int))
    rw [hb] at member
    simp only [member, range, true_and]
    cases bytes[j].getLsbD k <;> rfl
  · rw [bitmapBytes_lookup_out n _ j (by omega), List.getElem?_eq_none (by omega)]

theorem bitmapBytes_update (n : Nat) (left right : BlockSet) (j : Int)
    (nonnegative : 0 ≤ j) (bound : j.toNat < n)
    (same : ∀ x : Int, 0 ≤ x → x / 8 ≠ j → (x ∈ left ↔ x ∈ right)) :
    (bitmapBytes n left).set j.toNat (bitmapByte right j) = bitmapBytes n right := by
  apply List.ext_getElem?
  intro i
  by_cases equal : i = j.toNat
  · subst i
    rw [List.getElem?_set_self (by rw [bitmapBytes_length]; exact bound),
      bitmapBytes_lookup n right j.toNat bound, Int.toNat_of_nonneg nonnegative]
  · rw [List.getElem?_set_ne (Ne.symm equal)]
    by_cases hi : i < n
    · rw [bitmapBytes_lookup n left i hi, bitmapBytes_lookup n right i hi]
      congr 1
      apply bitmapByte_ext
      intro k hk
      apply same
      · omega
      · rw [bit_byte _ _ hk]
        omega
    · rw [bitmapBytes_lookup_out n left i (by omega), bitmapBytes_lookup_out n right i (by omega)]

theorem bitmapBytes_set (n : Nat) (used : BlockSet) (bit : Int)
    (nonnegative : 0 ≤ bit) (bound : (bit / 8).toNat < n) :
    (bitmapBytes n used).set (bit / 8).toNat (bitmapByte (used.insert bit) (bit / 8)) =
      bitmapBytes n (used.insert bit) := by
  apply bitmapBytes_update n used (used.insert bit) (bit / 8) (by omega) bound
  intro x hx different
  simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_eq_iff_eq]
  have ne : bit ≠ x := by intro eq; subst bit; exact different rfl
  simp only [ne, false_or]

theorem bitmapBytes_clear (n : Nat) (used : BlockSet) (bit : Int)
    (nonnegative : 0 ≤ bit) (bound : (bit / 8).toNat < n) :
    (bitmapBytes n used).set (bit / 8).toNat (bitmapByte (used.erase bit) (bit / 8)) =
      bitmapBytes n (used.erase bit) := by
  apply bitmapBytes_update n used (used.erase bit) (bit / 8) (by omega) bound
  intro x hx different
  simp only [Std.ExtTreeSet.mem_erase]
  have compare_ne : compare bit x ≠ .eq := by
    intro eq
    have same := Std.compare_eq_eq_iff_eq.mp eq
    subst bit
    exact different rfl
  exact ⟨fun hx => ⟨compare_ne, hx⟩, fun hx => hx.2⟩

/-- Decoding an encoder restricts only to the byte image's actual bit range. -/
theorem bitmapSet_encoded_mem (n : Nat) (used : BlockSet) (bit : Int) :
    bit ∈ bitmapSet n (bitmapBytes n used) ↔
      (0 ≤ bit ∧ bit < 8 * (n : Int)) ∧ bit ∈ used := by
  rw [bitmapSet_mem]
  by_cases bound : 0 ≤ bit ∧ bit < 8 * (n : Int)
  · rw [bitmapBytes_bit n used bit bound]
    simp only [decide_eq_true_eq]
  · simp only [bound, false_and]

/-- Negative byte indices remain meaningful for the signed primitive. -/
theorem negative_byte_index :
    bitmapByte (Std.ExtTreeSet.ofList [(-1 : Int)]) (-1) = 128 := by
  unfold bitmapByte byteBits bitsToInt
  decide

/-- The top padding bit survives decoding and re-encoding. -/
theorem high_padding_preserved : bitmapBytes 1 (bitmapSet 1 [128]) = [128] :=
  bitmapBytes_roundtrip 1 [128] rfl

end Xv6.Fs.BitmapEncoding

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.BitmapEncoding." ||
        name.toString.startsWith "_private.Xv6.Fs.BitmapEncoding" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} bitmap-encoding declarations; standard foundational axioms only."
