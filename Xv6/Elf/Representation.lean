import Xv6.Elf.Proofs
import Xv6.Image.PackedProofs

/-!
The packed ELF reader agrees with a contiguous-list reader when all declared
file bytes have backing pages. This proves the representation change inside
Lean, including failure and zero-width behavior. The integer assembler bridge
below is mathematical; it is not a cross-prover equivalence certificate for
Rocq or a substitute for correspondence with the generated Sail byte routines.
-/
namespace Xv6.Elf

/-- The integer fold corresponding to `RiscvModelBytes.assemble_bytes`
(line 108 at the paper pin), with unsigned `UInt8` values and `2^8 = 256`. -/
def assembleLEInt (bytes : List UInt8) : Int :=
  bytes.foldr (fun byte rest => (byte.toNat : Int) + 256 * rest) 0

/-- Casting the natural-number assembler preserves every unsigned byte value. -/
theorem assembleLE_cast (bytes : List UInt8) :
    (assembleLE bytes : Int) = assembleLEInt bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [assembleLE, assembleLEInt, List.foldr_cons,
      Int.natCast_add, Int.natCast_mul]
    rw [ih]
    rfl

/-- Contiguous ELF file reader. Positive-width availability is exactly the
file-bound check; an empty read succeeds at every nonnegative offset. -/
def readList (bytes : List UInt8) (offset : Int) (width : Nat) : Option Int :=
  if offset < 0 then none
  else if width = 0 then some 0
  else if offset + (width : Int) ≤ (bytes.length : Int) then
    some (assembleLE ((bytes.drop offset.toNat).take width) : Int)
  else none

private theorem mapM_none_of_mem {α β : Type} (xs : List α)
    (f : α → Option β) {x : α} (hx : x ∈ xs) (hf : f x = none) :
    xs.mapM f = none := by
  induction xs with
  | nil => simp at hx
  | cons a rest ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst a
      simp [List.mapM_cons, hf]
    · rw [List.mapM_cons, ih h]
      cases f a <;> rfl

/-- The packed reader rejects a nonempty window whose last byte is outside EOF.
This direction does not require coverage: an out-of-bounds byte always fails. -/
theorem read_past_end (f : Image.Packed) (offset : Int) (width : Nat)
    (ho : 0 ≤ offset) (hw : 0 < width)
    (hb : (f.byteLength : Int) < offset + (width : Int)) :
    read f offset width = none := by
  have hlast : width - 1 ∈ List.range width := List.mem_range.mpr (by omega)
  have heof : f.byteLength ≤ offset.toNat + (width - 1) := by omega
  have hm := mapM_none_of_mem (List.range width)
    (fun i => f.getByte? (offset.toNat + i)) hlast
    (f.getByte?_out_of_bounds heof)
  simp [read, show ¬ offset < 0 by omega, show width ≠ 0 by omega, hm]

/-- Full reader equality, including negative, empty, truncated and valid reads. -/
theorem read_eq_readList (f : Image.Packed) (hc : f.Covered)
    (offset : Int) (width : Nat) :
    read f offset width = readList f.toBytes offset width := by
  by_cases ho : offset < 0
  · simp [read, readList, ho]
  · by_cases hz : width = 0
    · simp [read, readList, ho, hz]
    · by_cases hb : offset + (width : Int) ≤ (f.byteLength : Int)
      · have hbn : offset.toNat + width ≤ f.byteLength := by omega
        simp only [read, readList, ho, hz, if_false, Image.Packed.toBytes_length,
          hb, if_true]
        rw [f.mapM_getByte?_eq_take_drop hc offset.toNat width hbn]
        rfl
      · rw [read_past_end f offset width (by omega) (by omega) (by omega)]
        simp [readList, ho, hz, Image.Packed.toBytes_length, hb]

theorem readList_negative (bytes : List UInt8) {offset : Int}
    (ho : offset < 0) (width : Nat) : readList bytes offset width = none := by
  simp [readList, ho]

theorem readList_empty (bytes : List UInt8) {offset : Int}
    (ho : 0 ≤ offset) : readList bytes offset 0 = some 0 := by
  simp [readList, show ¬ offset < 0 by omega]

/-- Exact positive-width success criterion and value of the contiguous reader. -/
theorem readList_some_iff (bytes : List UInt8) (offset : Int) (width : Nat)
    (hw : 0 < width) (value : Int) :
    readList bytes offset width = some value ↔
      0 ≤ offset ∧ offset + (width : Int) ≤ (bytes.length : Int) ∧
      value = (assembleLE ((bytes.drop offset.toNat).take width) : Int) := by
  by_cases ho : offset < 0
  · simp [readList, ho, show ¬ 0 ≤ offset by omega]
  · have ho' : 0 ≤ offset := by omega
    by_cases hb : offset + (width : Int) ≤ (bytes.length : Int)
    · simp [readList, ho, ho', show width ≠ 0 by omega, hb, eq_comm]
    · simp [readList, ho, show width ≠ 0 by omega, hb]

/-- The packed reader has exactly the reference's positive-width availability
and assembled result once coverage is established. -/
theorem read_some_iff (f : Image.Packed) (hc : f.Covered)
    (offset : Int) (width : Nat) (hw : 0 < width) (value : Int) :
    read f offset width = some value ↔
      0 ≤ offset ∧ offset + (width : Int) ≤ (f.byteLength : Int) ∧
      value = (assembleLE ((f.toBytes.drop offset.toNat).take width) : Int) := by
  rw [read_eq_readList f hc, readList_some_iff _ _ _ hw]
  rw [Image.Packed.toBytes_length]

/-- Equivalent success statement using the integer little-endian fold. -/
theorem read_some_iff_int (f : Image.Packed) (hc : f.Covered)
    (offset : Int) (width : Nat) (hw : 0 < width) (value : Int) :
    read f offset width = some value ↔
      0 ≤ offset ∧ offset + (width : Int) ≤ (f.byteLength : Int) ∧
      value = assembleLEInt ((f.toBytes.drop offset.toNat).take width) := by
  rw [read_some_iff f hc offset width hw value, assembleLE_cast]

/-- For positive widths, a value is available exactly for a valid file window. -/
theorem read_available_iff (f : Image.Packed) (hc : f.Covered)
    (offset : Int) (width : Nat) (hw : 0 < width) :
    (∃ value, read f offset width = some value) ↔
      0 ≤ offset ∧ offset + (width : Int) ≤ (f.byteLength : Int) := by
  constructor
  · rintro ⟨value, hv⟩
    have hs := (read_some_iff f hc offset width hw value).mp hv
    exact ⟨hs.1, hs.2.1⟩
  · rintro ⟨ho, hb⟩
    refine ⟨(assembleLE ((f.toBytes.drop offset.toNat).take width) : Int), ?_⟩
    apply (read_some_iff f hc offset width hw _).mpr
    exact ⟨ho, hb, rfl⟩

end Xv6.Elf
