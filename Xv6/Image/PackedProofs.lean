import Xv6.Image.Packed
import Init.Data.List.Range
import Init.Data.List.TakeDrop
import Init.Data.List.Monadic
import Lean.Elab.Tactic.Omega

/-!
Representation lemmas for the packed-page input format. `Covered` rules out
missing pages within the declared file extent. `toBytes` is a logical contiguous
view, not a second executable image decoder. No equality with the original hex
encoding or the Sail byte assembler is asserted by this module.
-/
namespace Xv6.Image

/-- Every byte in the declared file extent has a backing page. Extra pages and
high bits outside the declared extent are irrelevant to byte lookup. -/
def Packed.Covered (image : Packed) : Prop :=
  image.byteLength ≤ image.pages.length * 4096

/-- Extract a byte directly from its page; default a missing page to zero.
`Covered` proves this default is unused inside the declared file extent. -/
def Packed.pageByte (image : Packed) (offset : Nat) : UInt8 :=
  (((image.pages[offset / 4096]?.getD 0) >>> (8 * (offset % 4096))) % 256).toUInt8

/-- Contiguous logical view. Use coverage when relating it to partial access. -/
def Packed.toBytes (image : Packed) : List UInt8 :=
  (List.range image.byteLength).map image.pageByte

theorem Packed.toBytes_length (image : Packed) :
    image.toBytes.length = image.byteLength := by
  simp [Packed.toBytes]

/-- Coverage supplies the page needed for any in-bounds address. -/
theorem Packed.page_index_lt (image : Packed) (hc : image.Covered)
    {offset : Nat} (ho : offset < image.byteLength) :
    offset / 4096 < image.pages.length := by
  unfold Packed.Covered at hc
  omega

theorem Packed.getByte?_eq_some_pageByte (image : Packed) (hc : image.Covered)
    {offset : Nat} (ho : offset < image.byteLength) :
    image.getByte? offset = some (image.pageByte offset) := by
  have hp := image.page_index_lt hc ho
  simp [Packed.getByte?, Packed.pageByte, ho, List.getElem?_eq_getElem hp]

/-- Every partial lookup agrees with ordinary contiguous list lookup. -/
theorem Packed.getByte?_eq_lookup (image : Packed) (hc : image.Covered)
    (offset : Nat) : image.getByte? offset = image.toBytes[offset]? := by
  by_cases ho : offset < image.byteLength
  · rw [image.getByte?_eq_some_pageByte hc ho]
    simp [Packed.toBytes, List.getElem?_range ho]
  · rw [image.getByte?_out_of_bounds (Nat.le_of_not_lt ho)]
    exact (List.getElem?_eq_none (by simpa [Packed.toBytes] using Nat.le_of_not_lt ho)).symm

/-- Any finite sequence of partial reads agrees with the contiguous view. -/
theorem Packed.mapM_getByte?_eq_lookup (image : Packed) (hc : image.Covered)
    (offsets : List Nat) :
    offsets.mapM image.getByte? = offsets.mapM (fun i => image.toBytes[i]?) := by
  have heq : image.getByte? = fun i => image.toBytes[i]? :=
    funext (image.getByte?_eq_lookup hc)
  rw [heq]

private theorem mapM_eq_some_map {α β : Type} (xs : List α)
    (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, h x (by simp), List.map_cons]
    rw [ih (fun y hy => h y (by simp [hy]))]
    rfl

/-- Successful bounded reads return the actual contiguous byte window. -/
theorem Packed.mapM_getByte?_eq_take_drop (image : Packed) (hc : image.Covered)
    (offset count : Nat) (hb : offset + count ≤ image.byteLength) :
    (List.range count).mapM (fun i => image.getByte? (offset + i)) =
      some ((image.toBytes.drop offset).take count) := by
  rw [mapM_eq_some_map (List.range count) _ (fun i => image.pageByte (offset + i))
    (fun i hi => image.getByte?_eq_some_pageByte hc (by
      have := List.mem_range.mp hi
      omega))]
  congr 1
  apply List.ext_getElem?
  intro i
  by_cases hi : i < count
  · rw [List.getElem?_map, List.getElem?_range hi, List.getElem?_take_of_lt hi]
    simp [List.getElem?_drop, Packed.toBytes, List.getElem?_range (show offset + i < image.byteLength by omega)]
  · have hi' : count ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_eq_none (by simpa using hi')]
    exact (List.getElem?_eq_none (by
      have := List.length_take_le count (image.toBytes.drop offset)
      omega)).symm

/-- The executable byte-array reader realizes a bounded contiguous window. -/
theorem Packed.readBytes?_eq_take_drop (image : Packed) (hc : image.Covered)
    (offset count : Nat) (hb : offset + count ≤ image.byteLength) :
    image.readBytes? offset count =
      some (ByteArray.mk (((image.toBytes.drop offset).take count).toArray)) := by
  unfold Packed.readBytes?
  have hi : offset ≤ image.byteLength ∧ count ≤ image.byteLength - offset :=
    ⟨by omega, by omega⟩
  rw [if_pos hi, image.mapM_getByte?_eq_take_drop hc offset count hb]
  rfl

end Xv6.Image
