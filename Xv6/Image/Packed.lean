/-! Pure packed image data with bounded, partial byte access. -/
namespace Xv6.Image

/-- Little-endian 4096-byte pages. `byteLength` excludes padding in the last page. -/
structure Packed where
  byteLength : Nat
  pages : List Nat

/-- Read one byte. Out-of-bounds addresses and absent pages return `none`. -/
def Packed.getByte? (image : Packed) (offset : Nat) : Option UInt8 :=
  if offset < image.byteLength then
    image.pages[offset / 4096]?.map fun page =>
      ((page >>> (8 * (offset % 4096))) % 256).toUInt8
  else none

/-- Read exactly `count` bytes or reject the entire read. -/
def Packed.readBytes? (image : Packed) (offset count : Nat) : Option ByteArray :=
  if offset ≤ image.byteLength ∧ count ≤ image.byteLength - offset then do
    let bytes ← (List.range count).mapM fun i => image.getByte? (offset + i)
    return ByteArray.mk bytes.toArray
  else none

/-- The explicit byte length prevents reading padding beyond the image. -/
theorem Packed.getByte?_out_of_bounds (image : Packed) {offset : Nat}
    (h : image.byteLength ≤ offset) : image.getByte? offset = none := by
  simp [Packed.getByte?, Nat.not_lt.mpr h]

end Xv6.Image
