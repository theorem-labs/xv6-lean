/-! Strict decoding of generated image hex. File format validity is a separate obligation. -/
namespace Xv6.Image

/-- Accept exactly ASCII hex digits. -/
def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Each byte must have two digits; malformed or truncated input is rejected. -/
def decodeChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    let tail ← decodeChars rest
    return (hi * 16 + lo) :: tail
  | [_] => none

/-- Decode byte-aligned chunks, preserving chunk order. -/
def decodeChunks (chunks : List String) : Option ByteArray := do
  let parts ← chunks.mapM fun chunk => decodeChars chunk.toList
  return ByteArray.mk (parts.flatten.toArray)

theorem decode_empty : decodeChunks [] = some ByteArray.empty := rfl

theorem reject_truncated : decodeChars ['a'] = none := rfl

theorem reject_nonhex : decodeChars ['g', '0'] = none := by decide

end Xv6.Image
