import Xv6.Image.Hex
import Xv6.Image.PackedProofs
import MachCSL.Memory.ReadBytes

/-!
Kernel-checkable certificates relating strict hexadecimal decoding to packed
pages. Short `HexBlock` certificates compose by byte-aligned concatenation;
concrete string decomposition and arithmetic equalities remain proof obligations
for the generator. No native evaluator or untrusted byte default is used.
-/
namespace Xv6.Image

/-- Little-endian integer encoding; shares the already checked byte assembler. -/
def assembleLE (bytes : List UInt8) : Nat :=
  MachCSL.Memory.assembleBytes (bytes.map fun b => BitVec.ofNat 8 b.toNat)

@[simp] theorem assembleLE_nil : assembleLE [] = 0 := rfl

@[simp] theorem assembleLE_cons (byte : UInt8) (bytes : List UInt8) :
    assembleLE (byte :: bytes) = byte.toNat + 256 * assembleLE bytes := by
  simp [assembleLE, MachCSL.Memory.assembleBytes]

theorem assembleLE_bound (bytes : List UInt8) : assembleLE bytes < 2 ^ (8 * bytes.length) := by
  simpa [assembleLE] using MachCSL.Memory.assembleBytes_bound
    (bytes.map fun b => BitVec.ofNat 8 b.toNat)

theorem assembleLE_byte (bytes : List UInt8) (j : Nat) (hj : j < bytes.length) :
    ((assembleLE bytes >>> (8 * j)) % 256).toUInt8 = bytes[j] := by
  have h := MachCSL.Memory.assembleBytes_byte
    (bytes.map fun b => BitVec.ofNat 8 b.toNat) j (by simpa using hj)
  simp only [List.getElem_map, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (UInt8.toNat_lt bytes[j])] at h
  rw [Nat.shiftRight_eq_div_pow]
  change ((assembleLE bytes / 2 ^ (8 * j)) % 256).toUInt8 = bytes[j]
  rw [show (assembleLE bytes / 2 ^ (8 * j)) % 256 = bytes[j].toNat from h]
  simp

/-- Length is essential: integer zero alone cannot distinguish any number of zero bytes. -/
theorem assembleLE_injective_of_length (left right : List UInt8)
    (length : left.length = right.length) (value : assembleLE left = assembleLE right) :
    left = right := by
  apply List.ext_getElem length
  intro i hi hj
  rw [← assembleLE_byte left i hi, ← assembleLE_byte right i hj, value]

theorem assembleLE_append (left right : List UInt8) :
    assembleLE (left ++ right) = assembleLE left + 2 ^ (8 * left.length) * assembleLE right := by
  induction left with
  | nil => simp
  | cons byte rest ih =>
    rw [List.cons_append, assembleLE_cons, assembleLE_cons, ih]
    rw [List.length_cons, Nat.mul_succ, Nat.pow_add]
    change byte.toNat + 256 * (assembleLE rest + 2 ^ (8 * rest.length) * assembleLE right) =
      byte.toNat + 256 * assembleLE rest + (2 ^ (8 * rest.length) * 256) * assembleLE right
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

/-- Concatenating after a successful decode preserves byte alignment. -/
theorem decodeChars_append {left : List Char} {bytes : List UInt8}
    (decoded : decodeChars left = some bytes) (right : List Char) :
    decodeChars (left ++ right) = (decodeChars right).map (bytes ++ ·) := by
  induction left using decodeChars.induct generalizing bytes with
  | case1 =>
    simp only [decodeChars, Option.some.injEq] at decoded
    subst bytes
    simp
  | case2 a b rest ih =>
    cases ha : hexDigit a with
    | none => simp [decodeChars, ha] at decoded
    | some hi =>
      cases hb : hexDigit b with
      | none => simp [decodeChars, ha, hb] at decoded
      | some lo =>
        cases hr : decodeChars rest with
        | none => simp [decodeChars, ha, hb, hr] at decoded
        | some tail =>
          have heq : (hi * 16 + lo) :: tail = bytes := by simpa [decodeChars, ha, hb, hr] using decoded
          subst bytes
          simp only [List.cons_append, decodeChars, ha, hb]
          rw [ih hr]
          cases decodeChars right <;> rfl
  | case3 a => simp [decodeChars] at decoded

/-- A short block certificate. It names its exact decoded length and integer,
    while existentially hiding the potentially large decoded list. -/
def HexBlock (chars : List Char) (byteCount value : Nat) : Prop :=
  ∃ bytes, decodeChars chars = some bytes ∧ bytes.length = byteCount ∧ assembleLE bytes = value

/-- Compact leaf-check proposition for generated certificates. The proof can
    reduce a short decoder call without spelling its intermediate byte list. -/
theorem HexBlock.of_check
    (checked : (decodeChars chars).map (fun bytes => (bytes.length, assembleLE bytes)) =
      some (byteCount, value)) : HexBlock chars byteCount value := by
  obtain ⟨bytes, decoded, fields⟩ := Option.map_eq_some_iff.mp checked
  exact ⟨bytes, decoded, congrArg Prod.fst fields, congrArg Prod.snd fields⟩

theorem HexBlock.check (cert : HexBlock chars byteCount value) :
    (decodeChars chars).map (fun bytes => (bytes.length, assembleLE bytes)) =
      some (byteCount, value) := by
  obtain ⟨bytes, decoded, length, value⟩ := cert
  simp [decoded, length, value]

theorem HexBlock.append (left : HexBlock chars1 n1 value1) (right : HexBlock chars2 n2 value2) :
    HexBlock (chars1 ++ chars2) (n1 + n2) (value1 + 2 ^ (8 * n1) * value2) := by
  obtain ⟨bytes1, decode1, length1, value1⟩ := left
  obtain ⟨bytes2, decode2, length2, value2⟩ := right
  refine ⟨bytes1 ++ bytes2, ?_, by simp [length1, length2], ?_⟩
  · rw [decodeChars_append decode1, decode2]
    rfl
  · rw [assembleLE_append, length1, value1, value2]

theorem HexBlock.append_strings {s1 s2 : String}
    (left : HexBlock s1.toList n1 value1) (right : HexBlock s2.toList n2 value2) :
    HexBlock (s1 ++ s2).toList (n1 + n2) (value1 + 2 ^ (8 * n1) * value2) := by
  rw [String.toList_append]
  exact left.append right

/-- Convenient string-level spelling for generated short-block certificates. -/
abbrev HexBlockString (s : String) (byteCount value : Nat) : Prop :=
  HexBlock s.toList byteCount value

theorem hexBlockString_append {s1 s2 : String}
    (left : HexBlockString s1 n1 value1) (right : HexBlockString s2 n2 value2) :
    HexBlockString (s1 ++ s2) (n1 + n2) (value1 + 2 ^ (8 * n1) * value2) :=
  HexBlock.append_strings left right

/-- A page layout with full nonfinal pages and a possibly short final page. -/
inductive PageBytes : List UInt8 → List Nat → Prop
  | nil : PageBytes [] []
  | full (block tail : List UInt8) (length : block.length = 4096)
      (rest : PageBytes tail pages) : PageBytes (block ++ tail) (assembleLE block :: pages)
  | last (block : List UInt8) (length : block.length ≤ 4096) :
      PageBytes block [assembleLE block]

theorem PageBytes.covered (cert : PageBytes bytes pages) :
    (Packed.mk bytes.length pages).Covered := by
  induction cert with
  | nil => simp [Packed.Covered]
  | full block tail length rest ih =>
    simp only [Packed.Covered, List.length_append, List.length_cons] at *
    omega
  | last block length => simpa [Packed.Covered] using length

/-- Every lookup, including out-of-bounds lookups, agrees with the certified bytes. -/
theorem PageBytes.lookup (cert : PageBytes bytes pages) (offset : Nat) :
    (Packed.mk bytes.length pages).getByte? offset = bytes[offset]? := by
  induction cert generalizing offset with
  | nil => simp [Packed.getByte?]
  | last block length =>
    by_cases within : offset < block.length
    · have small : offset < 4096 := by omega
      simp [Packed.getByte?, within, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small,
        assembleLE_byte block offset within]
    · simp [Packed.getByte?, within]
  | full block tail length rest ih =>
    by_cases small : offset < 4096
    · have within : offset < (block ++ tail).length := by simp only [List.length_append]; omega
      have inBlock : offset < block.length := by omega
      have within' : offset < block.length + tail.length := by simpa using within
      simp [Packed.getByte?, within', Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small,
        assembleLE_byte block offset inBlock, List.getElem_append_left inBlock]
    · have divEq : offset / 4096 = (offset - 4096) / 4096 + 1 := by omega
      have modEq : offset % 4096 = (offset - 4096) % 4096 := by omega
      have boundEq : (offset < (block ++ tail).length) ↔ offset - 4096 < tail.length := by
        simp only [List.length_append]; omega
      rw [List.getElem?_append_right (by omega : block.length ≤ offset), length]
      rw [← ih (offset - 4096)]
      simp only [Packed.getByte?, boundEq, divEq, modEq, List.getElem?_cons_succ]

theorem PageBytes.toBytes (cert : PageBytes bytes pages) :
    (Packed.mk bytes.length pages).toBytes = bytes := by
  apply List.ext_getElem?
  intro offset
  rw [← Packed.getByte?_eq_lookup _ cert.covered, cert.lookup]

/-- Whole-image certificates mirror the generator's page/chunk order. The last
    constructor allows zero bytes, while all preceding chunks have exactly 4096. -/
inductive HexPages : List String → List Nat → Nat → Prop
  | nil : HexPages [] [] 0
  | full (head : HexBlockString chunk 4096 page)
      (tail : HexPages chunks pages n) : HexPages (chunk :: chunks) (page :: pages) (4096 + n)
  | last (head : HexBlockString chunk n page) (length : n ≤ 4096) :
      HexPages [chunk] [page] n

/-- Decoder flattening is literal; it neither inserts padding nor drops chunks. -/
theorem decodeChunks_of_parts (decoded : chunks.mapM (fun chunk => decodeChars chunk.toList) = some parts) :
    decodeChunks chunks = some (ByteArray.mk parts.flatten.toArray) := by
  simp [decodeChunks, decoded]

private theorem HexPages.parts (cert : HexPages chunks pages n) :
    ∃ parts : List (List UInt8),
      chunks.mapM (fun chunk => decodeChars chunk.toList) = some parts ∧
      parts.flatten.length = n ∧ PageBytes parts.flatten pages := by
  induction cert with
  | nil => exact ⟨[], rfl, rfl, .nil⟩
  | @full chunk page chunks pages n head tail ih =>
    obtain ⟨block, decoded, length, value⟩ := head
    obtain ⟨parts, decodedRest, total, packed⟩ := ih
    refine ⟨block :: parts, ?_, ?_, ?_⟩
    · simp [List.mapM_cons, decoded, decodedRest]
    · simp [length, total]
    · simp only [List.flatten_cons]
      rw [← value]
      exact .full block parts.flatten length packed
  | @last chunk n page head length =>
    obtain ⟨block, decoded, blockLength, value⟩ := head
    refine ⟨[block], ?_, by simpa using blockLength, ?_⟩
    · simp [List.mapM_cons, decoded]
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [← value]
      exact .last block (by omega)

/-- All per-page certificates compose into exact original-hex/packed equality. -/
theorem HexPages.decode_eq (cert : HexPages chunks pages n) :
    decodeChunks chunks = some (ByteArray.mk (Packed.mk n pages).toBytes.toArray) := by
  obtain ⟨parts, decoded, length, packed⟩ := cert.parts
  have bytes := packed.toBytes
  rw [length] at bytes
  rw [bytes]
  exact decodeChunks_of_parts decoded

theorem HexPages.covered (cert : HexPages chunks pages n) : (Packed.mk n pages).Covered := by
  obtain ⟨parts, _, length, packed⟩ := cert.parts
  rw [← length]
  exact packed.covered

/-- Lookup form for clients that already have a successful strict hex decode. -/
theorem HexPages.lookup (cert : HexPages chunks pages n)
    (decoded : decodeChunks chunks = some raw) (offset : Nat) :
    (Packed.mk n pages).getByte? offset = raw.data.toList[offset]? := by
  rw [cert.decode_eq] at decoded
  have rawEq := Option.some.inj decoded
  subst raw
  simpa using (Packed.mk n pages).getByte?_eq_lookup cert.covered offset

/-- Record-oriented wrapper for the generated `Packed` constants. -/
theorem Packed.decode_eq_of_hexPages (image : Packed)
    (cert : HexPages chunks image.pages image.byteLength) :
    decodeChunks chunks = some (ByteArray.mk image.toBytes.toArray) := by
  cases image
  exact cert.decode_eq

/-- Certificate-oriented partial lookup wrapper for the generated image record. -/
theorem Packed.lookup_eq_of_hexPages (image : Packed)
    (cert : HexPages chunks image.pages image.byteLength)
    (decoded : decodeChunks chunks = some raw) (offset : Nat) :
    image.getByte? offset = raw.data.toList[offset]? := by
  cases image
  exact cert.lookup decoded offset

end Xv6.Image
