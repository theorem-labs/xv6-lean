import MachCSL.Memory.ReadBytes

/-! Shared on-disk byte vocabulary from `FsImg.v`, `BlockWords.v` and
`FsCrash.v` at xv6iris arxiv-v1. Signed disk/block addresses are retained;
list lookup defaults to zero exactly as the source's total lookup. -/
namespace Xv6.Fs
open MachCSL.Memory

abbrev Disk := Int → Byte
abbrev Blocks := Int → List Byte

def blockSize : Nat := 1024
def blocks (disk : Disk) (block : Int) : List Byte :=
  (List.range blockSize).map fun i : Nat => disk (block * 1024 + (i : Int))

def byteAt (bytes : List Byte) (offset : Nat) : Byte := bytes[offset]?.getD 0

def leAt (bytes : List Byte) (offset count : Nat) : Int :=
  (assembleBytes ((List.range count).map fun j => byteAt bytes (offset + j)) : Int)

def wordBytes (word : BitVec (8 * n)) : List Byte :=
  (List.range n).map (nthByte word)

def halfBytes (word : BitVec 16) : List Byte := [nthByte word 0, nthByte word 1]
def word32Bytes (word : BitVec 32) : List Byte :=
  [nthByte word 0, nthByte word 1, nthByte word 2, nthByte word 3]

def indirectBytes : List (BitVec 32) → List Byte
  | [] => []
  | word :: rest => word32Bytes word ++ indirectBytes rest

theorem blocks_length (disk : Disk) (block : Int) : (blocks disk block).length = 1024 := by
  simp [blocks, blockSize]

theorem blocks_byte (disk : Disk) (block : Int) (offset : Nat) (bound : offset < 1024) :
    byteAt (blocks disk block) offset = disk (block * 1024 + offset) := by
  simp [blocks, blockSize, byteAt, List.getElem?_range bound]

theorem leAt_blocks (disk : Disk) (block : Int) (offset count : Nat)
    (bound : offset + count ≤ 1024) :
    leAt (blocks disk block) offset count =
      (assembleBytes ((List.range count).map fun j : Nat => disk (block * 1024 + ((offset + j : Nat) : Int))) : Int) := by
  unfold leAt
  apply congrArg Int.ofNat
  apply congrArg assembleBytes
  apply List.map_congr_left
  intro j hj
  rw [blocks_byte disk block (offset + j) (by have := List.mem_range.mp hj; omega)]

theorem wordBytes_length (word : BitVec (8 * n)) : (wordBytes word).length = n := by
  simp [wordBytes]

theorem wordBytes_byte (word : BitVec (8 * n)) (j : Nat) (bound : j < n) :
    (wordBytes word)[j]? = some (nthByte word j) := by
  simp [wordBytes, List.getElem?_range bound]

theorem wordBytes_decode (word : BitVec (8 * n)) :
    BitVec.ofNat (8 * n) (assembleBytes (wordBytes word)) = word := by
  apply bv_eq_of_bytes
  intro j hj
  rw [nthByte_assemble_len (8 * n) (wordBytes word) j
    (by simp [wordBytes_length]) (by simpa [wordBytes_length] using hj)]
  simp [wordBytes]

theorem leAt_word (bytes : List Byte) (offset n : Nat) (word : BitVec (8 * n))
    (fields : ∀ j, j < n → byteAt bytes (offset + j) = nthByte word j) :
    BitVec.ofInt (8 * n) (leAt bytes offset n) = word := by
  have h : (List.range n).map (fun j => byteAt bytes (offset + j)) = wordBytes word := by
    apply List.map_congr_left
    intro j hj
    exact fields j (List.mem_range.mp hj)
  unfold leAt
  rw [h]
  exact wordBytes_decode word

theorem indirectBytes_length (words : List (BitVec 32)) :
    (indirectBytes words).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [indirectBytes, List.length_append, word32Bytes, List.length_cons, List.length_nil, ih]
    omega

theorem assemble_zero_byte (bytes : List Byte) (j : Nat) (zero : assembleBytes bytes = 0)
    (bound : j < bytes.length) : byteAt bytes j = 0 := by
  have h := assembleBytes_byte bytes j bound
  rw [zero] at h
  have value : bytes[j].toNat = 0 := by simpa using h.symm
  simp only [byteAt, List.getElem?_eq_getElem bound, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  exact value

theorem byteAt_append_left (left right : List Byte) (offset : Nat) (bound : offset < left.length) :
    byteAt (left ++ right) offset = byteAt left offset := by
  simp only [byteAt, List.getElem?_append_left bound]

theorem byteAt_append_right (left right : List Byte) (offset : Nat) :
    byteAt (left ++ right) (left.length + offset) = byteAt right offset := by
  simp [byteAt, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem leAt_append_left (left right : List Byte) (offset count : Nat)
    (bound : offset + count ≤ left.length) : leAt (left ++ right) offset count = leAt left offset count := by
  unfold leAt
  apply congrArg Int.ofNat
  apply congrArg assembleBytes
  apply List.map_congr_left
  intro j hj
  exact byteAt_append_left left right _ (by have := List.mem_range.mp hj; omega)

theorem leAt_append_right (left right : List Byte) (offset count : Nat) :
    leAt (left ++ right) (left.length + offset) count = leAt right offset count := by
  unfold leAt
  apply congrArg Int.ofNat
  apply congrArg assembleBytes
  apply List.map_congr_left
  intro j _
  rw [Nat.add_assoc, byteAt_append_right]

theorem word32Bytes_byte (word : BitVec 32) (j : Nat) (bound : j < 4) :
    byteAt (word32Bytes word) j = nthByte word j := by
  change byteAt (wordBytes (n := 4) word) j = _
  simp only [byteAt, wordBytes_byte (n := 4) word j bound, Option.getD_some]

theorem indirectBytes_byte (words : List (BitVec 32)) (i j : Nat)
    (index : i < words.length) (byte : j < 4) :
    byteAt (indirectBytes words) (4 * i + j) = nthByte words[i] j := by
  induction words generalizing i with
  | nil => simp at index
  | cons word rest ih =>
    cases i with
    | zero =>
      simp only [indirectBytes, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [byteAt_append_left (word32Bytes word) (indirectBytes rest) j byte,
        word32Bytes_byte word j byte]
    | succ i =>
      have hi : i < rest.length := by simpa using index
      change byteAt (word32Bytes word ++ indirectBytes rest) (4 * (i + 1) + j) = nthByte rest[i] j
      rw [show 4 * (i + 1) + j = (word32Bytes word).length + (4 * i + j) by
        change 4 * (i + 1) + j = 4 + (4 * i + j); omega,
        byteAt_append_right]
      exact ih i (by simpa using index)

end Xv6.Fs
