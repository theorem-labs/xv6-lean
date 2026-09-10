import Xv6.Elf.Image
import Xv6.Image.PackedProofs

/-!
Pointwise list-to-image correspondence for the constructors in `iris/ElfFile.v`
at fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. `mapAt` gives the lookup meaning of
`map_seqZ`: the byte at list index `i` occupies integer address `base + i`.
The image theorems retain the same parsed segment headers. They do not establish
an independent list-based ELF parser, original hex/dump equality, or machine boot.
-/
namespace Xv6.Elf

/-- Pointwise meaning of assigning consecutive integer addresses to a byte list. -/
def mapAt (base : Int) (bytes : List UInt8) : MemoryImage := fun address =>
  if 0 ≤ address - base then bytes[(address - base).toNat]? else none

/-- The source's `take filesz (drop offset file)` window at its load address. -/
def segmentFileList (bytes : List UInt8) (p : ProgramHeader) : MemoryImage :=
  mapAt p.vaddr ((bytes.drop p.offset.toNat).take p.filesz.toNat)

/-- The source's replicated zero bytes following the declared file-backed size. -/
def segmentZeroList (p : ProgramHeader) : MemoryImage :=
  mapAt (p.vaddr + p.filesz) (List.replicate (p.memsz - p.filesz).toNat 0)

def segmentList (bytes : List UInt8) (p : ProgramHeader) : MemoryImage :=
  union (segmentFileList bytes p) (segmentZeroList p)

/-- Ordered, left-biased segment union over explicit headers. -/
def fileImageList (bytes : List UInt8) (headers : List ProgramHeader) : MemoryImage :=
  segmentsUnion (segmentFileList bytes) headers

def zeroImageList (headers : List ProgramHeader) : MemoryImage :=
  segmentsUnion segmentZeroList headers

def loadedImageList (bytes : List UInt8) (headers : List ProgramHeader) : MemoryImage :=
  segmentsUnion (segmentList bytes) headers

/-- Exact lookup law for the finite consecutive-address list map. -/
theorem mapAt_some_iff (base address : Int) (bytes : List UInt8) (byte : UInt8) :
    mapAt base bytes address = some byte ↔
      0 ≤ address - base ∧ bytes[(address - base).toNat]? = some byte := by
  by_cases h : 0 ≤ address - base <;>
    simp only [mapAt, h, if_true, if_false, true_and, false_and, reduceCtorEq]

/-- The declared window truncates at EOF, with no well-formedness assumption. -/
theorem mapAt_window (base address : Int) (bytes : List UInt8) (offset count : Nat) :
    mapAt base ((bytes.drop offset).take count) address =
      if 0 ≤ address - base ∧
          address - base < ((min count (bytes.length - offset) : Nat) : Int) then
        bytes[offset + (address - base).toNat]?
      else none := by
  by_cases hn : 0 ≤ address - base
  · by_cases hb : address - base < ((min count (bytes.length - offset) : Nat) : Int)
    · have hi : (address - base).toNat < count := by
        have := Nat.min_le_left count (bytes.length - offset)
        omega
      have ht : 0 ≤ address - base ∧
          address - base < ((min count (bytes.length - offset) : Nat) : Int) := ⟨hn, hb⟩
      simp only [mapAt, if_pos hn, if_pos ht,
        List.getElem?_take_of_lt hi, List.getElem?_drop]
    · have hi : ((bytes.drop offset).take count).length ≤ (address - base).toNat := by
        simp only [List.length_take, List.length_drop]
        omega
      simp only [mapAt, if_pos hn, List.getElem?_eq_none hi]
      rw [if_neg (fun h => hb h.2)]
  · simp only [mapAt, hn, false_and, if_false]

/-- A replicated list gives precisely a constant-valued address interval. -/
theorem mapAt_replicate (base address : Int) (count : Nat) (byte : UInt8) :
    mapAt base (List.replicate count byte) address =
      if 0 ≤ address - base ∧ address - base < (count : Int) then some byte else none := by
  by_cases hn : 0 ≤ address - base
  · by_cases hb : address - base < (count : Int)
    · have hi : (address - base).toNat < count := by omega
      simp only [mapAt, hn, hb, List.getElem?_replicate, hi, and_self, if_true]
    · have hi : ¬ (address - base).toNat < count := by omega
      simp only [mapAt, hn, hb, List.getElem?_replicate, hi, and_false, if_true, if_false]
  · simp only [mapAt, hn, false_and, if_false]

theorem fileWindowLength_eq_list_length (f : Image.Packed) (p : ProgramHeader) :
    fileWindowLength f p = ((f.toBytes.drop p.offset.toNat).take p.filesz.toNat).length := by
  simp [fileWindowLength, Image.Packed.toBytes_length]

/-- All file-backed addresses agree, including malformed/truncated segments.
Coverage is needed only to connect partial packed reads to contiguous file bytes. -/
theorem segmentFile_eq_list (f : Image.Packed) (hc : f.Covered)
    (p : ProgramHeader) (address : Int) :
    segmentFile f p address = segmentFileList f.toBytes p address := by
  simp only [segmentFileList, mapAt_window, Image.Packed.toBytes_length,
    segmentFile, fileWindowLength]
  split
  · exact f.getByte?_eq_lookup hc _
  · rfl

/-- The zero-tail map needs no file coverage or segment well-formedness premise. -/
theorem segmentZero_eq_list (p : ProgramHeader) (address : Int) :
    segmentZero p address = segmentZeroList p address := by
  simp only [segmentZeroList, mapAt_replicate, segmentZero]

theorem segment_eq_list (f : Image.Packed) (hc : f.Covered)
    (p : ProgramHeader) (address : Int) :
    segment f p address = segmentList f.toBytes p address := by
  simp only [segment, segmentList, union, segmentFile_eq_list f hc, segmentZero_eq_list]

/-- Replacing each map by a pointwise equal map preserves union order and bias. -/
theorem segmentsUnion_congr (left right : ProgramHeader → MemoryImage)
    (headers : List ProgramHeader)
    (h : ∀ p ∈ headers, ∀ address, left p address = right p address)
    (address : Int) :
    segmentsUnion left headers address = segmentsUnion right headers address := by
  induction headers with
  | nil => rfl
  | cons p rest ih =>
    simp only [segmentsUnion, List.foldr_cons, union]
    rw [h p (by simp) address]
    rw [show List.foldr (fun p rest => union (left p) rest) (fun _ => none) rest address =
      List.foldr (fun p rest => union (right p) rest) (fun _ => none) rest address from
      ih (fun q hq => h q (by simp [hq]))]

/-- File-image correspondence using the same headers selected by `loads`. -/
theorem fileImage_eq_list (f : Image.Packed) (hc : f.Covered) (address : Int) :
    fileImage f address = fileImageList f.toBytes (loads f) address := by
  exact segmentsUnion_congr _ _ _ (fun p _ a => segmentFile_eq_list f hc p a) address

theorem zeroImage_eq_list (f : Image.Packed) (address : Int) :
    zeroImage f address = zeroImageList (loads f) address := by
  exact segmentsUnion_congr _ _ _ (fun p _ a => segmentZero_eq_list p a) address

/-- Loaded-image construction agrees with contiguous windows and replicated
zero tails, preserving left-biased ordering even for overlapping segments. -/
theorem loadedImage_eq_list (f : Image.Packed) (hc : f.Covered) (address : Int) :
    loadedImage f address = loadedImageList f.toBytes (loads f) address := by
  exact segmentsUnion_congr _ _ _ (fun p _ a => segment_eq_list f hc p a) address

end Xv6.Elf
