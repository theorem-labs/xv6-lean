import Xv6.Elf.Proofs

/-! Pointwise partial-map representation of `seg_file_map`, `seg_zero_map`,
`seg_map`, `segs_union`, and `elf_image` from the pinned `iris/ElfFile.v`.
List/map representation correspondence is a separate obligation. -/
namespace Xv6.Elf

abbrev MemoryImage := Int → Option UInt8

/-- The reference `take filesz (drop offset bytes)` truncates at the file end. -/
def fileWindowLength (f : Image.Packed) (p : ProgramHeader) : Nat :=
  min p.filesz.toNat (f.byteLength - p.offset.toNat)

def segmentFile (f : Image.Packed) (p : ProgramHeader) : MemoryImage := fun address =>
  let delta := address - p.vaddr
  if 0 ≤ delta ∧ delta < (fileWindowLength f p : Int) then
    f.getByte? (p.offset.toNat + delta.toNat)
  else none

def segmentZero (p : ProgramHeader) : MemoryImage := fun address =>
  let delta := address - (p.vaddr + p.filesz)
  if 0 ≤ delta ∧ delta < ((p.memsz - p.filesz).toNat : Int) then some 0 else none

/-- Left-biased union, matching stdpp's map union in the reference. -/
def union (left right : MemoryImage) : MemoryImage := fun address =>
  (left address).orElse fun _ => right address

def segment (f : Image.Packed) (p : ProgramHeader) : MemoryImage :=
  union (segmentFile f p) (segmentZero p)

def segmentsUnion (get : ProgramHeader → MemoryImage) (ps : List ProgramHeader) : MemoryImage :=
  ps.foldr (fun p rest => union (get p) rest) (fun _ => none)

def fileImage (f : Image.Packed) : MemoryImage := segmentsUnion (segmentFile f) (loads f)
def zeroImage (f : Image.Packed) : MemoryImage := segmentsUnion segmentZero (loads f)
def loadedImage (f : Image.Packed) : MemoryImage := segmentsUnion (segment f) (loads f)

theorem union_left (left right : MemoryImage) (address : Int) (byte : UInt8)
    (h : left address = some byte) : union left right address = some byte := by
  simp [union, h]

theorem segmentFile_outside (f : Image.Packed) (p : ProgramHeader) (address : Int)
    (h : address < p.vaddr ∨ p.vaddr + (fileWindowLength f p : Int) ≤ address) :
    segmentFile f p address = none := by
  have : ¬ (0 ≤ address - p.vaddr ∧ address - p.vaddr < (fileWindowLength f p : Int)) := by
    omega
  simp only [segmentFile, if_neg this]

theorem segmentZero_inside (p : ProgramHeader) (address : Int)
    (h : p.vaddr + p.filesz ≤ address ∧ address < p.vaddr + p.memsz) :
    segmentZero p address = some 0 := by
  have hd : 0 ≤ address - (p.vaddr + p.filesz) ∧
      address - (p.vaddr + p.filesz) < ((p.memsz - p.filesz).toNat : Int) := ⟨by omega, by omega⟩
  simp only [segmentZero, if_pos hd]

/-- The zero tail is filled after the complete declared file-backed region. -/
theorem segment_bss (f : Image.Packed) (p : ProgramHeader) (address : Int)
    (hfilesz : 0 ≤ p.filesz)
    (h : p.vaddr + p.filesz ≤ address ∧ address < p.vaddr + p.memsz) :
    segment f p address = some 0 := by
  have hw : (fileWindowLength f p : Int) ≤ p.filesz := by
    have hm := Nat.min_le_left p.filesz.toNat (f.byteLength - p.offset.toNat)
    dsimp [fileWindowLength]
    omega
  have hf := segmentFile_outside f p address (Or.inr (by omega))
  simp [segment, union, hf, segmentZero_inside p address h]

end Xv6.Elf
