import Xv6.Fs.FileBytesProofs
import Xv6.Kernel.Proofs

namespace Xv6.Fs

def packedFsDisk (image : Xv6.Image.Packed) : Disk := fun address =>
  if 0 ≤ address then BitVec.ofNat 8 ((image.getByte? address.toNat).getD 0).toNat else 0

def packedFileBytes (image : Xv6.Image.Packed) : List (BitVec 8) :=
  image.toBytes.map (fun byte => BitVec.ofNat 8 byte.toNat)

def CopySlice (disk file : Xv6.Image.Packed) (diskOffset fileOffset count : Nat) : Prop :=
  ∀ j < count, disk.getByte? (diskOffset + j) = file.getByte? (fileOffset + j)

/-- Two arithmetic slices of independent pages certify every byte in the window. -/
theorem copySlice_of_pages disk file diskPage filePage diskWord fileWord diskOffset fileOffset count payload
    (disk_page : disk.pages[diskPage]? = some diskWord)
    (file_page : file.pages[filePage]? = some fileWord)
    (disk_window : diskOffset + count ≤ 4096) (file_window : fileOffset + count ≤ 4096)
    (disk_bound : diskPage * 4096 + diskOffset + count ≤ disk.byteLength)
    (file_bound : filePage * 4096 + fileOffset + count ≤ file.byteLength)
    (disk_slice : payload = (diskWord >>> (8 * diskOffset)) % 2 ^ (8 * count))
    (file_slice : payload = (fileWord >>> (8 * fileOffset)) % 2 ^ (8 * count)) :
    CopySlice disk file (diskPage * 4096 + diskOffset) (filePage * 4096 + fileOffset) count := by
  intro j hj
  have left := Xv6.Kernel.ByteRun.slice_read ⟨0, count, payload⟩ disk diskPage diskOffset diskWord
    disk_page disk_window disk_bound disk_slice j hj
  have right := Xv6.Kernel.ByteRun.slice_read ⟨0, count, payload⟩ file filePage fileOffset fileWord
    file_page file_window file_bound file_slice j hj
  exact left.trans right.symm

def FileBlockMatch (disk file : Xv6.Image.Packed) (dn : Dinode) (k : Nat) : Prop :=
  ∀ j < 1024, k * 1024 + j < file.byteLength →
    fileByte (dataOf (blocks (packedFsDisk disk)) dn) (k * 1024 + j) =
      BitVec.ofNat 8 (file.pageByte (k * 1024 + j)).toNat

theorem fileBlockMatch_of_copy disk file dn k block count
    (covered : file.Covered)
    (address : blockAddress (blocks (packedFsDisk disk)) dn k = block)
    (positive : 0 < block)
    (count_eq : count = min 1024 (file.byteLength - k * 1024))
    (copy : CopySlice disk file (block.toNat * 1024) (k * 1024) count) :
    FileBlockMatch disk file dn k := by
  intro j hj inside
  have enough : j < count := by omega
  have eq := copy j enough
  unfold fileByte
  have div : (k * 1024 + j) / 1024 = k := by omega
  have mod : (k * 1024 + j) % 1024 = j := by omega
  rw [div, mod, dataOf_address, address]
  have nz : (block == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [nz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [blocks_byte _ block j hj]
  unfold packedFsDisk
  rw [if_pos (by omega)]
  have cast : (block * 1024 + (j : Int)).toNat = block.toNat * 1024 + j := by omega
  rw [cast, eq, file.getByte?_eq_some_pageByte covered inside]
  rfl

inductive FileBlockCertificates (disk file : Xv6.Image.Packed) (dn : Dinode) : Nat → Nat → Prop where
  | nil (start : Nat) : FileBlockCertificates disk file dn start 0
  | cons {start count : Nat} (head : FileBlockMatch disk file dn start)
      (tail : FileBlockCertificates disk file dn (start + 1) count) :
      FileBlockCertificates disk file dn start (count + 1)

theorem FileBlockCertificates.lookup disk file dn start count
    (cert : FileBlockCertificates disk file dn start count) (k : Nat)
    (bound : start ≤ k ∧ k < start + count) : FileBlockMatch disk file dn k := by
  induction cert with
  | nil start => omega
  | @cons start count head tail ih =>
    by_cases first : k = start
    · subst k
      exact head
    · exact ih ⟨by omega, by omega⟩

theorem fileBytes_of_certificates disk file dn count
    (size : dn.size.toNat = file.byteLength) (capacity : file.byteLength ≤ count * 1024)
    (cert : FileBlockCertificates disk file dn 0 count) :
    fileBytes (dataOf (blocks (packedFsDisk disk)) dn) dn.size.toNat = packedFileBytes file := by
  unfold fileBytes packedFileBytes Xv6.Image.Packed.toBytes
  rw [size, List.map_map]
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have block := cert.lookup disk file dn 0 count (i / 1024) ⟨by omega, by omega⟩
  have result := block (i % 1024) (by omega) (by omega)
  have eq : i / 1024 * 1024 + i % 1024 = i := by omega
  simpa only [eq, Function.comp_def] using result

theorem nodeAt_of_file_content image sb i dn bytes (record : dinode image sb i = dn)
    (live : dn.typeZ ≠ 0) (non_directory : dn.typeZ ≠ 1)
    (content : fileBytes (dataOf image dn) dn.size.toNat = bytes) :
    nodeAt image sb i = some (.file bytes) := by
  unfold nodeAt
  rw [record]
  simp only [beq_eq_false_iff_ne.mpr live, Bool.false_eq_true, ↓reduceIte,
    nodeOf, non_directory, content]

end Xv6.Fs
