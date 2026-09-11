import MachCSL.Logic.FsInodeRegionCodecDefs
import Xv6.Fs.SnapshotCodecProofs
import Xv6.Fs.InodeRegionImageProofs

namespace MachCSL.Logic.FsInodeRegion
open Xv6.Fs MachCSL.Memory

theorem decode_records_length n bytes : (decodeRecords n bytes).length = n := by
  induction n generalizing bytes with
  | zero => rfl
  | succ n ih => simp [decodeRecords, ih]

theorem decode_records_wf n bytes : ∀ record ∈ decodeRecords n bytes, record.WellFormed := by
  induction n generalizing bytes with
  | zero => simp [decodeRecords]
  | succ n ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact decodeDinode_wf bytes
    · exact ih (bytes.drop 64) record member

theorem decode_records_roundtrip n bytes (full : bytes.length = 64 * n) :
    inodeBlockBytes (decodeRecords n bytes) = bytes := by
  induction n generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst bytes
    rfl
  | succ n ih =>
    change dinodeBytes (decodeDinode bytes) ++ inodeBlockBytes (decodeRecords n (bytes.drop 64)) = bytes
    rw [encode_decodeDinode_prefix bytes (by omega), ih (bytes.drop 64) (by simp; omega)]
    exact List.take_append_drop 64 bytes

theorem image_decode (blocks : List (List Byte)) (full : ∀ block ∈ blocks, block.length = 1024) :
    (decodeImage blocks).length = blocks.length ∧
    (∀ records ∈ decodeImage blocks, InodeBlockWellFormed records) ∧
    ∀ bi : Nat, bi < blocks.length →
      blocks[bi]?.getD [] = inodeBlockBytes ((decodeImage blocks)[bi]?.getD []) := by
  refine ⟨by simp [decodeImage], ?_, ?_⟩
  · intro records member
    obtain ⟨block, member, rfl⟩ := List.mem_map.mp member
    exact ⟨decode_records_length 16 block, decode_records_wf 16 block⟩
  · intro bi bound
    have member := List.getElem_mem bound
    simp only [List.getElem?_eq_getElem bound, Option.getD_some]
    rw [show (decodeImage blocks)[bi]?.getD [] = decodeRecords 16 blocks[bi] by
      simp [decodeImage, List.getElem?_eq_getElem bound]]
    exact (decode_records_roundtrip 16 blocks[bi] (by simpa using full _ member)).symm

end MachCSL.Logic.FsInodeRegion
