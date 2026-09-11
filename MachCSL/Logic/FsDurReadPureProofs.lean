import MachCSL.Logic.FsDurReadSpec
import MachCSL.Logic.FsDurBytesProofs

namespace MachCSL.Logic.FsDurRead
open Iris Iris.Std Xv6.Fs DurableState
open FsDurBytes (flatten byteRun byteRun_lookup flatten_lookup dbytesOK_full)

theorem dblk_full_ok (disk : BlockMap) (full : BlocksFull disk) : FsDurBytes.DbytesOK disk :=
  dbytesOK_full disk full

theorem fs_dbytes_block_sub (disk : BlockMap) (block : Int) (bytes : List (BitVec 8))
    (full : BlocksFull disk) (found : disk[block]? = some bytes) :
    PartialMap.submap (M := Disk.ImageMap) (byteRun (block * 1024) bytes) (flatten disk) := by
  intro address byte get
  obtain ⟨k, kth, eq⟩ := (byteRun_lookup _ _ _ _).mp get
  exact (flatten_lookup disk address byte (dbytesOK_full disk full)).mpr ⟨block, bytes, k, found, kth, eq⟩

theorem block_of_byte (disk : BlockMap) (block offset : Int) (byte : MachCSL.Memory.Byte)
    (full : BlocksFull disk) (bound : 0 ≤ offset ∧ offset < 1024)
    (found : (flatten disk)[block * 1024 + offset]? = some byte) :
    ∃ stored, disk[block]? = some stored ∧ stored[offset.toNat]? = some byte := by
  obtain ⟨other, stored, k, get, kth, address⟩ :=
    (flatten_lookup disk _ byte (dbytesOK_full disk full)).mp found
  have len := full other stored get
  have hk := (List.getElem?_eq_some_iff.mp kth).1
  have same : other = block ∧ (k : Int) = offset := by omega
  obtain ⟨rfl, off⟩ := same
  refine ⟨stored, get, ?_⟩
  have cast : offset.toNat = k := by omega
  rwa [cast]

theorem run_read (disk : BlockMap) (block offset : Int) (bytes : List (BitVec 8))
    (full : BlocksFull disk) (nonneg : 0 ≤ offset) (fits : offset + (bytes.length : Int) ≤ 1024)
    (nonempty : 0 < bytes.length)
    (submap : PartialMap.submap (M := Disk.ImageMap) (byteRun (block * 1024 + offset) bytes) (flatten disk)) :
    RunSlice disk block offset bytes := by
  have first := List.getElem?_eq_getElem nonempty
  have firstRun : (byteRun (block * 1024 + offset) bytes)[block * 1024 + offset]? = some bytes[0] :=
    (byteRun_lookup _ _ _ _).mpr ⟨0, first, by omega⟩
  have inMap := submap _ _ firstRun
  obtain ⟨stored, found, _⟩ := block_of_byte disk block offset bytes[0] full (by omega) inMap
  have len := full block stored found
  let start := offset.toNat
  have start_eq : (start : Int) = offset := Int.toNat_of_nonneg nonneg
  have sliceBound : start + bytes.length ≤ stored.length := by omega
  have slice : (stored.drop start).take bytes.length = bytes := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]
      omega
    · intro i hi hi'
      have kth := List.getElem?_eq_getElem hi'
      have inRun : (byteRun (block * 1024 + offset) bytes)[block * 1024 + offset + (i : Int)]? = some bytes[i] :=
        (byteRun_lookup _ _ _ _).mpr ⟨i, kth, rfl⟩
      have read := submap _ _ inRun
      have address : block * 1024 + offset + (i : Int) = block * 1024 + (offset + (i : Int)) := by omega
      rw [address] at read
      obtain ⟨other, otherFound, atByte⟩ := block_of_byte disk block (offset + (i : Int)) bytes[i] full (by omega) read
      have same : other = stored := Option.some.inj (otherFound.symm.trans found)
      subst other
      have index_eq : (offset + (i : Int)).toNat = start + i := by omega
      rw [index_eq] at atByte
      have sliceGet : ((stored.drop start).take bytes.length)[i]? = some bytes[i] := by
        rw [List.getElem?_take_of_lt hi', List.getElem?_drop]
        exact atByte
      exact (List.getElem?_eq_some_iff.mp sliceGet).2
  refine ⟨stored, found, len, stored.take start, stored.drop (start + bytes.length), ?_, ?_⟩
  · have split := List.take_append_drop bytes.length (stored.drop start)
    rw [slice, List.drop_drop] at split
    calc
      stored = stored.take start ++ stored.drop start := (List.take_append_drop start stored).symm
      _ = stored.take start ++ (bytes ++ stored.drop (start + bytes.length)) := by rw [split]
      _ = stored.take start ++ bytes ++ stored.drop (start + bytes.length) := List.append_assoc .. |>.symm
  · simp only [List.length_take]
    have bound : start ≤ stored.length := by omega
    rw [Nat.min_eq_left bound]
    exact start_eq

theorem RunSlice.full_block (slice : RunSlice disk block 0 bytes) (length : bytes.length = 1024) :
    disk[block]? = some bytes := by
  obtain ⟨stored, found, len, pre, post, split, offset⟩ := slice
  have counts : pre.length + bytes.length + post.length = 1024 := by
    rw [split, List.length_append, List.length_append] at len
    exact len
  have preEmpty : pre = [] := List.length_eq_zero_iff.mp (by omega)
  have postEmpty : post = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [split, preEmpty, postEmpty, List.nil_append, List.append_nil] using found

/-- A nonempty owned run cannot manufacture a missing committed block. -/
theorem RunSlice.present (slice : RunSlice disk block offset bytes) : (disk[block]?).isSome := by
  obtain ⟨stored, found, _⟩ := slice
  simp [found]

theorem RunSlice.not_absent (absent : disk[block]? = none) : ¬RunSlice disk block offset bytes := by
  intro slice
  have present := slice.present
  simp [absent] at present

end MachCSL.Logic.FsDurRead
