import MachCSL.Logic.FsDurAllocSpec
import MachCSL.Logic.FsDurBytesProofs
import Xv6.Fs.SnapshotProofs

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Xv6.Fs DurableState DurableNode FsDurBytes

theorem nodeAt_found (state : State) (i : Int) (n : Node) (found : state.inodes[i]? = some n) :
    nodeAt state i = n := by simp only [nodeAt, found, Option.getD_some]

theorem fpRun_empty b off : fpRun b off [] = ∅ := rfl

theorem fpRun_slice (disk : DurableState.BlockMap) (b off : Int) (bytes pre part post : List (BitVec 8))
    (full : BlocksFull disk) (found : disk[b]? = some bytes)
    (split : bytes = pre ++ part ++ post) (offset : (pre.length : Int) = off) :
    PartialMap.submap (M := Disk.ImageMap) (fpRun b off part) (flatten disk) ∧
      0 ≤ off ∧ off + (part.length : Int) ≤ 1024 := by
  have size := full b bytes found
  have sizes : pre.length + part.length + post.length = 1024 := by
    rw [split, List.length_append, List.length_append] at size
    exact size
  refine ⟨?_, by omega, by omega⟩
  intro a v read
  obtain ⟨k, get, addr⟩ := (byteRun_lookup _ _ _ _).mp read
  have kth := List.getElem?_eq_some_iff.mp get
  have joined : bytes[pre.length + k]? = some v := by
    rw [split, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left kth.1]
    exact get
  apply (flatten_lookup disk a v (dbytesOK_full disk full)).mpr
  exact ⟨b, bytes, pre.length + k, found, joined, by omega⟩

theorem fpRun_block (disk : DurableState.BlockMap) (b : Int) (bytes : List (BitVec 8))
    (full : BlocksFull disk) (found : disk[b]? = some bytes) :
    PartialMap.submap (M := Disk.ImageMap) (fpRun b 0 bytes) (flatten disk) ∧
      0 ≤ (0 : Int) ∧ (0 : Int) + bytes.length ≤ 1024 :=
  fpRun_slice disk b 0 bytes [] bytes [] full found (by simp) rfl

theorem fpRun_empty_slice disk b :
    PartialMap.submap (M := Disk.ImageMap) (fpRun b 0 []) (flatten disk) ∧
      0 ≤ (0 : Int) ∧ (0 : Int) + ([] : List (BitVec 8)).length ≤ 1024 := by
  refine ⟨?_, by decide, by decide⟩
  intro a v found
  change none = some v at found
  cases found

theorem fp_ok (state : State) (disk : DurableState.BlockMap) (slot : Slot)
    (bytes : Snapshot.Bytes state disk) (valid : Valid state slot) :
    PartialMap.submap (M := Disk.ImageMap) (fpMap state disk slot) (flatten disk) ∧
      0 ≤ fpOffset slot ∧ fpOffset slot + (fpBytes state disk slot).length ≤ (1024 : Int) := by
  have full : BlocksFull disk := bytes.blockSize
  cases slot with
  | sb => exact fpRun_block disk 1 state.superblockBytes full bytes.superblock
  | bmap => exact fpRun_block disk _ _ full bytes.bitmap
  | record i =>
    obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp valid
    obtain ⟨block, stored, pre, post, split, offset⟩ := bytes.record i n found
    simpa only [fpMap, fpBytes, fpBlock, fpOffset, nodeAt_found state i n found] using
      fpRun_slice disk _ _ block pre (dinodeBytes n.record) post full stored split offset
  | data i k =>
    obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp valid.1
    have get := valid.2
    rw [nodeAt_found state i n found] at get
    obtain ⟨block, stored⟩ := Option.isSome_iff_exists.mp get
    simpa only [fpMap, fpBytes, fpBlock, fpOffset, nodeAt_found state i n found, stored,
      Option.getD_some] using fpRun_block disk _ block full (bytes.data i n k block found stored)
  | indirect i =>
    obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp valid
    simp only [fpMap, fpBytes, fpBlock, fpOffset, nodeAt_found state i n found]
    by_cases zero : n.indirect = 0
    · simp only [if_pos zero]
      exact fpRun_empty_slice disk _
    · simp only [if_neg zero]
      exact fpRun_block disk _ _ full (bytes.indirect i n found zero)
  | pool b =>
    simp only [fpMap, fpBytes, fpBlock, fpOffset]
    by_cases used : b ∈ state.used
    · simp only [if_pos used]
      exact fpRun_empty_slice disk _
    · obtain ⟨block, stored⟩ := Option.isSome_iff_exists.mp (bytes.pool b valid used)
      simp only [if_neg used, stored, Option.getD_some]
      exact fpRun_block disk b block full stored

theorem fpRun_disjoint (b off : Int) (left : List (BitVec 8)) (c off' : Int) (right : List (BitVec 8))
    (nonneg : 0 ≤ off) (bound : off + (left.length : Int) ≤ 1024)
    (nonneg' : 0 ≤ off') (bound' : off' + (right.length : Int) ≤ 1024)
    (separated : b ≠ c ∨ off + (left.length : Int) ≤ off' ∨ off' + (right.length : Int) ≤ off) :
    PartialMap.disjoint (M := Disk.ImageMap) (fpRun b off left) (fpRun c off' right) := by
  apply (PartialMap.disjoint_iff _ _).mpr
  intro a
  cases get : (fpRun b off left)[a]? with
  | none => exact Or.inl get
  | some v =>
    right
    cases get' : (fpRun c off' right)[a]? with
    | none => exact get'
    | some w =>
      obtain ⟨k, kth, addr⟩ := (byteRun_lookup _ _ _ _).mp get
      obtain ⟨j, jth, addr'⟩ := (byteRun_lookup _ _ _ _).mp get'
      have hk := (List.getElem?_eq_some_iff.mp kth).1
      have hj := (List.getElem?_eq_some_iff.mp jth).1
      rcases separated with ne | before | after <;> omega

/-- The source inhabitant is deliberately not a well-shaped disk inode. -/
theorem sourceDefault_record_width : (dinodeBytes sourceDefault.record).length = 12 := by decide

theorem absent_data_is_empty (state : State) disk i k (absent : state.inodes[i]? = none) :
    fpBytes state disk (.data i k) = [] := by
  simp only [fpBytes, nodeAt, absent, Option.getD_none, sourceDefault]
  rfl

end MachCSL.Logic.FsDurAlloc
