import Xv6.Fs.SnapshotConfigDefs
import Xv6.Fs.SnapshotImageBytesProofs
import Xv6.Fs.SnapshotHomeProofs
import Xv6.Fs.DinodeProofs

namespace Xv6.Fs.SnapshotConfig
open DurableState SnapshotHome

theorem rec_in_blk_inj bytes offset (left right : Dinode) (hl : left.WellFormed) (hr : right.WellFormed)
    (placedLeft : RecordInBlock bytes offset left) (placedRight : RecordInBlock bytes offset right) : left = right := by
  obtain ⟨pre, post, hleft, lenLeft⟩ := placedLeft
  obtain ⟨pre', post', hright, lenRight⟩ := placedRight
  have len : pre.length = pre'.length := by omega
  have same := hleft.symm.trans hright
  rw [List.append_assoc, List.append_assoc] at same
  have rest := List.append_inj_right same len
  have encoded := List.append_inj_left rest (by rw [dinodeBytes_length left hl, dinodeBytes_length right hr])
  exact dinodeBytes_injective left right hl hr encoded

theorem snap_rec_decode state image home i n (full : BlocksFull image)
    (bytes : Snapshot.Bytes state (restrict image home)) (found : state.inodes[i]? = some n) :
    dinode image state.superblock i = n.record := by
  obtain ⟨record, present, placed⟩ := bytes.record i n found
  obtain ⟨_, rfl⟩ := (restrict_lookup_some image home _ record).mp present
  exact rec_in_blk_inj _ _ _ _ (dinode_wf image state.superblock i) (bytes.repr i n found).record
    (image_record_in_block image state.superblock i full (bytes.inum i n found)) placed

theorem region_inums_spec nib i : i ∈ regionInums nib ↔ 0 ≤ i ∧ i < 16 * (nib : Int) := by
  simp only [regionInums, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, bound, rfl⟩
    change 0 ≤ (k : Int) ∧ (k : Int) < 16 * (nib : Int)
    omega
  · intro bounds
    exact ⟨i.toNat, by omega, by change (i.toNat : Int) = i; omega⟩

theorem region_blocks_spec start nib b : b ∈ regionBlocks start nib ↔ start ≤ b ∧ b < start + (nib : Int) := by
  simp only [regionBlocks, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, bound, rfl⟩
    omega
  · intro bounds
    exact ⟨(b - start).toNat, by omega, by omega⟩

theorem node_at state i n (found : state.inodes[i]? = some n) : node state i = n := by
  simp [node, found]

theorem node_absent state i (absent : state.inodes[i]? = none) : node state i = defaultNode := by
  simp [node, absent]

theorem default_not_zero : defaultNode ≠ DurableNode.zero := by
  intro same
  have lengths := congrArg (fun n : DurableNode.Node => n.entries.length) same
  change ([] : List (BitVec 32)).length = (List.replicate 256 (0 : BitVec 32)).length at lengths
  rw [List.length_nil, List.length_replicate] at lengths
  omega

theorem snap_node_at state disk (nib : Nat) i (bytes : Snapshot.Bytes state disk)
    (width : (nib : Int) = state.superblock.ninodes / 16 + 1) (member : i ∈ regionInums nib) :
    state.inodes[i]? = some (node state i) := by
  have bounds := (region_inums_spec nib i).mp member
  obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp (bytes.regionDomain i (by omega))
  rw [node_at state i n found]
  exact found

theorem snap_rec_decode_region state image home (nib : Nat) i (full : BlocksFull image)
    (bytes : Snapshot.Bytes state (restrict image home))
    (width : (nib : Int) = state.superblock.ninodes / 16 + 1) (member : i ∈ regionInums nib) :
    dinode image state.superblock i = (node state i).record :=
  snap_rec_decode state image home i (node state i) full bytes (snap_node_at state _ nib i bytes width member)

end Xv6.Fs.SnapshotConfig
