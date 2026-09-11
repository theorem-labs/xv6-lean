import Xv6.Fs.SnapshotConfigDecodeProofs
import Xv6.Fs.SnapshotCoverageProofs

namespace Xv6.Fs.SnapshotConfig
open DurableState SnapshotHome

theorem elem_of_snap_blk_set (n : DurableNode.Node) b : b ∈ blockSet n ↔ n.Owns b := by
  have data : b ∈ Std.ExtTreeSet.ofList (n.blocks.toList.map (fun entry => n.address entry.1)) ↔
      ∃ k, n.blocks[k]?.isSome ∧ n.address k = b := by
    simp only [Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨⟨k, bytes⟩, member, same⟩
      refine ⟨k, ?_, same⟩
      rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at member
      rw [member]; trivial
    · rintro ⟨k, present, same⟩
      obtain ⟨bytes, found⟩ := Option.isSome_iff_exists.mp present
      exact ⟨(k, bytes), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr found, same⟩
  unfold blockSet DurableNode.Node.Owns
  rw [Std.ExtTreeSet.mem_union_iff, data]
  by_cases zero : n.indirect = 0
  · simp [zero]
  · simp [zero]

theorem snap_blk_set_home state image home (i : Int) (n : DurableNode.Node) (bytes : Snapshot.Bytes state (restrict image home))
    (found : state.inodes[i]? = some n) : ∀ b, b ∈ blockSet n → b ∈ home := by
  intro b member
  exact SnapshotCoverage.snap_names_home state image home b bytes
    (Or.inr (Or.inl ⟨i, n, found, (elem_of_snap_blk_set n b).mp member⟩))

theorem snap_blk_set_disj state disk (i j : Int) (n m : DurableNode.Node) (bytes : Snapshot.Bytes state disk)
    (left : state.inodes[i]? = some n) (right : state.inodes[j]? = some m) (different : i ≠ j) :
    ∀ b, b ∈ blockSet n → b ∈ blockSet m → False := by
  intro b hn hm
  exact different (bytes.disjoint i n j m b left right
    ((elem_of_snap_blk_set n b).mp hn) ((elem_of_snap_blk_set m b).mp hm))

private theorem liveBlocks_list_mem state (inums : List Int) b :
    b ∈ inums.foldr (fun i all => blockSet (node state i) ∪ all) (∅ : BlockSet) ↔
      ∃ i, i ∈ inums ∧ b ∈ blockSet (node state i) := by
  induction inums with
  | nil => simp
  | cons i inums ih => simp [List.foldr_cons, ih, or_and_right, exists_or]

theorem elem_of_snap_live_blocks state inums b : b ∈ liveBlocks state inums ↔
    ∃ i, i ∈ inums ∧ b ∈ blockSet (node state i) := by
  simp only [liveBlocks, liveBlocks_list_mem, Std.ExtTreeSet.mem_toList]

theorem elem_of_free_set count used b : b ∈ freeSet count used ↔ (0 ≤ b ∧ b < count) ∧ b ∉ used := by
  simp only [freeSet, Std.ExtTreeSet.mem_diff_iff, Std.ExtTreeSet.mem_ofList,
    List.contains_iff_mem, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨k, bound, rfl⟩, absent⟩
    exact ⟨by change 0 ≤ (k : Int) ∧ (k : Int) < count; omega, absent⟩
  · rintro ⟨bounds, absent⟩
    exact ⟨⟨b.toNat, by omega, by change (b.toNat : Int) = b; omega⟩, absent⟩

theorem elem_of_snap_bitmap_spent state b : b ∈ bitmapSpent state ↔
    b = state.superblock.bmapstart ∨ ((0 ≤ b ∧ b < state.superblock.size) ∧ b ∉ state.used) := by
  simp only [bitmapSpent, Std.ExtTreeSet.mem_union_iff, Std.ExtTreeSet.mem_insert,
    Std.ExtTreeSet.not_mem_empty, or_false, Std.compare_eq_eq_iff_eq, elem_of_free_set]
  simp only [eq_comm]

theorem snap_meta_ireg state disk (nib : Nat) b (bytes : Snapshot.Bytes state disk)
    (width : (nib : Int) = state.superblock.ninodes / 16 + 1)
    (member : b ∈ regionBlocks state.superblock.inodestart nib) : Metadata state b := by
  have range := (region_blocks_spec _ nib b).mp member
  refine Or.inr (Or.inr ⟨(b - state.superblock.inodestart) * 16, ?_, ?_⟩)
  · exact bytes.regionDomain _ (by omega)
  · omega

theorem elem_of_snap_live_set state nib i : i ∈ liveSet state nib ↔
    i ∈ regionInums nib ∧ (node state i).typeZ ≠ 0 := by
  simp [liveSet]

theorem elem_of_snap_spent state nib b : b ∈ spent state nib ↔
    b = 1 ∨ b ∈ logRegion state.superblock.logstart ∨
    b ∈ regionBlocks state.superblock.inodestart nib ∨ b ∈ bitmapSpent state ∨
    b ∈ liveBlocks state (liveSet state nib) := by
  simp only [spent, Std.ExtTreeSet.mem_union_iff, Std.ExtTreeSet.mem_insert,
    Std.ExtTreeSet.not_mem_empty, or_false, Std.compare_eq_eq_iff_eq, or_assoc]
  simp only [eq_comm]

/-- No validity premise or slot upper bound is part of the raw footprint. -/
theorem blockSet_stored_slot (n : DurableNode.Node) k bytes (found : n.blocks[k]? = some bytes) :
    n.address k ∈ blockSet n := by
  apply (elem_of_snap_blk_set n _).mpr
  refine Or.inl ⟨k, ?_, rfl⟩
  rw [found]; trivial

theorem freeSet_nonpositive count used (bound : count ≤ 0) : freeSet count used = ∅ := by
  apply Std.ExtTreeSet.ext_mem
  intro b
  simp only [elem_of_free_set, Std.ExtTreeSet.not_mem_empty, iff_false]
  omega

end Xv6.Fs.SnapshotConfig
