import Xv6.Fs.DurableBlocksProofs
import Xv6.Fs.BitmapImage
import Xv6.Fs.InodeW3Certificates

namespace Xv6.Fs.Image

/-- The entry-derived list is the same ordered list, not merely the same set. -/
theorem entry_blocks_eq_initial : entryBlocks blockView superblock = usedBlocks blockView superblock :=
  entryBlocks_eq_used blockView superblock superblock_ok inodes_valid_checked

theorem entry_set_checked : entrySet blockView superblock = some initialUsedBlocks := by
  rw [entrySet_eq_used blockView superblock superblock_ok inodes_valid_checked]
  exact used_set_checked

theorem entry_blocks_nodup_checked : (entryBlocks blockView superblock).Nodup :=
  entrySet_nodup blockView superblock initialUsedBlocks entry_set_checked

theorem live_inode_slots_injective (i : Int) (live : i ∈ liveSet blockView superblock) :
    SlotInjective blockView (dinode blockView superblock i) := by
  obtain ⟨bound, nz⟩ := (liveSet_mem blockView superblock i).mp live
  exact usedBlocks_slot_injective blockView superblock i superblock_ok inodes_valid_checked
    used_blocks_nodup_checked bound nz

theorem initial_inode_entries_disjoint (i j : Int)
    (li : i ∈ liveSet blockView superblock) (lj : j ∈ liveSet blockView superblock) (different : i ≠ j) :
    ∀ b, b ∈ inodeEntrySet blockView superblock i → b ∈ inodeEntrySet blockView superblock j → False := by
  obtain ⟨hi, ti⟩ := (liveSet_mem blockView superblock i).mp li
  obtain ⟨hj, tj⟩ := (liveSet_mem blockView superblock j).mp lj
  exact inodeEntrySet_disjoint blockView superblock i j entry_blocks_nodup_checked hi hj different ti tj

theorem entry_bitmap_checked : ∃ used, entrySet blockView superblock = some used ∧
    bitmapValid blockView superblock used = true :=
  ⟨initialUsedBlocks, entry_set_checked, bitmap_valid_checked⟩

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} entry-derived block theorem cones; standard foundational axioms only."
