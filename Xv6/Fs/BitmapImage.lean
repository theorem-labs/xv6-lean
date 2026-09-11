import Xv6.Fs.BitmapCertificateProofs
import Xv6.Fs.InodeW3Certificates
import Xv6.Fs.BitmapData
import Init.Data.List.Perm
import Init.Data.List.Nat.Range

/-! Actual W4/W5 certificates reuse all checked W3 reader inputs.
Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

def usedBlockInputs : List Int :=
    inodeBlocksInput record01 entries01 ++
    inodeBlocksInput record02 entries02 ++
    inodeBlocksInput record03 entries03 ++
    inodeBlocksInput record04 entries04 ++
    inodeBlocksInput record05 entries05 ++
    inodeBlocksInput record06 entries06 ++
    inodeBlocksInput record07 entries07 ++
    inodeBlocksInput record08 entries08 ++
    inodeBlocksInput record09 entries09 ++
    inodeBlocksInput record10 entries10 ++
    inodeBlocksInput record11 entries11 ++
    inodeBlocksInput record12 entries12 ++
    inodeBlocksInput record13 entries13 ++
    inodeBlocksInput record14 entries14 ++
    inodeBlocksInput record15 entries15 ++
    inodeBlocksInput record16 entries16 ++
    inodeBlocksInput record17 entries17 ++
    inodeBlocksInput record18 entries18 ++
    inodeBlocksInput record19 entries19 ++
    inodeBlocksInput record20 entries20 ++
    inodeBlocksInput record21 entries21 ++
    inodeBlocksInput record22 entries22

theorem used_blocks_input_eq : usedBlocks blockView superblock = usedBlockInputs := by
  have live : liveInodes blockView superblock = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] := by
    rw [live_inode_list]
    decide
  rw [usedBlocks_eq_live, live]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [record01_eq, record02_eq, record03_eq, record04_eq, record05_eq, record06_eq, record07_eq, record08_eq, record09_eq, record10_eq, record11_eq, record12_eq, record13_eq, record14_eq, record15_eq, record16_eq, record17_eq, record18_eq, record19_eq, record20_eq, record21_eq, record22_eq]
  simp only [inodeBlocks_eq_inputs, entries01_eq, entries02_eq, entries03_eq, entries04_eq, entries05_eq, entries06_eq, entries07_eq, entries08_eq, entries09_eq, entries10_eq, entries11_eq, entries12_eq, entries13_eq, entries14_eq, entries15_eq, entries16_eq, entries17_eq, entries18_eq, entries19_eq, entries20_eq, entries21_eq, entries22_eq]
  rfl

theorem used_inputs_literal : usedBlockInputs = Xv6.Generated.Bitmap.orderedBlocks := by decide

private theorem ordered_blocks_perm :
    Xv6.Generated.Bitmap.orderedBlocks.Perm
      ((List.range 936).map (fun (i : Nat) => (i : Int) + 47)) := by decide

theorem used_inputs_collected : (collectNodup Xv6.Generated.Bitmap.orderedBlocks).isSome = true := by
  apply Option.isSome_iff_exists.mpr
  apply (collectNodup_exists _).mpr
  apply ordered_blocks_perm.nodup_iff.mpr
  change List.Pairwise (· ≠ ·) ((List.range 936).map (fun (i : Nat) => (i : Int) + 47))
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun ne eq => ne (by omega)) List.nodup_range

def initialUsedBlocks : BlockSet := (collectNodup Xv6.Generated.Bitmap.orderedBlocks).getD ∅

theorem used_set_checked : usedSet blockView superblock = some initialUsedBlocks :=
  (congrArg collectNodup (used_blocks_input_eq.trans used_inputs_literal)).trans
    (collectNodup_getD _ used_inputs_collected)

theorem used_blocks_nodup_checked : (usedBlocks blockView superblock).Nodup :=
  usedSet_nodup blockView superblock initialUsedBlocks used_set_checked

theorem initial_used_mem (b : Int) : b ∈ initialUsedBlocks ↔ 47 ≤ b ∧ b < 983 := by
  apply (collectNodup_mem _ _ (collectNodup_getD _ used_inputs_collected) b).trans
  rw [ordered_blocks_perm.mem_iff]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro bound
    exact ⟨(b - 47).toNat, by omega, by omega⟩

theorem bitmap_valid_checked : bitmapValid blockView superblock initialUsedBlocks = true := by
  apply (bitmapValid_iff blockView superblock initialUsedBlocks).mpr
  intro b bound
  have bound' : 0 ≤ b ∧ b < 2000 := bound
  rw [initial_bitmap_bit b bound', decide_eq_true_eq, initial_used_mem]
  change b < 983 ↔ b < 47 ∨ 47 ≤ b ∧ b < 983
  omega

theorem blocks_bitmap_valid_checked : blocksBitmapValid blockView superblock = true :=
  blocksBitmapValid_of_collected blockView superblock initialUsedBlocks
    used_set_checked bitmap_valid_checked

theorem blocks_bitmap_ok : BlocksBitmapOK blockView superblock :=
  (blocksBitmapValid_iff blockView superblock).mp blocks_bitmap_valid_checked

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." ||
        name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem/bitmap certificate theorem cones; standard foundational axioms only."
