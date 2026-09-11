import Xv6.Fs.InodeImage
import Xv6.Generated.InodeW3Leaf01
import Xv6.Generated.InodeW3Leaf02
import Xv6.Generated.InodeW3Leaf03
import Xv6.Generated.InodeW3Leaf04
import Xv6.Generated.InodeW3Leaf05
import Xv6.Generated.InodeW3Leaf06
import Xv6.Generated.InodeW3Leaf07
import Xv6.Generated.InodeW3Leaf08
import Xv6.Generated.InodeW3Leaf09
import Xv6.Generated.InodeW3Leaf10
import Xv6.Generated.InodeW3Leaf11
import Xv6.Generated.InodeW3Leaf12
import Xv6.Generated.InodeW3Leaf13
import Xv6.Generated.InodeW3Leaf14
import Xv6.Generated.InodeW3Leaf15
import Xv6.Generated.InodeW3Leaf16
import Xv6.Generated.InodeW3Leaf17
import Xv6.Generated.InodeW3Leaf18
import Xv6.Generated.InodeW3Leaf19
import Xv6.Generated.InodeW3Leaf20
import Xv6.Generated.InodeW3Leaf21
import Xv6.Generated.InodeW3Leaf22
import Lean.Util.CollectAxioms

/-! Complete W3 certificate for the actual initial filesystem image. Every live
record and indirect block has an independently checked source-reader equality.
Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

/-- Exact advertised 200-inode Boolean check, including the source's free-inode skip. -/
theorem inodes_valid_checked : inodesValid blockView superblock = true := by
  apply inodesValid_of_live
  intro z live
  rw [live_inode_list] at live
  obtain ⟨i, hi, he⟩ := List.mem_map.mp live
  have bound := List.mem_range.mp hi
  have cases : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 ∨ z = 10 ∨ z = 11 ∨ z = 12 ∨ z = 13 ∨ z = 14 ∨ z = 15 ∨ z = 16 ∨ z = 17 ∨ z = 18 ∨ z = 19 ∨ z = 20 ∨ z = 21 ∨ z = 22 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inode01_valid
  · exact inode02_valid
  · exact inode03_valid
  · exact inode04_valid
  · exact inode05_valid
  · exact inode06_valid
  · exact inode07_valid
  · exact inode08_valid
  · exact inode09_valid
  · exact inode10_valid
  · exact inode11_valid
  · exact inode12_valid
  · exact inode13_valid
  · exact inode14_valid
  · exact inode15_valid
  · exact inode16_valid
  · exact inode17_valid
  · exact inode18_valid
  · exact inode19_valid
  · exact inode20_valid
  · exact inode21_valid
  · exact inode22_valid

/-- All nine source W3 obligations for every actual live initial inode. -/
theorem live_inode_ok (z : Int) (live : z ∈ liveSet blockView superblock) :
    InodeOK blockView superblock (dinode blockView superblock z) := by
  obtain ⟨bound, nonzero⟩ := (liveSet_mem blockView superblock z).mp live
  exact inodesValid_spec blockView superblock z inodes_valid_checked bound nonzero

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if info.isTheorem && (text.startsWith "Xv6.Fs." ||
        text.startsWith "_private.Xv6.Fs." || text.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem/W3 theorem cones; standard foundational axioms only."
