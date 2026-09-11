import Xv6.Fs.InodeValidityProofs
import Xv6.Fs.Image

/-! Concrete initial-image leaf. Pure inode validity modules do not import it.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Xv6.Fs.Image

/-- Actual initial image enumeration: inode zero and every inode after22 are free. -/
theorem live_inode_list : liveInodes blockView superblock =
    (List.range 22).map (fun i : Nat => (i + 1 : Int)) := by
  simp only [liveInodes, Dinode.typeZ, blockView, dinode_type_blocks]
  decide

/-- The rounded13-block inode region has208 records; all8 tail records are free. -/
theorem region_free_checked : regionFree blockView superblock 13 = true := by
  simp only [regionFree, Dinode.typeZ, blockView, dinode_type_blocks]
  decide

theorem live_set_membership (z : Int) : z ∈ liveSet blockView superblock ↔
    1 ≤ z ∧ z ≤ 22 := by
  simp only [liveSet, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem,
    live_inode_list, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    omega
  · intro bound
    refine ⟨(z - 1).toNat, by omega, ?_⟩
    change ((z - 1).toNat : Int) + 1 = z
    omega

theorem tail_type_zero (z : Int) (tail : 200 ≤ z ∧ z < 208) :
    (dinode blockView superblock z).typeZ = 0 :=
  regionFree_spec blockView superblock 13 z region_free_checked (by omega)
    (by simpa only [superblock] using tail.1) (by omega)

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  for name in #[``Xv6.Fs.Image.live_inode_list, ``Xv6.Fs.Image.region_free_checked,
      ``Xv6.Fs.Image.live_set_membership, ``Xv6.Fs.Image.tail_type_zero] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
