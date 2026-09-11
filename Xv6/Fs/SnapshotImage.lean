import Xv6.Fs.SnapshotImageProofs
import Xv6.Fs.BootImageImage

/-! The full durable snapshot predicate at the actual checked initial image.
The generic assembly remains separate from all literal-image imports. -/
namespace Xv6.Fs.Image
open DurableImageNode SnapshotHome

-- Avoid unfolding the literal finite maps while matching the generic theorem.
-- These local elaboration hints add no premise or logical dependency.
attribute [local irreducible] DurableImageNode.imageState SnapshotHome.homeMap

theorem snapshot_ok :
    Snapshot.OK (imageState blockView superblock 13)
      (homeMap blockView initialCoverage superblock.logstart) :=
  SnapshotImage.image_snap_ok (disk := disk) (ndisk := 2048000)
    (sb := superblock) (nib := 13) (cov := initialCoverage) boot_image_wf

theorem snapshot_holds :
    Snapshot.Holds (homeMap blockView initialCoverage superblock.logstart) :=
  SnapshotImage.image_snap_holds (disk := disk) (ndisk := 2048000)
    (sb := superblock) (nib := 13) (cov := initialCoverage) boot_image_wf

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  for name in #[``Xv6.Fs.Image.snapshot_ok, ``Xv6.Fs.Image.snapshot_holds] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in initial image snapshot {name}"
  logInfo "Initial image full snapshot validity: standard foundational axioms only."
