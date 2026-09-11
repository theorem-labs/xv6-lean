import Xv6.Fs.LinkImageProofs
import Xv6.Fs.BootImageImage

/-! Concrete initial-image projection. Generic link proofs remain literal-free. -/
namespace Xv6.Fs.Image
open DurableImageNode LinkFamily MachCSL.Logic.FsLink Iris Iris.CMRA

-- Reuse the proved generic application without unfolding the full literal map
-- during elaboration. These local transparency hints add no logical premise.
attribute [local irreducible] LinkFamily.elem DurableImageNode.imageNodes LinkFamily.imageChoice

theorem link_family_valid :
    ✓ (elem (imageNodes blockView superblock 13) (imageChoice blockView superblock) •
      tokElem 1 (imageValue blockView superblock 1)) :=
  LinkImage.bootImage_link_valid (disk := disk) (ndisk := 2048000)
    (sb := superblock) (nib := 13) (cov := initialCoverage) boot_image_wf

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  for axiomName in ← collectAxioms ``Xv6.Fs.Image.link_family_valid do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom {axiomName} in initial image link-family validity"
  logInfo "Initial image link-family validity: standard foundational axioms only."
