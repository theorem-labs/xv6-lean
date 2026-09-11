import Xv6.Fs.ValidityProofs
import Xv6.Fs.InodeW3Certificates
import Xv6.Fs.BitmapImage
import Xv6.Fs.LinksImage

/-! Full initial fsimg_wf, composed from checked readers and exact W1–W9 clauses.
This is the initial filesystem predicate, not machine adequacy or crash consistency. -/
namespace Xv6.Fs.Image

theorem fsimg_valid_checked : fsimgValid blockView superblock = true :=
  (fsimgValid_iff blockView superblock).mpr
    ⟨superblock_valid, log_clean, inodes_valid_checked, blocks_bitmap_valid_checked,
      dirs_valid_checked, root_valid_checked, dots_all_checked, links_valid_checked⟩

theorem fsimg_checks : FsimgChecks blockView superblock :=
  (fsimgValid_iff blockView superblock).mp fsimg_valid_checked

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
  logInfo m!"Audited {count} full initial filesystem theorem cones; standard foundational axioms only."
