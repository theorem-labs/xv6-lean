import Xv6.Fs.BootImageProofs
import Xv6.Fs.ValidityImage
import Xv6.Fs.InodeCertificates
import Xv6.Fs.DurableLinksImage

namespace Xv6.Fs.Image

def initialCoverage : BlockSet := blockCoverage 2000

theorem initial_coverage (b : Int) :
    b ∈ initialCoverage ↔ 1 ≤ b ∧ b < 2000 := blockCoverage_mem 2000 b

/-- Full source initial boot-image hypothesis, using the independently checked
image, rounded inode region, exact link counts, free records and root entries. -/
theorem boot_image_wf : BootImageWF disk 2048000 superblock 13 initialCoverage where
  image := fsimg_valid_checked
  region := region_valid_checked
  advertised := by decide
  wordBound := by decide
  positive := by decide
  rounded := by decide
  coverage := blockCoverage_covIn 2000
  metadata := by
    intro b hb
    apply (initial_coverage b).mpr
    change 1 ≤ b ∧ b < 46 + 1 at hb
    constructor <;> omega
  data := by
    intro b hb
    apply (initial_coverage b).mpr
    change 46 + 1 ≤ b ∧ b < 2000 at hb
    constructor <;> omega
  parsed := parse_superblock
  ushortBound := by decide
  diskBound := by decide
  links := links_equal_checked
  bare := region_bare_checked
  rootSelf := root_no_self_checked

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." ||
        name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem boot-image theorem cones; standard foundational axioms only."
