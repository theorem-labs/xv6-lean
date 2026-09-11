import Xv6.Fs.DurableLinksProofs
import Xv6.Fs.LinksImage

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

theorem links_equal_checked : linksEqual blockView superblock = true := by
  apply linksEqual_of_tickets _ _ _ initial_tickets
  simp only [blockView, dinode_blocks, diskDinode, Dinode.typeZ, Dinode.nlinkZ]
  decide

theorem root_no_self_checked : rootNoSelf blockView superblock = true := by
  apply rootNoSelf_of_data_eq _ _ _ _ record01_eq root_directory_data
  decide

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.InodeW3.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
