import Xv6.Fs.LinksCertificateProofs
import Xv6.Fs.DirectoryImage

/-! W9 uses all ordered actual directory tickets, without deduplication. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

theorem initial_tickets : allTickets blockView superblock =
    (List.range 21).map (fun i : Nat => (i + 2 : Int)) := by
  rw [allTickets_eq_directories, directory_inode_list]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [record01_eq, dirTickets_of_data_eq _ _ _ _ root_directory_data]
  decide

theorem links_valid_checked : linksValid blockView superblock = true := by
  apply linksValid_of_tickets _ _ _ initial_tickets
  simp only [blockView, dinode_blocks, diskDinode, Dinode.typeZ, Dinode.nlinkZ]
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
