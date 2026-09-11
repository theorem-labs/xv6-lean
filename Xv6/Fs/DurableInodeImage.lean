import Xv6.Fs.DurableInodeProofs
import Xv6.Fs.InodeW3Certificates

namespace Xv6.Fs.Image

theorem inodes_durable_valid_checked : inodesDurableValid blockView superblock = true :=
  inodesValid_durable blockView superblock inodes_valid_checked

theorem live_inode_durable_ok (z : Int) (live : z ∈ liveSet blockView superblock) :
    InodeDurableOK blockView superblock (dinode blockView superblock z) :=
  (live_inode_ok z live).durable _ _ _

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.InodeW3.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
