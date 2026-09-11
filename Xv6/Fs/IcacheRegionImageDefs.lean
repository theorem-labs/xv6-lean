import MachCSL.Logic.IcacheRegionBootDefs
import Xv6.Fs.Image
import Xv6.Fs.DurableImageNodeDefs

/-! Literal inode-region inputs from the checked artifact, separate from generic allocation. -/
namespace Xv6.Fs.Image.IcacheRegion
open MachCSL.Logic

def inodeBlocks : List (List (BitVec 8)) :=
  (List.range 13).map (fun bi : Nat => blockView (superblock.inodestart + (bi : Int)))
def state : DurableState.State := DurableImageNode.imageState blockView superblock 13
def counts (i : Int) : Nat := (SnapshotConfig.node state i).nlink
def imageRecords (i : Int) : Dinode := (SnapshotConfig.node state i).record

/-- Fix only the geometry field; all ghost names and the observation-name
function remain the caller's exact supplied values. -/
def imageNames (names : IcacheRegionSlot.Names) : IcacheRegionSlot.Names :=
  { names with epoch := { names.epoch with inodeStart := superblock.inodestart } }

end Xv6.Fs.Image.IcacheRegion
