import MachCSL.Logic.FsDurReadDefs
import MachCSL.Logic.FsStateInodeDefs
import Xv6.Fs.SnapshotDefs

/-! Source FsDurSnap §7b's inode byte legs. The stored slot map remains
arbitrary, including allocations beyond file size; validity is a caller premise. -/
namespace MachCSL.Logic.FsDurInodeRead
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors}

def dataLeg (view : FsView.View GF) (node : Node) : IProp GF :=
  bigSepM (M := FsState.SlotMap) (fun k bytes => FsView.blockOwned view (node.address k) bytes) node.blocks

def inodeLeg (view : FsView.View GF) (sb : Superblock) (nodes : InodeMap) : IProp GF :=
  bigSepM (M := FsState.InodeMap) (fun i node => FsState.inodePhi view sb i node) nodes

end MachCSL.Logic.FsDurInodeRead
