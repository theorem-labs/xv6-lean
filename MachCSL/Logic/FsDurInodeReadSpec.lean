import MachCSL.Logic.FsDurInodeReadDefs

namespace MachCSL.Logic.FsDurInodeRead
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors}

structure OwnershipSpec (view : FsView.View GF) : Prop where
  owns : ∀ node block, node.Owns block →
    FsState.inodeDat view node ⊢ ∃ bytes, FsView.blockOwned view block bytes
  injective : ∀ i node, FsView.PhiExcl view → DurableNode.Local i node →
    FsState.inodeDat view node ⊢ ⌜node.SlotInjective⌝

structure ReadSpec (capacity : Disk.Capacity GF) : Prop where
  inode : ∀ g gl gt disk sb i node, FsDurRead.BlocksFull disk →
    0 ≤ i ∧ i < 2 ^ 32 → DurableNode.Local i node →
    FsDurBytes.snapAuth capacity g disk ∗ FsState.inodePhi (FsView.snapGamma capacity g gl gt) sb i node ⊢
      ⌜Snapshot.InodeRead sb disk i node⌝
  inodes : ∀ g gl gt disk sb nodes, FsDurRead.BlocksFull disk →
    (∀ (i : Int) node, nodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32) →
    (∀ (i : Int) node, nodes[i]? = some node → DurableNode.Local i node) →
    FsDurBytes.snapAuth capacity g disk ∗ inodeLeg (FsView.snapGamma capacity g gl gt) sb nodes ⊢
      ⌜∀ i node, nodes[i]? = some node → Snapshot.InodeRead sb disk i node⌝

end MachCSL.Logic.FsDurInodeRead
