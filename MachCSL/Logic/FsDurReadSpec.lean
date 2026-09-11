import MachCSL.Logic.FsDurReadDefs

namespace MachCSL.Logic.FsDurRead
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState
variable {GF : BundledGFunctors}

structure ReadSpec (capacity : Disk.Capacity GF) : Prop where
  runSub : ∀ g gl gt disk dq b off bytes,
    FsDurBytes.snapAuth capacity g disk ∗ FsView.byteRangeQ (FsView.snapGamma capacity g gl gt) dq b off bytes ⊢
      ⌜PartialMap.submap (M := Disk.ImageMap) (FsDurBytes.byteRun (b * 1024 + off) bytes) (FsDurBytes.flatten disk)⌝
  runRead : ∀ g gl gt disk dq b off bytes, BlocksFull disk → 0 ≤ off → off + (bytes.length : Int) ≤ 1024 →
    0 < bytes.length →
    FsDurBytes.snapAuth capacity g disk ∗ FsView.byteRangeQ (FsView.snapGamma capacity g gl gt) dq b off bytes ⊢
      ⌜RunSlice disk b off bytes⌝
  blockRead : ∀ g gl gt disk dq b bytes, BlocksFull disk →
    FsDurBytes.snapAuth capacity g disk ∗ FsView.blockOwnedQ (FsView.snapGamma capacity g gl gt) dq b bytes ⊢
      ⌜disk[b]? = some bytes⌝

structure OverlapSpec (view : FsView.View GF) : Prop where
  overlap : ∀ (dq1 dq2 : DFrac) b off1 off2 bytes1 bytes2 (k1 k2 : Nat), FsView.PhiExcl view →
    ¬✓ (dq1 • dq2) → k1 < bytes1.length → k2 < bytes2.length →
    off1 + (k1 : Int) = off2 + (k2 : Int) →
    FsView.byteRangeQ view dq1 b off1 bytes1 ∗ FsView.byteRangeQ view dq2 b off2 bytes2 ⊢ ⌜False⌝
  poolUsed : ∀ nb used b off bytes, FsView.PhiExcl view →
    0 ≤ b ∧ b < nb → 0 ≤ off → off + (bytes.length : Int) ≤ 1024 → 0 < bytes.length →
    FsState.freePool view nb used ∗ FsView.byteRange view b off bytes ⊢ ⌜b ∈ used⌝

end MachCSL.Logic.FsDurRead
