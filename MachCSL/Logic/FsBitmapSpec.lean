import MachCSL.Logic.FsBitmapDefs

namespace MachCSL.Logic.FsBitmap
open Iris Iris.Std Iris.BI Xv6.Fs DurableState SnapshotConfig
variable {GF : BundledGFunctors}

structure Spec (dc : Disk.Capacity GF) : Prop where
  poolIntro : ∀ (view : FsView.View GF) size used,
    bigSepS (fun b => iprop(∃ bytes, FsView.blockOwned view b bytes)) (freeSet size used) ⊢ FsState.freePool view size used
  openResource : ∀ names bitmapBlock size used,
    resource dc names bitmapBlock size used ⊣⊢
      FsBlocks.block dc names.bytes bitmapBlock (BitmapEncoding.bitmapBytes 1024 used) ∗
        FsState.freePool (FsBytesGamma.logged dc names) size used
  ofSnapshot : ∀ names state image home, Snapshot.Bytes state (SnapshotHome.restrict image home) →
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) (bitmapSpent state) ⊢
      resource dc names state.superblock.bmapstart state.superblock.size state.used

end MachCSL.Logic.FsBitmap
