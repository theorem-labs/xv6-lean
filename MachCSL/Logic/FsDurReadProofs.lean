import MachCSL.Logic.FsDurReadPureProofs

namespace MachCSL.Logic.FsDurRead
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState
variable {GF : BundledGFunctors}

theorem snap_run_sub (capacity : Disk.Capacity GF) g gl gt disk dq b off bytes :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.byteRangeQ (FsView.snapGamma capacity g gl gt) dq b off bytes ⊢
      ⌜PartialMap.submap (M := Disk.ImageMap) (FsDurBytes.byteRun (b * 1024 + off) bytes) (FsDurBytes.flatten disk)⌝ := by
  letI := capacity.image
  unfold FsDurBytes.snapAuth
  iintro ⟨⟨%owned, Ha, %subset⟩, Hr⟩
  unfold PartialMap.submap
  iapply pure_forall.mpr
  iintro %address
  iapply pure_forall.mpr
  iintro %byte
  iapply pure_imp.mpr
  iintro %found
  obtain ⟨k, kth, rfl⟩ := (FsDurBytes.byteRun_lookup _ _ _ _).mp found
  unfold FsView.byteRangeQ
  ihave Hk := BigSepL.bigSepL_lookup kth $$ Hr
  unfold Disk.mapAuth FsView.snapGamma
  ihave %lookup := ghost_map_lookup (H := Disk.ImageMap) (GF := GF) $$ Ha Hk
  ipureintro
  exact subset _ _ lookup

theorem snap_run_read (capacity : Disk.Capacity GF) g gl gt disk dq b off bytes
    (full : BlocksFull disk) (nonneg : 0 ≤ off) (fits : off + (bytes.length : Int) ≤ 1024)
    (nonempty : 0 < bytes.length) :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.byteRangeQ (FsView.snapGamma capacity g gl gt) dq b off bytes ⊢
      ⌜RunSlice disk b off bytes⌝ := by
  iintro H
  ihave %subset := snap_run_sub capacity g gl gt disk dq b off bytes $$ H
  ipureintro
  exact run_read disk b off bytes full nonneg fits nonempty subset

theorem snap_run_read_full (capacity : Disk.Capacity GF) g gl gt disk b off bytes
    (full : BlocksFull disk) (nonneg : 0 ≤ off) (fits : off + (bytes.length : Int) ≤ 1024)
    (nonempty : 0 < bytes.length) :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.byteRange (FsView.snapGamma capacity g gl gt) b off bytes ⊢
      ⌜RunSlice disk b off bytes⌝ :=
  snap_run_read capacity g gl gt disk (.own 1) b off bytes full nonneg fits nonempty

theorem snap_blk_read (capacity : Disk.Capacity GF) g gl gt disk dq b bytes (full : BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.blockOwnedQ (FsView.snapGamma capacity g gl gt) dq b bytes ⊢
      ⌜disk[b]? = some bytes⌝ := by
  unfold FsView.blockOwnedQ
  iintro ⟨Ha, %length, Hr⟩
  ihave %slice := snap_run_read capacity g gl gt disk dq b 0 bytes full (by omega) (by omega) (by omega) $$ [$Ha $Hr]
  ipureintro
  exact slice.full_block length

theorem snap_blk_read_full (capacity : Disk.Capacity GF) g gl gt disk b bytes (full : BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.blockOwned (FsView.snapGamma capacity g gl gt) b bytes ⊢
      ⌜disk[b]? = some bytes⌝ :=
  snap_blk_read capacity g gl gt disk (.own 1) b bytes full

theorem snap_blk_dom (capacity : Disk.Capacity GF) g gl gt disk dq b bytes (full : BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ FsView.blockOwnedQ (FsView.snapGamma capacity g gl gt) dq b bytes ⊢
      ⌜(disk[b]?).isSome⌝ := by
  iintro H
  ihave %found := snap_blk_read capacity g gl gt disk dq b bytes full $$ H
  ipureintro
  simp [found]

theorem readSpec (capacity : Disk.Capacity GF) : ReadSpec capacity where
  runSub := snap_run_sub capacity
  runRead := snap_run_read capacity
  blockRead := snap_blk_read capacity

end MachCSL.Logic.FsDurRead
