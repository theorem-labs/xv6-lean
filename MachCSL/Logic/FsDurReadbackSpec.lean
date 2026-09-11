import MachCSL.Logic.FsDurSnapshotDefs

namespace MachCSL.Logic.FsDurReadback
open Iris Iris.Std Iris.BI Xv6.Fs DurableState
variable {GF : BundledGFunctors}

structure ReadbackSpec (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF) : Prop where
  snapshot : ∀ g gl gt disk state, FsDurBytes.BlocksFull disk →
    FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state ⊢ ⌜Snapshot.OK state disk⌝
  snapshotKeep : ∀ g gl gt disk state, FsDurBytes.BlocksFull disk →
    FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state ⊢
      ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state
  durable : ∀ disk, FsDurBytes.BlocksFull disk → FsDurSnapshot.Pdur dc lc tc disk ⊢ ∃ state, ⌜Snapshot.OK state disk⌝
  durableKeep : ∀ disk, FsDurBytes.BlocksFull disk → FsDurSnapshot.Pdur dc lc tc disk ⊢
    ∃ state, ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.Pdur dc lc tc disk

end MachCSL.Logic.FsDurReadback
