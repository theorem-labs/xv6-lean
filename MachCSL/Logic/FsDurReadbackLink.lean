import MachCSL.Logic.FsDurReadbackProofs
import MachCSL.Logic.FsDurSnapshotLink

namespace MachCSL.Logic.FsDurReadback
open Iris Iris.Std Iris.BI Xv6.Fs DurableState

theorem registryReadbackSpec : ReadbackSpec FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity :=
  readbackSpec FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity

theorem registry_snapshot g gl gt disk state (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.fsSnap FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
      (FsView.snapGamma FsTop.eraCapacity.disk g gl gt) g disk state ⊢ ⌜Snapshot.OK state disk⌝ :=
  fs_snap_read_ok FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity g gl gt disk state full

theorem registry_snapshot_keep g gl gt disk state (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.fsSnap FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
      (FsView.snapGamma FsTop.eraCapacity.disk g gl gt) g disk state ⊢
    ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.fsSnap FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
      (FsView.snapGamma FsTop.eraCapacity.disk g gl gt) g disk state :=
  fs_snap_read_ok_keep FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity g gl gt disk state full

theorem registry_tie disk (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.registryPdur disk ⊢ ∃ state, ⌜Snapshot.OK state disk⌝ :=
  P_dur_tie FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk full

theorem registry_tie_keep disk (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.registryPdur disk ⊢ ∃ state, ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.registryPdur disk :=
  P_dur_tie_keep FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk full

end MachCSL.Logic.FsDurReadback
