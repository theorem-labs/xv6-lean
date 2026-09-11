import MachCSL.Logic.FsDurSnapshotXferProofs

namespace MachCSL.Logic.FsDurSnapshotXfer
open Iris Iris.BI Xv6.Fs DurableState FsDurSnapshot

theorem registrySpec : Spec FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity :=
  actual _ _ _

theorem registryClone disk : iprop(Pdur FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk ⊢
    |==> (Pdur FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk ∗
      Pdur FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk)) :=
  P_dur_clone _ _ _ disk

theorem registryStep old next : Pdur FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity next ⊢
    dsnapStep FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity old next :=
  dsnap_step_xfer _ _ _ old next

end MachCSL.Logic.FsDurSnapshotXfer
