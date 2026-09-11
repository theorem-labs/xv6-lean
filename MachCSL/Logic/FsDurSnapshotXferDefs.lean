import MachCSL.Logic.FsDurSnapshotDefs

/-! FsDurSnap.v:1368: the WAL-facing step consumes the old registry and
returns the supplied next registry through an ordinary basic update. -/
namespace MachCSL.Logic.FsDurSnapshotXfer
open Iris Iris.BI Xv6.Fs DurableState FsDurSnapshot
variable {GF : BundledGFunctors}

noncomputable def dsnapStep (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF)
    (tc : FsTop.Capacity GF) (old next : BlockMap) : IProp GF :=
  iprop(Pdur dc lc tc old -∗ |==> Pdur dc lc tc next)

end MachCSL.Logic.FsDurSnapshotXfer
