import MachCSL.Logic.FsDurSnapshotXferDefs
import MachCSL.Logic.FsDurXferSpec

namespace MachCSL.Logic.FsDurSnapshotXfer
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurSnapshot FsDurXferRuns
variable {GF : BundledGFunctors}

structure Spec (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF) : Prop where
  transfer : ∀ (view : FsView.View GF), FsView.PhiExcl view → ∀ authority whole,
    PhiAgree view authority whole → ∀ (q : Qp) state disk ty,
    (1 : Qp).half < q → Snapshot.Shape state disk →
    PartialMap.submap (M := Disk.ImageMap) whole (FsDurBytes.flatten disk) →
    iprop(authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link 1 ty ⊢
      |==> (authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link 1 ty ∗ Pdur dc lc tc disk))
  clone : ∀ disk, iprop(Pdur dc lc tc disk ⊢ |==> (Pdur dc lc tc disk ∗ Pdur dc lc tc disk))
  step : ∀ old next, Pdur dc lc tc next ⊢ dsnapStep dc lc tc old next

end MachCSL.Logic.FsDurSnapshotXfer
