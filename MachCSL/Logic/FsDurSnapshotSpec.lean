import MachCSL.Logic.FsDurSnapshotDefs
import MachCSL.Logic.FsDurAssembleDefs

namespace MachCSL.Logic.FsDurSnapshot
open Iris Iris.Std Iris.BI Xv6.Fs DurableState
variable {GF : BundledGFunctors}

structure SnapshotSpec (diskCapacity : Disk.Capacity GF) (linkCapacity : FsLink.Capacity GF)
    (topCapacity : FsTop.Capacity GF) : Prop where
  shape : ∀ view g disk state,
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢ ⌜Snapshot.Shape state disk⌝
  state : ∀ view g disk state,
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢ FsState.state view linkCapacity (.own 1) state
  registry : ∀ g gl gt disk state,
    fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state ⊢
      Pdur diskCapacity linkCapacity topCapacity disk

/-- Source value-first constructor, designated for initial epoch setup.
This API name is not a linear permission and does not enforce once-only use.
Runtime integration must use source-instance transfer instead. -/
structure InitialSpec (diskCapacity : Disk.Capacity GF) (linkCapacity : FsLink.Capacity GF)
    (topCapacity : FsTop.Capacity GF) : Prop where
  snapshot : ∀ state disk, Snapshot.OK state disk → ∀ frame : IProp GF,
    frame ⊢ |==> ∃ g gl gt,
      fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state ∗
      FsDurAssemble.remainder (FsView.snapGamma diskCapacity g gl gt) (FsDurBytes.flatten disk) state disk ∗ frame
  durable : ∀ state disk, Snapshot.OK state disk → ∀ frame : IProp GF,
    frame ⊢ |==> (Pdur diskCapacity linkCapacity topCapacity disk ∗ frame)

end MachCSL.Logic.FsDurSnapshot
