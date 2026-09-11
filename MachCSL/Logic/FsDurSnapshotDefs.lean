import MachCSL.Logic.FsDurBytesDefs
import MachCSL.Logic.FsViewLink
import MachCSL.Logic.FsTopDefs
import MachCSL.Logic.FsStateDefs
import Xv6.Fs.SnapshotDefs

/-! Exact native durable snapshot and existential registry from
FsDurSnap.v:807–826. The only pure snapshot leg is the source Shape;
the constructor's stronger Snapshot.OK is not stored here. -/
namespace MachCSL.Logic.FsDurSnapshot
open Iris Iris.Std Iris.BI Xv6.Fs DurableState
variable {GF : BundledGFunctors} (diskCapacity : Disk.Capacity GF)
  (linkCapacity : FsLink.Capacity GF) (topCapacity : FsTop.Capacity GF)

noncomputable def fsSnap (view : FsView.View GF) (g : GName) (disk : BlockMap) (state : State) : IProp GF :=
  iprop(FsDurBytes.snapAuth diskCapacity g disk ∗
    FsTop.auth topCapacity view.top state.inodes ∗
    FsTop.allFragments topCapacity view.top state.inodes ∗
    FsState.state view linkCapacity (.own 1) state ∗
    (∃ ty : FsLink.IType, FsLink.tok linkCapacity view.link 1 ty) ∗
    ⌜Snapshot.Shape state disk⌝)

noncomputable def Pdur (disk : BlockMap) : IProp GF :=
  iprop(∃ (g gl gt : GName) (state : State),
    fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state)

end MachCSL.Logic.FsDurSnapshot
