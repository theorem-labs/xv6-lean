import MachCSL.Logic.FsDurSnapshotSpec
import MachCSL.Logic.FsStateProofs
import MachCSL.Logic.FsTopProofs
import MachCSL.Logic.DiskProofs

namespace MachCSL.Logic.FsDurSnapshot
open Iris Iris.Std Iris.BI Xv6.Fs DurableState
variable {GF : BundledGFunctors} (diskCapacity : Disk.Capacity GF)
  (linkCapacity : FsLink.Capacity GF) (topCapacity : FsTop.Capacity GF)

instance snapAuth_timeless g disk : Timeless (FsDurBytes.snapAuth diskCapacity g disk) := by
  unfold FsDurBytes.snapAuth
  infer_instance

instance fsSnap_timeless (view : FsView.View GF) [FsView.GTimeless view] g disk state :
    Timeless (fsSnap diskCapacity linkCapacity topCapacity view g disk state) := by
  unfold fsSnap
  infer_instance

instance Pdur_timeless disk : Timeless (Pdur diskCapacity linkCapacity topCapacity disk) := by
  unfold Pdur
  infer_instance

theorem fsSnap_components view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊣⊢
      FsDurBytes.snapAuth diskCapacity g disk ∗ FsTop.auth topCapacity view.top state.inodes ∗
      FsTop.allFragments topCapacity view.top state.inodes ∗ FsState.state view linkCapacity (.own 1) state ∗
      (∃ ty : FsLink.IType, FsLink.tok linkCapacity view.link 1 ty) ∗ ⌜Snapshot.Shape state disk⌝ := .rfl

theorem fsSnap_shape view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢ ⌜Snapshot.Shape state disk⌝ := by
  unfold fsSnap
  iintro ⟨_, _, _, _, _, Hshape⟩
  iexact Hshape

theorem fsSnap_state view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢ FsState.state view linkCapacity (.own 1) state := by
  unfold fsSnap
  iintro ⟨_, _, _, Hstate, _, _⟩
  iexact Hstate

theorem fsSnap_identity view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢ FsDurBytes.snapAuth diskCapacity g disk := by
  unfold fsSnap
  iintro ⟨Hauth, _, _, _, _, _⟩
  iexact Hauth

theorem fsSnap_top view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢
      FsTop.auth topCapacity view.top state.inodes ∗ FsTop.allFragments topCapacity view.top state.inodes := by
  unfold fsSnap
  iintro ⟨_, Hauth, Hfrags, _, _, _⟩
  iframe Hauth Hfrags

theorem fsSnap_root view g disk state :
    fsSnap diskCapacity linkCapacity topCapacity view g disk state ⊢
      ∃ ty : FsLink.IType, FsLink.tok linkCapacity view.link 1 ty := by
  unfold fsSnap
  iintro ⟨_, _, _, _, Hroot, _⟩
  iexact Hroot

theorem Pdur_intro g gl gt disk state :
    fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state ⊢
      Pdur diskCapacity linkCapacity topCapacity disk := by
  iintro H
  unfold Pdur
  iexists g, gl, gt, state
  iexact H

theorem Pdur_components disk : Pdur diskCapacity linkCapacity topCapacity disk ⊣⊢
    ∃ (g gl gt : GName) (state : State),
      fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state := .rfl

theorem snapshotSpec : SnapshotSpec diskCapacity linkCapacity topCapacity where
  shape := fsSnap_shape diskCapacity linkCapacity topCapacity
  state := fsSnap_state diskCapacity linkCapacity topCapacity
  registry := Pdur_intro diskCapacity linkCapacity topCapacity

end MachCSL.Logic.FsDurSnapshot
