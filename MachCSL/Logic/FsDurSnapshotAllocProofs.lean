import MachCSL.Logic.FsDurSnapshotProofs
import MachCSL.Logic.FsDurAssembleProofs
import MachCSL.Logic.FsStateLinkAllocProofs

/-! The value-first source constructor is for initial epoch setup only.
These ordinary Iris allocation lemmas do not enforce once-only use. Runtime
commit/reboot integration must supply the source-instance transfer path. -/
namespace MachCSL.Logic.FsDurSnapshot.Initial
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState
variable {GF : BundledGFunctors} (diskCapacity : Disk.Capacity GF)
  (linkCapacity : FsLink.Capacity GF) (topCapacity : FsTop.Capacity GF)

/-- Allocate one fresh snapshot name at the existing disk image camera. -/
theorem snap_bytes_alloc (bytes : FsDurBytes.ByteMap) :
    iprop(⊢ |==> ∃ g : GName, Disk.mapAuth diskCapacity g bytes ∗ FsDurBytes.imageBytesFull diskCapacity g bytes) := by
  letI := diskCapacity.image
  exact ghost_map_alloc (H := Disk.ImageMap) (GF := GF) bytes

/-- Source fs_snap_alloc, retaining the exact uncarved bytes and caller's frame.
It is designated for the initial image producer, not a runtime epoch update. -/
theorem fs_snap_alloc (state : State) disk (ok : Snapshot.OK state disk) (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ g gl gt,
      fsSnap diskCapacity linkCapacity topCapacity (FsView.snapGamma diskCapacity g gl gt) g disk state ∗
      FsDurAssemble.remainder (FsView.snapGamma diskCapacity g gl gt) (FsDurBytes.flatten disk) state disk ∗ frame) := by
  iintro Hframe
  imod snap_bytes_alloc diskCapacity (FsDurBytes.flatten disk) with ⟨%g, HbyteAuth, Hbytes⟩
  obtain ⟨choices, rootType, choiceOK, valid⟩ := ok.1.links
  imod FsState.boot_alloc_root_slack linkCapacity topCapacity state.inodes choices 1 rootType choiceOK valid
    with ⟨%gl, %gt, HtopAuth, HtopFrags, Hlinks, Hroot⟩
  let view := FsView.snapGamma diskCapacity g gl gt
  have bytes_view : FsDurBytes.imageBytesFull diskCapacity g (FsDurBytes.flatten disk) =
      FsDurBytes.byteLedger view (FsDurBytes.flatten disk) := rfl
  ihave Hbytes := (BIBase.BiEntails.of_eq bytes_view).mp $$ Hbytes
  have links_view : FsState.links linkCapacity gl state.inodes = FsState.links linkCapacity view.link state.inodes := rfl
  ihave Hlinks := (BIBase.BiEntails.of_eq links_view).mp $$ Hlinks
  ihave ⟨Hstate, Hrest, Hframe⟩ := FsDurAssemble.state_of_image view linkCapacity state disk ok
    (FsDurBytes.flatten disk) (PartialMap.subset_refl _) frame $$ [$Hbytes $Hlinks $Hframe]
  imodintro
  iexists g, gl, gt
  isplitl [HbyteAuth HtopAuth HtopFrags Hstate Hroot]
  · unfold fsSnap
    rw [show (FsView.snapGamma diskCapacity g gl gt).top = gt from rfl,
      show (FsView.snapGamma diskCapacity g gl gt).link = gl from rfl]
    isplitl [HbyteAuth]
    · unfold FsDurBytes.snapAuth
      iexists (FsDurBytes.flatten disk)
      iframe HbyteAuth
      ipureintro
      exact PartialMap.subset_refl _
    isplitl [HtopAuth]
    · iexact HtopAuth
    isplitl [HtopFrags]
    · iexact HtopFrags
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Hroot]
    · iexists rootType
      iexact Hroot
    · ipureintro
      exact Snapshot.ok_shape ok
  · iframe Hrest Hframe

/-- The exact source existential registry result. The stronger constructor
above additionally exposes the uncarved snapshot-byte remainder. -/
theorem P_dur_alloc (state : State) disk (ok : Snapshot.OK state disk) (frame : IProp GF) :
    iprop(frame ⊢ |==> (Pdur diskCapacity linkCapacity topCapacity disk ∗ frame)) := by
  refine (fs_snap_alloc diskCapacity linkCapacity topCapacity state disk ok frame).trans (bupd_mono ?_)
  iintro ⟨%g, %gl, %gt, Hsnap, _, Hframe⟩
  iframe Hframe
  iapply Pdur_intro diskCapacity linkCapacity topCapacity g gl gt disk state $$ Hsnap

theorem initialSpec : InitialSpec diskCapacity linkCapacity topCapacity where
  snapshot := fs_snap_alloc diskCapacity linkCapacity topCapacity
  durable := P_dur_alloc diskCapacity linkCapacity topCapacity

end MachCSL.Logic.FsDurSnapshot.Initial
