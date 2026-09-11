import MachCSL.Logic.FsDurSnapshotXferSpec
import MachCSL.Logic.FsDurXferLink
import MachCSL.Logic.FsDurSnapshotProofs

namespace MachCSL.Logic.FsDurSnapshotXfer
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurSnapshot FsDurXferRuns
variable {GF : BundledGFunctors} (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF)

/-- Exact source epoch allocation off an owned filesystem instance. -/
theorem P_dur_alloc_xfer (view : FsView.View GF) (exclusive : FsView.PhiExcl view)
    authority whole (agree : PhiAgree view authority whole) (q : Qp) state disk ty
    (half : (1 : Qp).half < q) (shape : Snapshot.Shape state disk)
    (subset : PartialMap.submap (M := Disk.ImageMap) whole (FsDurBytes.flatten disk)) :
    iprop(authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link 1 ty ⊢
      |==> (authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link 1 ty ∗ Pdur dc lc tc disk)) := by
  iintro ⟨Ha, Hstate, Htok⟩
  imod FsDurXfer.fs_state_xfer_tok dc lc tc view exclusive authority whole agree q state 1 ty half
    $$ [$Ha $Hstate $Htok] with ⟨%g, %gl, %gt, %bytes, %included, Ha, Hstate, Htok, HbyteAuth, HtopAuth, HtopFrags, HnewState, HnewTok⟩
  imodintro
  iframe Ha Hstate Htok
  unfold Pdur
  iexists g, gl, gt, state
  unfold fsSnap
  rw [show (FsView.snapGamma dc g gl gt).top = gt from rfl,
    show (FsView.snapGamma dc g gl gt).link = gl from rfl]
  isplitl [HbyteAuth]
  · unfold FsDurBytes.snapAuth
    iexists bytes
    iframe HbyteAuth
    ipureintro
    exact fun address byte found => subset address byte (included address byte found)
  isplitl [HtopAuth]
  · iexact HtopAuth
  isplitl [HtopFrags]
  · iexact HtopFrags
  isplitl [HnewState]
  · iexact HnewState
  isplitl [HnewTok]
  · iexists ty
    iexact HnewTok
  · ipureintro
    exact shape

/-- The first epoch is returned at its original names; the second is
constructed by source-instance transport, not by duplicating ownership. -/
theorem P_dur_clone disk :
    iprop(Pdur dc lc tc disk ⊢ |==> (Pdur dc lc tc disk ∗ Pdur dc lc tc disk)) := by
  iintro H
  iunfold Pdur at H
  icases H with ⟨%g, %gl, %gt, %state, Hsnap⟩
  iunfold fsSnap at Hsnap
  icases Hsnap with ⟨HbyteAuth, HtopAuth, HtopFrags, Hstate, Htok, %shape⟩
  iunfold FsDurBytes.snapAuth at HbyteAuth
  icases HbyteAuth with ⟨%bytes, HbyteAuth, %subset⟩
  icases Htok with ⟨%ty, Htok⟩
  imod P_dur_alloc_xfer dc lc tc (FsView.snapGamma dc g gl gt) (FsView.snapGamma_excl dc g gl gt)
    (Disk.mapAuth dc g bytes) bytes (snap_gamma_agree dc g gl gt bytes) 1 state disk ty
    qp_half_lt_1 shape subset $$ [$HbyteAuth $Hstate $Htok] with ⟨HbyteAuth, Hstate, Htok, Hnew⟩
  imodintro
  isplitr [Hnew]
  · unfold Pdur
    iexists g, gl, gt, state
    unfold fsSnap
    isplitl [HbyteAuth]
    · unfold FsDurBytes.snapAuth
      iexists bytes
      iframe HbyteAuth
      ipureintro
      exact subset
    isplitl [HtopAuth]
    · iexact HtopAuth
    isplitl [HtopFrags]
    · iexact HtopFrags
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Htok]
    · iexists ty
      iexact Htok
    · ipureintro
      exact shape
  · iexact Hnew

/-- Source registry swap: the next epoch is already provided; the affine
old epoch is discarded. This theorem allocates and updates no ghost name. -/
theorem dsnap_step_xfer old next : Pdur dc lc tc next ⊢ dsnapStep dc lc tc old next := by
  unfold dsnapStep
  iintro Hnext Hold
  imodintro
  iexact Hnext

theorem actual : Spec dc lc tc where
  transfer := P_dur_alloc_xfer dc lc tc
  clone := P_dur_clone dc lc tc
  step := dsnap_step_xfer dc lc tc

end MachCSL.Logic.FsDurSnapshotXfer
