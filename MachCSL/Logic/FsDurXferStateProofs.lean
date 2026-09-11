import MachCSL.Logic.FsDurXferByteProofs
import MachCSL.Logic.FsStateLinkAllocProofs

namespace MachCSL.Logic.FsDurXfer
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState FsDurXferRuns FsDurXferShape
variable {GF : BundledGFunctors} (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF)

theorem fs_state_xfer (view : FsView.View GF) (exclusive : FsView.PhiExcl view)
    authority whole (agree : PhiAgree view authority whole) (q : Qp) state (half : (1 : Qp).half < q) :
    iprop(authority ∗ FsState.state view lc (.own q) state ⊢ |==> ∃ g gl gt bytes,
      ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.state view lc (.own q) state ∗ Disk.mapAuth dc g bytes ∗
      FsTop.auth tc gt state.inodes ∗ FsTop.allFragments tc gt state.inodes ∗
      FsState.state (FsView.snapGamma dc g gl gt) lc (.own 1) state) := by
  iintro ⟨Ha, Hstate⟩
  ihave ⟨Hfoot, Hghost⟩ := (FsState.state_split view lc (.own q) state).mp $$ Hstate
  ihave ⟨Hlinks, #Hp⟩ := (FsState.ghost_split view lc state).mp $$ Hghost
  ihave ⟨%f, %ok, %valid⟩ := FsState.links_valid lc view.link state.inodes $$ Hlinks
  imod FsState.boot_alloc_at lc tc state.inodes state.inodes f ok valid with ⟨%gl, %gt, HtopAuth, HtopFrags, HnewLinks⟩
  imod fs_footprint_xfer dc view exclusive authority whole agree (.own q) state gl gt
    (dfrac_own_gt_half q half) $$ [$Ha $Hfoot] with ⟨%g, %bytes, %subset, Ha, Hfoot, HbyteAuth, HnewFoot⟩
  ihave Hghost := (FsState.ghost_split view lc state).mpr $$ [$Hlinks $Hp]
  ihave Hstate := (FsState.state_split view lc (.own q) state).mpr $$ [$Hfoot $Hghost]
  have links_same : FsState.links lc gl state.inodes =
      FsState.links lc (FsView.snapGamma dc g gl gt).link state.inodes := rfl
  ihave HnewLinks := (BIBase.BiEntails.of_eq links_same).mp $$ HnewLinks
  ihave HnewGhost := (FsState.ghost_split (FsView.snapGamma dc g gl gt) lc state).mpr $$ [$HnewLinks $Hp]
  ihave HnewState := (FsState.state_split (FsView.snapGamma dc g gl gt) lc (.own 1) state).mpr $$ [$HnewFoot $HnewGhost]
  imodintro
  iexists g, gl, gt, bytes
  iframe Ha Hstate HbyteAuth HtopAuth HtopFrags HnewState
  ipureintro
  exact subset

theorem fs_state_xfer_tok (view : FsView.View GF) (exclusive : FsView.PhiExcl view)
    authority whole (agree : PhiAgree view authority whole) (q : Qp) state root ty (half : (1 : Qp).half < q) :
    iprop(authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link root ty ⊢
      |==> ∃ g gl gt bytes, ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link root ty ∗ Disk.mapAuth dc g bytes ∗
      FsTop.auth tc gt state.inodes ∗ FsTop.allFragments tc gt state.inodes ∗
      FsState.state (FsView.snapGamma dc g gl gt) lc (.own 1) state ∗ FsLink.tok lc gl root ty) := by
  iintro ⟨Ha, Hstate, Htok⟩
  ihave ⟨Hfoot, Hghost⟩ := (FsState.state_split view lc (.own q) state).mp $$ Hstate
  ihave ⟨Hlinks, #Hp⟩ := (FsState.ghost_split view lc state).mp $$ Hghost
  ihave ⟨%f, %ok, %valid⟩ := FsState.links_valid_tok lc view.link state.inodes root ty $$ Hlinks Htok
  imod FsState.boot_alloc_root_slack lc tc state.inodes f root ty ok valid with ⟨%gl, %gt, HtopAuth, HtopFrags, HnewLinks, HnewTok⟩
  imod fs_footprint_xfer dc view exclusive authority whole agree (.own q) state gl gt
    (dfrac_own_gt_half q half) $$ [$Ha $Hfoot] with ⟨%g, %bytes, %subset, Ha, Hfoot, HbyteAuth, HnewFoot⟩
  ihave Hghost := (FsState.ghost_split view lc state).mpr $$ [$Hlinks $Hp]
  ihave Hstate := (FsState.state_split view lc (.own q) state).mpr $$ [$Hfoot $Hghost]
  have links_same : FsState.links lc gl state.inodes =
      FsState.links lc (FsView.snapGamma dc g gl gt).link state.inodes := rfl
  ihave HnewLinks := (BIBase.BiEntails.of_eq links_same).mp $$ HnewLinks
  ihave HnewGhost := (FsState.ghost_split (FsView.snapGamma dc g gl gt) lc state).mpr $$ [$HnewLinks $Hp]
  ihave HnewState := (FsState.state_split (FsView.snapGamma dc g gl gt) lc (.own 1) state).mpr $$ [$HnewFoot $HnewGhost]
  imodintro
  iexists g, gl, gt, bytes
  iframe Ha Hstate Htok HbyteAuth HtopAuth HtopFrags HnewState HnewTok
  ipureintro
  exact subset

theorem stateSpec : StateSpec dc lc tc where
  transfer := fs_state_xfer dc lc tc
  transferToken := fs_state_xfer_tok dc lc tc

end MachCSL.Logic.FsDurXfer
