import MachCSL.Logic.FsDurXferSpec

namespace MachCSL.Logic.FsDurXfer
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState FsDurXferRuns FsDurXferShape
variable {GF : BundledGFunctors} (dc : Disk.Capacity GF)

/-- Exact source mint. This pure-fact helper allocates at the run union;
its source-instance caller below reads both premises from owned resources. -/
theorem fs_footprint_mint state pool gl gt (shape : Shape state pool)
    (disjoint : RunsDisjoint (fsRuns state pool)) :
    iprop(⊢ |==> ∃ g, Disk.mapAuth dc g (runUnion (fsRuns state pool)) ∗
      FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state) := by
  letI := dc.image
  have allocate : iprop(⊢ |==> ∃ g, Disk.mapAuth dc g (runUnion (fsRuns state pool)) ∗
      FsDurBytes.imageBytesFull dc g (runUnion (fsRuns state pool))) :=
    ghost_map_alloc (H := Disk.ImageMap) (GF := GF) (runUnion (fsRuns state pool))
  imod allocate with ⟨%g, Ha, Hmap⟩
  imodintro
  iexists g
  iframe Ha
  have same : FsDurBytes.imageBytesFull dc g (runUnion (fsRuns state pool)) =
      phiMap (FsView.snapGamma dc g gl gt) (runUnion (fsRuns state pool)) := rfl
  ihave Hmap := (BIBase.BiEntails.of_eq same).mp $$ Hmap
  ihave Hruns := (phi_runs_union (FsView.snapGamma dc g gl gt) (fsRuns state pool) disjoint).mpr $$ Hmap
  iapply fs_footprint_of_runs (FsView.snapGamma dc g gl gt) state pool shape $$ Hruns

theorem fs_footprint_xfer (view : FsView.View GF) (exclusive : FsView.PhiExcl view)
    authority whole (agree : PhiAgree view authority whole) (dq : DFrac) state gl gt (share : ¬✓ (dq • dq)) :
    iprop(authority ∗ FsState.footprint view dq state ⊢ |==> ∃ g bytes,
      ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.footprint view dq state ∗ Disk.mapAuth dc g bytes ∗
      FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state) := by
  iintro ⟨Ha, Hfoot⟩
  ihave ⟨%pool, %shape, Hruns⟩ := fs_footprint_runs_q view dq state $$ Hfoot
  have shares := sharesOK_atShare dq (fsRuns state pool) share
  ihave %disjoint := phi_runs_q_disj view exclusive (atShare dq (fsRuns state pool)) shares $$ Hruns
  rw [strip_atShare] at disjoint
  ihave %subset := phi_runs_q_in view authority whole agree (atShare dq (fsRuns state pool)) $$ [$Ha $Hruns]
  rw [strip_atShare] at subset
  imod fs_footprint_mint dc state pool gl gt shape disjoint with ⟨%g, HnewAuth, HnewFoot⟩
  ihave Hfoot := fs_footprint_of_runs_q view dq state pool shape $$ Hruns
  imodintro
  iexists g, runUnion (fsRuns state pool)
  iframe Ha Hfoot HnewAuth HnewFoot
  ipureintro
  exact subset

theorem mintSpec : MintSpec dc where
  footprint := fs_footprint_mint dc

theorem byteSpec : ByteSpec dc where
  transfer := fs_footprint_xfer dc

end MachCSL.Logic.FsDurXfer
