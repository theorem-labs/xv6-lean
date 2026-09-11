import MachCSL.Logic.FsDurInstallSpec
import MachCSL.Logic.FsDurXferShapeProofs

namespace MachCSL.Logic.FsDurInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns FsDurXferShape
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem phi_map_install (part whole : FsDurBytes.ByteMap)
    (subset : PartialMap.submap (M := Disk.ImageMap) part whole) :
    phiMap view whole ⊣⊢ phiMap view part ∗ phiMap view (PartialMap.difference (M := Disk.ImageMap) whole part) := by
  have law := BigSepM.bigSepM_union (M := Disk.ImageMap) (Φ := fun a v => view.phi (.own 1) a v)
    (LawfulPartialMap.disjoint_difference_right (M := Disk.ImageMap) (m₁ := whole) (m₂ := part))
  rw [LawfulPartialMap.union_difference_cancel (M := Disk.ImageMap) subset] at law
  exact law

theorem fs_footprint_install state pool whole (shape : FsDurXferShape.Shape state pool)
    (disjoint : RunsDisjoint (fsRuns state pool))
    (subset : PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) whole) :
    phiMap view whole ⊢ FsState.footprint view (.own 1) state ∗ phiMap view (remainder state pool whole) := by
  iintro H
  ihave ⟨Hpart, Hrest⟩ := (phi_map_install view _ whole subset).mp $$ H
  ihave Hruns := (phi_runs_union view (fsRuns state pool) disjoint).mpr $$ Hpart
  ihave Hfoot := fs_footprint_of_runs view state pool shape $$ Hruns
  unfold remainder
  iframe Hfoot Hrest

theorem fs_footprint_install_nonvac (exclusive : FsView.PhiExcl view) state :
    FsState.footprint view (.own 1) state ⊢ ∃ pool whole,
      ⌜Facts state pool whole ∧ remainder state pool whole = ∅⌝ ∗ phiMap view whole := by
  iintro H
  ihave ⟨%pool, %shape, Hruns⟩ := fs_footprint_runs view state $$ H
  ihave %disjoint := phi_runs_disj view exclusive (fsRuns state pool) $$ Hruns
  ihave Hmap := (phi_runs_union view (fsRuns state pool) disjoint).mp $$ Hruns
  iexists pool, runUnion (fsRuns state pool)
  iframe Hmap
  ipureintro
  refine ⟨⟨shape, disjoint, fun _ _ h => h⟩, ?_⟩
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro address
  change get? (M := Disk.ImageMap) (remainder state pool (runUnion (fsRuns state pool))) address = get? (M := Disk.ImageMap) ∅ address
  unfold remainder
  rw [show get? (M := Disk.ImageMap) (PartialMap.difference (M := Disk.ImageMap) (runUnion (fsRuns state pool)) (runUnion (fsRuns state pool))) address = _ from LawfulPartialMap.get?_difference (M := Disk.ImageMap) (m₁ := runUnion (fsRuns state pool)) (m₂ := runUnion (fsRuns state pool)) (k := address)]
  cases get? (M := Disk.ImageMap) (runUnion (fsRuns state pool)) address <;> rfl

theorem fs_state_install (lc : FsLink.Capacity GF) state pool whole (shape : FsDurXferShape.Shape state pool)
    (disjoint : RunsDisjoint (fsRuns state pool))
    (subset : PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) whole) :
    phiMap view whole ∗ FsState.ghost view lc state ⊢
      FsState.state view lc (.own 1) state ∗ phiMap view (remainder state pool whole) := by
  iintro ⟨Hmap, Hghost⟩
  ihave ⟨Hfoot, Hrest⟩ := fs_footprint_install view state pool whole shape disjoint subset $$ Hmap
  ihave Hstate := (FsState.state_split view lc (.own 1) state).mpr $$ [$Hfoot $Hghost]
  iframe Hstate Hrest

theorem installSpec (lc : FsLink.Capacity GF) : InstallSpec view lc where
  mapSplit := phi_map_install view
  footprint state pool whole facts := fs_footprint_install view state pool whole facts.shape facts.disjoint facts.included
  state state pool whole facts := fs_state_install view lc state pool whole facts.shape facts.disjoint facts.included

theorem fs_footprint_install_facts (dc : Disk.Capacity GF) g gl gt whole state :
    Disk.mapAuth dc g whole ∗ FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state ⊢
      ∃ pool, ⌜Facts state pool whole⌝ := by
  iintro ⟨Ha, Hfoot⟩
  ihave ⟨%pool, %shape, Hruns⟩ := fs_footprint_runs (FsView.snapGamma dc g gl gt) state $$ Hfoot
  ihave %disjoint := phi_runs_disj (FsView.snapGamma dc g gl gt) (FsView.snapGamma_excl dc g gl gt) (fsRuns state pool) $$ Hruns
  ihave %subset := phi_runs_in (FsView.snapGamma dc g gl gt) (Disk.mapAuth dc g whole) whole
    (snap_gamma_agree dc g gl gt whole) (fsRuns state pool) disjoint $$ [$Ha $Hruns]
  iexists pool
  ipureintro
  exact ⟨shape, disjoint, subset⟩

theorem sourceSpec (dc : Disk.Capacity GF) : SourceSpec dc where
  facts := fs_footprint_install_facts dc

end MachCSL.Logic.FsDurInstall
