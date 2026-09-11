import MachCSL.Logic.FsDurInstallProofs
import MachCSL.Logic.FsDurBytesLedgerProofs
import MachCSL.Logic.FsTopLink
import Xv6.Fs.SnapshotHomeProofs

namespace MachCSL.Logic.FsDurInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns FsDurXferShape
variable {GF : BundledGFunctors}

/-- The source finite-set restriction and the native finite-map constructor agree. -/
theorem restrict_ofSetWith (image : Blocks) (home : BlockSet) :
    SnapshotHome.restrict image home = (FiniteMap.ofSetWith (M := Disk.ImageMap) image home) := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro b
  rw [SnapshotHome.restrict_lookup]
  have perm := LawfulFiniteMap.toList_ofSetWith (M := Disk.ImageMap) (g := image) (s := home)
  have lookup (bytes : List (BitVec 8)) :
      get? (M := Disk.ImageMap) (FiniteMap.ofSetWith (M := Disk.ImageMap) image home) b = some bytes ↔
        b ∈ home ∧ bytes = image b := by
    rw [← LawfulFiniteMap.toList_get (M := Disk.ImageMap), perm.mem_iff]
    simp only [List.mem_map, FiniteSet.mem_toList, Prod.mk.injEq]
    constructor
    · rintro ⟨key, member, same, value⟩
      subst key
      exact ⟨member, value.symm⟩
    · rintro ⟨member, rfl⟩
      exact ⟨b, member, rfl, rfl⟩
  by_cases member : b ∈ home
  · rw [if_pos member]
    exact ((lookup (image b)).mpr ⟨member, rfl⟩).symm
  · rw [if_neg member]
    change none = get? (M := Disk.ImageMap) (FiniteMap.ofSetWith (M := Disk.ImageMap) image home) b
    cases found : get? (M := Disk.ImageMap) (FiniteMap.ofSetWith (M := Disk.ImageMap) image home) b with
    | none => rfl
    | some bytes => exact False.elim (member ((lookup bytes).mp found).1)

theorem phi_map_set_blocks (view : FsView.View GF) (image : Blocks) (home : BlockSet)
    (full : ∀ b, b ∈ home → (image b).length = 1024) :
    phiMap view (FsDurBytes.flatten (SnapshotHome.restrict image home)) ⊣⊢
      bigSepS (fun b => FsView.blockOwned view b (image b)) home := by
  have blocksFull : FsDurBytes.BlocksFull (SnapshotHome.restrict image home) := by
    intro b bytes found
    obtain ⟨member, rfl⟩ := (SnapshotHome.restrict_lookup_some image home b bytes).mp found
    exact full b member
  calc
    _ ⊣⊢ FsDurBytes.blockLedger view (SnapshotHome.restrict image home) :=
      FsDurBytes.flatten_blocks view _ blocksFull
    _ ⊣⊢ _ := by
      rw [restrict_ofSetWith]
      exact BigSepM.bigSepM_ofSetWith (M := Disk.ImageMap)
        (fun b bytes => FsView.blockOwned view b bytes) image home

theorem fs_home_install (view : FsView.View GF) (image : Blocks) (home : BlockSet) state pool
    (full : ∀ b, b ∈ home → (image b).length = 1024)
    (shape : FsDurXferShape.Shape state pool)
    (disjoint : RunsDisjoint (fsRuns state pool))
    (subset : PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool))
      (FsDurBytes.flatten (SnapshotHome.restrict image home))) :
    bigSepS (fun b => FsView.blockOwned view b (image b)) home ⊢
      FsState.footprint view (.own 1) state ∗
        phiMap view (remainder state pool (FsDurBytes.flatten (SnapshotHome.restrict image home))) :=
  (phi_map_set_blocks view image home full).mpr.trans
    (fs_footprint_install view state pool _ shape disjoint subset)

theorem registrySourceSpec : SourceSpec FsTop.eraCapacity.disk :=
  sourceSpec _

theorem registryInstallSpec (view : FsView.View FsTop.registry) : InstallSpec view FsTop.linkCapacity :=
  installSpec view _

end MachCSL.Logic.FsDurInstall
