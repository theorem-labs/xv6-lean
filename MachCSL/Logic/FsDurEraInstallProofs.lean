import MachCSL.Logic.FsDurEraInstallSpec
import MachCSL.Logic.FsDurInstallLink
import MachCSL.Logic.FsBytesGammaProofs

namespace MachCSL.Logic.FsDurEraInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns FsDurXferShape FsDurInstall
variable {GF : BundledGFunctors} (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF)

theorem fs_home_blocks_phi_map (names : FsBlocks.Names) (image : Blocks) (home : BlockSet)
    (full : ∀ b, b ∈ home → (image b).length = 1024) :
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ⊣⊢
      phiMap (FsBytesGamma.logged dc names) (FsDurBytes.flatten (SnapshotHome.restrict image home)) := by
  have same : (fun b => FsBlocks.block dc names.bytes b (image b)) =
      (fun b => FsView.blockOwned (FsBytesGamma.logged dc names) b (image b)) := by
    funext b
    exact (FsBytesGamma.block dc names b (image b)).to_eq.symm
  rw [same]
  exact (phi_map_set_blocks (FsBytesGamma.logged dc names) image home full).symm

theorem fs_home_install_era (names : FsBlocks.Names) (image : Blocks) (home : BlockSet) state pool
    (full : ∀ b, b ∈ home → (image b).length = 1024)
    (shape : Shape state pool) (disjoint : RunsDisjoint (fsRuns state pool))
    (subset : PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) (FsDurBytes.flatten (SnapshotHome.restrict image home))) :
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ⊢
      FsState.footprint (FsBytesGamma.logged dc names) (.own 1) state ∗
      phiMap (FsBytesGamma.logged dc names) (remainder state pool (FsDurBytes.flatten (SnapshotHome.restrict image home))) :=
  (fs_home_blocks_phi_map dc names image home full).mp.trans
    (fs_footprint_install (FsBytesGamma.logged dc names) state pool _ shape disjoint subset)

theorem fs_state_install_era (names : FsBlocks.Names) (image : Blocks) (home : BlockSet) state pool
    (full : ∀ b, b ∈ home → (image b).length = 1024)
    (shape : Shape state pool) (disjoint : RunsDisjoint (fsRuns state pool))
    (subset : PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) (FsDurBytes.flatten (SnapshotHome.restrict image home))) :
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ∗ FsState.ghost (FsBytesGamma.logged dc names) lc state ⊢
      FsState.state (FsBytesGamma.logged dc names) lc (.own 1) state ∗
      phiMap (FsBytesGamma.logged dc names) (remainder state pool (FsDurBytes.flatten (SnapshotHome.restrict image home))) := by
  iintro ⟨Hhome, Hghost⟩
  ihave Hmap := (fs_home_blocks_phi_map dc names image home full).mp $$ Hhome
  iapply fs_state_install (FsBytesGamma.logged dc names) lc state pool _ shape disjoint subset $$ [$Hmap $Hghost]

theorem actual : Spec dc lc where
  homeMap := fs_home_blocks_phi_map dc
  footprint := fs_home_install_era dc
  state := fs_state_install_era dc lc

end MachCSL.Logic.FsDurEraInstall
