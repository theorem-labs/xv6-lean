import MachCSL.Logic.FsDurInstallSpec
import MachCSL.Logic.FsBytesGammaDefs
import Xv6.Fs.SnapshotHomeDefs

namespace MachCSL.Logic.FsDurEraInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns FsDurXferShape FsDurInstall
variable {GF : BundledGFunctors}

structure Spec (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) : Prop where
  homeMap : ∀ (names : FsBlocks.Names) (image : Blocks) (home : BlockSet),
    (∀ b, b ∈ home → (image b).length = 1024) →
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ⊣⊢
      phiMap (FsBytesGamma.logged dc names) (FsDurBytes.flatten (SnapshotHome.restrict image home))
  footprint : ∀ (names : FsBlocks.Names) (image : Blocks) (home : BlockSet) state pool,
    (∀ b, b ∈ home → (image b).length = 1024) →
    Shape state pool → RunsDisjoint (fsRuns state pool) →
    PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) (FsDurBytes.flatten (SnapshotHome.restrict image home)) →
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ⊢
      FsState.footprint (FsBytesGamma.logged dc names) (.own 1) state ∗
      phiMap (FsBytesGamma.logged dc names) (remainder state pool (FsDurBytes.flatten (SnapshotHome.restrict image home)))
  state : ∀ (names : FsBlocks.Names) (image : Blocks) (home : BlockSet) state pool,
    (∀ b, b ∈ home → (image b).length = 1024) →
    Shape state pool → RunsDisjoint (fsRuns state pool) →
    PartialMap.submap (M := Disk.ImageMap) (runUnion (fsRuns state pool)) (FsDurBytes.flatten (SnapshotHome.restrict image home)) →
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) home ∗ FsState.ghost (FsBytesGamma.logged dc names) lc state ⊢
      FsState.state (FsBytesGamma.logged dc names) lc (.own 1) state ∗
      phiMap (FsBytesGamma.logged dc names) (remainder state pool (FsDurBytes.flatten (SnapshotHome.restrict image home)))

end MachCSL.Logic.FsDurEraInstall
