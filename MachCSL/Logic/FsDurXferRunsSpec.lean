import MachCSL.Logic.FsDurXferRunsDefs

namespace MachCSL.Logic.FsDurXferRuns
open Iris Iris.Std Iris.BI Iris.CMRA
variable {GF : BundledGFunctors}

structure RunSpec (view : FsView.View GF) : Prop where
  disjoint : ∀ runs, FsView.PhiExcl view → phiRuns view runs ⊢ ⌜RunsDisjoint runs⌝
  union : ∀ runs, RunsDisjoint runs → phiRuns view runs ⊣⊢ phiMap view (runUnion runs)
  included : ∀ authority bytes runs, PhiAgree view authority bytes → RunsDisjoint runs →
    authority ∗ phiRuns view runs ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) (runUnion runs) bytes⌝
  mixedDisjoint : ∀ runs, FsView.PhiExcl view → SharesOK runs → phiRunsQ view runs ⊢ ⌜RunsDisjoint (strip runs)⌝
  mixedIncluded : ∀ authority bytes runs, PhiAgree view authority bytes →
    authority ∗ phiRunsQ view runs ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) (runUnion (strip runs)) bytes⌝

end MachCSL.Logic.FsDurXferRuns
