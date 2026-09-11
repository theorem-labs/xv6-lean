import MachCSL.Logic.FsDurInstallLink
import MachCSL.Logic.FsStateLinkSpec

namespace MachCSL.Logic.FsDurXfer
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState FsDurXferRuns FsDurXferShape
variable {GF : BundledGFunctors}

/-- Source §4a': a pure, native allocation helper. Runtime clients must derive
its Shape and disjointness inputs from their source resources. This is not
an initial-image constructor and does not take Snapshot.OK. -/
structure MintSpec (dc : Disk.Capacity GF) : Prop where
  footprint : ∀ state pool gl gt, Shape state pool → RunsDisjoint (fsRuns state pool) →
    iprop(⊢ |==> ∃ g, Disk.mapAuth dc g (runUnion (fsRuns state pool)) ∗
      FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state)

structure ByteSpec (dc : Disk.Capacity GF) : Prop where
  transfer : ∀ (view : FsView.View GF), FsView.PhiExcl view → ∀ authority whole,
    PhiAgree view authority whole → ∀ (dq : DFrac) state gl gt, ¬✓ (dq • dq) →
    iprop(authority ∗ FsState.footprint view dq state ⊢ |==> ∃ g bytes,
      ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.footprint view dq state ∗ Disk.mapAuth dc g bytes ∗
      FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state)

structure StateSpec (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF) : Prop where
  transfer : ∀ (view : FsView.View GF), FsView.PhiExcl view → ∀ authority whole,
    PhiAgree view authority whole → ∀ (q : Qp) state, (1 : Qp).half < q →
    iprop(authority ∗ FsState.state view lc (.own q) state ⊢ |==> ∃ g gl gt bytes,
      ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.state view lc (.own q) state ∗ Disk.mapAuth dc g bytes ∗
      FsTop.auth tc gt state.inodes ∗ FsTop.allFragments tc gt state.inodes ∗
      FsState.state (FsView.snapGamma dc g gl gt) lc (.own 1) state)
  transferToken : ∀ (view : FsView.View GF), FsView.PhiExcl view → ∀ authority whole,
    PhiAgree view authority whole → ∀ (q : Qp) state root ty, (1 : Qp).half < q →
    iprop(authority ∗ FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link root ty ⊢
      |==> ∃ g gl gt bytes, ⌜PartialMap.submap (M := Disk.ImageMap) bytes whole⌝ ∗ authority ∗
      FsState.state view lc (.own q) state ∗ FsLink.tok lc view.link root ty ∗ Disk.mapAuth dc g bytes ∗
      FsTop.auth tc gt state.inodes ∗ FsTop.allFragments tc gt state.inodes ∗
      FsState.state (FsView.snapGamma dc g gl gt) lc (.own 1) state ∗ FsLink.tok lc gl root ty)

end MachCSL.Logic.FsDurXfer
