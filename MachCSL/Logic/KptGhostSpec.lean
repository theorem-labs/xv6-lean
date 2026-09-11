import MachCSL.Logic.KptGhostDefs

namespace MachCSL.Logic.KptGhost
open Iris Iris.Std Iris.BI

/-- Native algebra contracts, deliberately separate from physical ownership,
publication, per-event invariant opening and translation correctness. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  mapLookup : ∀ γ M vpn ppn pc, iprop(mapAuth capacity γ M ∗ mapAt capacity γ vpn ppn pc ⊢
    ⌜M[vpn]? = some (ppn, pc)⌝)
  mapAgree : ∀ γ vpn p p' pc pc', iprop(mapAt capacity γ vpn p pc ∗ mapAt capacity γ vpn p' pc' ⊢
    ⌜p = p' ∧ pc = pc'⌝)
  mapInsert : ∀ γ M vpn ppn pc, M[vpn]? = none →
    iprop(mapAuth capacity γ M ⊢ |==>
      (mapAuth capacity γ (M.insert vpn (ppn, pc)) ∗ mapAt capacity γ vpn ppn pc))
  allocateMap : ∀ M (frame : IProp GF), iprop(frame ⊢ |==> ∃ γ,
    mapAuth capacity γ M ∗ allClaims capacity γ M ∗ frame)
  claimLookup : ∀ γ M vpn ppn pc, M[vpn]? = some (ppn, pc) →
    iprop(allClaims capacity γ M ⊢ mapAt capacity γ vpn ppn pc)
  shoot : ∀ γ t, iprop(unset capacity γ ⊢ |==> snapshot capacity γ t)
  agree : ∀ γ t t', iprop(snapshot capacity γ t ∗ snapshot capacity γ t' ⊢
    ⌜Xv6.Kernel.PtTree.canon t = Xv6.Kernel.PtTree.canon t'⌝)
  canonical : ∀ γ t t', Xv6.Kernel.PtTree.canon t = Xv6.Kernel.PtTree.canon t' →
    iprop(snapshot capacity γ t ⊢ snapshot capacity γ t')
  unsetExclusive : ∀ γ, iprop(unset capacity γ ∗ unset capacity γ ⊢ False)
  unsetSnapshotExclusive : ∀ γ t, iprop(unset capacity γ ∗ snapshot capacity γ t ⊢ False)
  allocateUnset : ∀ (frame : IProp GF), iprop(frame ⊢ |==> ∃ γ, unset capacity γ ∗ frame)
  shootBound : ∀ γ logName B, iprop(Tso.Views.llb capacity.views logName B ∗ boundUnset capacity γ ⊢
    |==> bound capacity γ logName B)
  boundLog : ∀ γ logName B, iprop(bound capacity γ logName B ⊢ Tso.Views.llb capacity.views logName B)
  boundAgree : ∀ γ logName logName' B B',
    iprop(bound capacity γ logName B ∗ bound capacity γ logName' B' ⊢ ⌜B = B'⌝)
  boundUnsetExclusive : ∀ γ, iprop(boundUnset capacity γ ∗ boundUnset capacity γ ⊢ False)
  boundUnsetShotExclusive : ∀ γ logName B,
    iprop(boundUnset capacity γ ∗ bound capacity γ logName B ⊢ False)
  allocateBoundUnset : ∀ (frame : IProp GF), iprop(frame ⊢ |==> ∃ γ, boundUnset capacity γ ∗ frame)
  allocate : ∀ logName M (frame : IProp GF), iprop(frame ⊢ |==> ∃ names,
    ⌜names.logLength = logName⌝ ∗ initial capacity names M ∗ frame)

end MachCSL.Logic.KptGhost
