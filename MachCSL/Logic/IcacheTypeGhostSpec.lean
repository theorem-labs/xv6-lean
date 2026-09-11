import MachCSL.Logic.IcacheTypeGhostDefs

namespace MachCSL.Logic.IcacheTypeGhost
open Iris Iris.BI
variable {GF : BundledGFunctors}

structure Spec (capacity : Capacity GF) : Prop where
  shoot : ∀ g ty, iprop(ity_pending capacity g ⊢ |==> ity_shot capacity g ty)
  agree : ∀ g ty ty', iprop(ity_shot capacity g ty ∗ ity_shot capacity g ty' ⊢ ⌜ty = ty'⌝)
  pendingExclusive : ∀ g, iprop(ity_pending capacity g ∗ ity_pending capacity g ⊢ False)
  pendingShotExclusive : ∀ g ty, iprop(ity_pending capacity g ∗ ity_shot capacity g ty ⊢ False)
  sealBoot : ∀ g, iprop(ireg_boot capacity g ⊢ |==> ireg_open capacity g)
  regimeBootExclusive : ∀ g rg, iprop(ireg_regime capacity g rg ∗ ireg_boot capacity g ⊢ False)
  allocate : ∀ (frame : IProp GF), iprop(frame ⊢ |==> ∃ g, ity_pending capacity g ∗ frame)

end MachCSL.Logic.IcacheTypeGhost
