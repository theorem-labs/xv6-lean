import MachCSL.Logic.ObservationInvariantDefs

namespace MachCSL.Logic.ObservationInvariant
open Iris Iris.BI MachCSL.Machine

structure ObservationInvariantSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : PowerGhost.Capacity GF) : Prop where
  allocate : ∀ N E γ R history,
    iprop(⊢ PowerGhost.obsFrag capacity γ history -∗ R history ={E}=∗ ledger capacity N γ R)
  update : ∀ (N : Namespace) (E : CoPset) γ R, (∀ history, Timeless (R history)) → (↑N : CoPset) ⊆ E →
    ∀ history next (S : IProp GF),
    iprop(⊢ R history -∗ S ={E \ ↑N}=∗ R next ∗ S) →
    iprop(⊢ ledger capacity N γ R -∗ PowerGhost.obsAuth capacity γ history -∗ S ={E}=∗
      PowerGhost.obsAuth capacity γ next ∗ S)
  trivialUpdate : ∀ (N : Namespace) (E : CoPset) γ history next, (↑N : CoPset) ⊆ E →
    iprop(⊢ trivial capacity N γ -∗ PowerGhost.obsAuth capacity γ history ={E}=∗
      PowerGhost.obsAuth capacity γ next)

end MachCSL.Logic.ObservationInvariant
