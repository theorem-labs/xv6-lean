import MachCSL.Logic.LockDefs

namespace MachCSL.Logic.Lock
open Iris Iris.Std Iris.CMRA Iris.BI

structure LockSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  agree : ∀ γ state state' position position',
    iprop(⊢ authAt capacity γ state position -∗ fragAt capacity γ state' position' -∗
      ⌜state = state' ∧ position = position'⌝)
  exclusive : ∀ γ state state' position position',
    iprop(⊢ fragAt capacity γ state position -∗ fragAt capacity γ state' position' -∗ False)
  update : ∀ γ state state' position position',
    iprop(⊢ authAt capacity γ state position -∗ fragAt capacity γ state position ==∗
      authAt capacity γ state' position' ∗ fragAt capacity γ state' position')
  allocate : ∀ state position, iprop(⊢ |==> ∃ γ,
    authAt capacity γ state position ∗ fragAt capacity γ state position)

end MachCSL.Logic.Lock
