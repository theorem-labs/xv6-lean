import MachCSL.Logic.ReservationDefs

/-! Client contract; imports definitions independently of its implementation. -/
namespace MachCSL.Logic.Reservations
open Iris Iris.BI MachCSL.Machine

structure ReservationSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  alloc : ∀ f, iprop(⊢ |==> ∃ γ, resvAuth capacity γ f ∗ allFragments capacity γ f)
  cellAccess : ∀ γ f cpu,
    iprop(⊢ allFragments capacity γ f -∗ resvFrag capacity γ cpu (f cpu) ∗
      (resvFrag capacity γ cpu (f cpu) -∗ allFragments capacity γ f))
  anyIntro : ∀ γ cpu value, iprop(⊢ resvFrag capacity γ cpu value -∗ resvAny capacity γ cpu)
  agree : ∀ γ f cpu value,
    iprop(⊢ resvAuth capacity γ f -∗ resvFrag capacity γ cpu value -∗ ⌜f cpu = value⌝)
  update : ∀ γ f cpu value value',
    iprop(⊢ resvAuth capacity γ f -∗ resvFrag capacity γ cpu value ==∗
      resvAuth capacity γ (updateHart f cpu value') ∗ resvFrag capacity γ cpu value')
  preserve : ∀ γ f cpu value, f cpu = value →
    iprop(resvAuth capacity γ f ⊣⊢ resvAuth capacity γ (updateHart f cpu value))

end MachCSL.Logic.Reservations
