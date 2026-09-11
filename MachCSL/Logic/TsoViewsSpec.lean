import MachCSL.Logic.TsoViewsDefs

/-! Client-facing monotone-view contract, independent of the proof module. -/
namespace MachCSL.Logic.Tso.Views
open MachCSL.Memory Iris Iris.BI

structure ViewsSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  alloc : ∀ (views : Agent → Nat),
    iprop(⊢ |==> ∃ γ, viewAuth capacity γ views)
  update : ∀ γ views views', (∀ h, views h ≤ views' h) →
    iprop(⊢ viewAuth capacity γ views ==∗ viewAuth capacity γ views')
  zero : ∀ γv γll h, iprop(⊢ viewLB capacity γv γll h 0)
  weaken : ∀ γv γll h bound lower, lower ≤ bound →
    iprop(⊢ viewLB capacity γv γll h bound -∗ viewLB capacity γv γll h lower)
  logBound : ∀ γv γll h bound,
    iprop(⊢ viewLB capacity γv γll h bound -∗ llb capacity γll bound)
  valid : ∀ γv γll views h bound,
    iprop(⊢ viewAuth capacity γv views -∗ viewLB capacity γv γll h bound -∗
      ⌜bound ≤ views h⌝)
  get : ∀ γv γll views h n, views h ≤ n →
    iprop(⊢ viewAuth capacity γv views -∗ natAuth capacity γll (.own 1) n -∗
      viewAuth capacity γv views ∗ natAuth capacity γll (.own 1) n ∗
        viewLB capacity γv γll h (views h))
  logValid : ∀ γ dq n bound,
    iprop(⊢ natAuth capacity γ dq n -∗ llb capacity γ bound -∗ ⌜bound ≤ n⌝)

end MachCSL.Logic.Tso.Views
