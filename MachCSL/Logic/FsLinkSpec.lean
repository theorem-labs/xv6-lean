import MachCSL.Logic.FsLinkDefs

namespace MachCSL.Logic.FsLink
open Iris Iris.Std Iris.CMRA Iris.BI

structure FsLinkSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  zeroRetype : ∀ γ i ty ty', iprop(auth capacity γ i 0 ty ⊣⊢ auth capacity γ i 0 ty')
  split : ∀ γ i (left right : Pile),
    iprop(toks capacity γ i (left ⊎ right) ⊣⊢ toks capacity γ i left ∗ toks capacity γ i right)
  valid : ∀ γ i n ty pile, iprop(⊢ auth capacity γ i n ty -∗ toks capacity γ i pile -∗
    ⌜pile ⊆ reps n ty⌝)
  agree : ∀ γ i n ty ty', iprop(⊢ auth capacity γ i n ty -∗ tok capacity γ i ty' -∗
    ⌜ty' = ty ∧ 1 ≤ n⌝)
  mint : ∀ γ i n k ty, iprop(⊢ auth capacity γ i n ty ==∗
    auth capacity γ i (n + k) ty ∗ toks capacity γ i (reps k ty))
  giveBack : ∀ γ i n k ty ty', iprop(⊢ auth capacity γ i (n + k) ty -∗
    toks capacity γ i (reps k ty') ==∗ auth capacity γ i n ty)
  allocate : ∀ family : FamilyRA, ✓ family →
    iprop(⊢ |==> ∃ γ, iOwn (E := capacity.link) γ family)

end MachCSL.Logic.FsLink
