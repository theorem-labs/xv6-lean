import MachCSL.Logic.IcacheRefLedgerProofs

namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.Std Iris.CMRA Iris.BI
open scoped CommMonoidLike
variable {GF : BundledGFunctors} (capacity : Capacity GF) (g : GName)

theorem link_mint_claim i r f rc ty t q : iprop(link_auth capacity g i none r f rc ⊢ |==>
    (link_auth capacity g i (claimCell ty t q) r f rc ∗ iclaim capacity g i ty t q)) := by
  unfold link_auth iclaim
  apply link_update_alloc capacity g
  apply lelemc_local_update
  · exact LocalUpdate.alloc_option none (show ✓ (Excl.excl (⟨(ty, t, q)⟩ : DiscreteO ClaimValue)) by trivial)
  · exact .id _
  · exact .id _

theorem link_spend_claim i c r f rc ty t q : iprop(link_auth capacity g i c r f rc ∗ iclaim capacity g i ty t q ⊢
    |==> link_auth capacity g i none r f rc) := by
  have update : (lelemc c r f rc, lelem (claimCell ty t q) 0) ~l~> (lelemc none r f rc, lelem none 0) := by
    apply lelemc_local_update
    · exact LocalUpdate.delete_option c (Excl.excl (⟨(ty, t, q)⟩ : DiscreteO ClaimValue))
    · exact .id _
    · exact .id _
  unfold link_auth iclaim
  iintro H
  imod link_update capacity g i _ _ _ _ update $$ H with ⟨Ha, _⟩
  imodintro
  iexact Ha

theorem link_mint_ref i c r f rc : iprop(link_auth capacity g i c r f rc ⊢ |==>
    (link_auth capacity g i c (r + 1) f rc ∗ runit_plain capacity g i)) := by
  unfold link_auth runit_plain
  apply link_update_alloc capacity g
  apply lelemc_local_update
  · exact .id _
  · apply CommMonoidLike.leftCancelAdd_local_update
    apply NatAdd.ext
    change r + 1 = (r + 1) + 0
    omega
  · exact .id _

theorem link_spend_ref i c r f rc : iprop(link_auth capacity g i c (r + 1) f rc ∗ runit_plain capacity g i ⊢
    |==> link_auth capacity g i c r f rc) := by
  have update : (lelemc c (r + 1) f rc, lelem none 1) ~l~> (lelemc c r f rc, lelem none 0) := by
    apply lelemc_local_update
    · exact .id _
    · apply CommMonoidLike.leftCancelAdd_local_update
      apply NatAdd.ext
      change (r + 1) + 0 = r + 1
      omega
    · exact .id _
  unfold link_auth runit_plain
  iintro H
  imod link_update capacity g i _ _ _ _ update $$ H with ⟨Ha, _⟩
  imodintro
  iexact Ha

theorem link_mint_refc i c r f rc : iprop(link_auth capacity g i c r f rc ⊢ |==>
    (link_auth capacity g i c r f (rc + 1) ∗ runit_claim capacity g i)) := by
  unfold link_auth runit_claim
  apply link_update_alloc capacity g
  apply lelemc_local_update
  · exact .id _
  · exact .id _
  · apply CommMonoidLike.leftCancelAdd_local_update
    apply NatAdd.ext
    change rc + 1 = (rc + 1) + 0
    omega

theorem link_spend_refc i c r f rc : iprop(link_auth capacity g i c r f (rc + 1) ∗ runit_claim capacity g i ⊢
    |==> link_auth capacity g i c r f rc) := by
  have update : (lelemc c r f (rc + 1), lelemc none 0 none 1) ~l~> (lelemc c r f rc, lelem none 0) := by
    apply lelemc_local_update
    · exact .id _
    · exact .id _
    · apply CommMonoidLike.leftCancelAdd_local_update
      apply NatAdd.ext
      change (rc + 1) + 0 = rc + 1
      omega
  unfold link_auth runit_claim
  iintro H
  imod link_update capacity g i _ _ _ _ update $$ H with ⟨Ha, _⟩
  imodintro
  iexact Ha

theorem link_mint_runit b i c r f rc : iprop(link_auth capacity g i c r f rc ⊢ |==>
    (link_auth capacity g i c (rup b r) f (rcup b rc) ∗ runit capacity g b i)) := by
  cases b
  · exact link_mint_ref capacity g i c r f rc
  · exact link_mint_refc capacity g i c r f rc

theorem link_spend_runit b i c r f rc : iprop(link_auth capacity g i c (rup b r) f (rcup b rc) ∗ runit capacity g b i ⊢
    |==> link_auth capacity g i c r f rc) := by
  cases b
  · exact link_spend_ref capacity g i c r f rc
  · exact link_spend_refc capacity g i c r f rc

theorem link_freeze_step i c r ph ph' rc : iprop(link_auth capacity g i c r (freezeCell ph) rc ∗ ifreeze capacity g ph i ⊢ |==>
    (link_auth capacity g i c r (freezeCell ph') rc ∗ ifreeze capacity g ph' i)) := by
  unfold link_auth ifreeze
  apply link_update capacity g
  apply LocalUpdate.prod'
  · apply LocalUpdate.prod'
    · exact .id _
    · apply LocalUpdate.option
      exact LocalUpdate.exclusive (show ✓ (Excl.excl (⟨ph'⟩ : DiscreteO Freeze)) by trivial)
  · exact .id _

end MachCSL.Logic.IcacheRefLedger
