import MachCSL.Logic.IcacheRefLedgerDefs

namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.BI
variable {GF : BundledGFunctors}

structure Spec (capacity : Capacity GF) : Prop where
  claimAgree : ∀ g i c r f rc ty t q,
    iprop(link_auth capacity g i c r f rc ∗ iclaim capacity g i ty t q ⊢ ⌜c = claimCell ty t q⌝)
  freezeAgree : ∀ g i c r f rc phase,
    iprop(link_auth capacity g i c r f rc ∗ ifreeze capacity g phase i ⊢ ⌜f = freezeCell phase⌝)
  freezeExclusive : ∀ g i p p', iprop(ifreeze capacity g p i ∗ ifreeze capacity g p' i ⊢ False)
  claimMint : ∀ g i r f rc ty t q,
    iprop(link_auth capacity g i none r f rc ⊢ |==>
      (link_auth capacity g i (claimCell ty t q) r f rc ∗ iclaim capacity g i ty t q))
  claimSpend : ∀ g i c r f rc ty t q,
    iprop(link_auth capacity g i c r f rc ∗ iclaim capacity g i ty t q ⊢ |==> link_auth capacity g i none r f rc)
  refMint : ∀ g b i c r f rc,
    iprop(link_auth capacity g i c r f rc ⊢ |==>
      (link_auth capacity g i c (rup b r) f (rcup b rc) ∗ runit capacity g b i))
  refSpend : ∀ g b i c r f rc,
    iprop(link_auth capacity g i c (rup b r) f (rcup b rc) ∗ runit capacity g b i ⊢ |==> link_auth capacity g i c r f rc)
  freezeStep : ∀ g i c r ph ph' rc,
    iprop(link_auth capacity g i c r (freezeCell ph) rc ∗ ifreeze capacity g ph i ⊢ |==>
      (link_auth capacity g i c r (freezeCell ph') rc ∗ ifreeze capacity g ph' i))
  boot : ∀ g inums, bootOwned capacity g inums ⊢ bootRows capacity g inums
  allocate : ∀ inums (frame : IProp GF), iprop(frame ⊢ |==> ∃ g, bootRows capacity g inums ∗ frame)

end MachCSL.Logic.IcacheRefLedger
