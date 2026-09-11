import Xv6.Kernel.KernelDatumDefs

namespace Xv6.Kernel.KernelDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  order_cases : ∀ tier tier', Tier.Le tier tier' →
    tier = tier' ∨ (tier = .identity ∧ tier' = .full)
  pin_mono : ∀ tier tier' ppn va, Tier.Le tier tier' → Pin tier ppn va → Pin tier' ppn va
  pin_identity : ∀ ppn va, Pin .identity ppn va → physical ppn va = va
  pin_intro : ∀ tier ppn va, physical ppn va = va → Pin tier ppn va
  canonical : ∀ va, Positive va → va = (va.extractLsb' 0 39).signExtend 64

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  claim_agree : ∀ era tier tier' va ppn ppn',
    iprop(⊢ claim capacity era tier va ppn -∗ claim capacity era tier' va ppn' -∗ ⌜ppn = ppn'⌝)
  claim_mono : ∀ era tier tier' va ppn, Tier.Le tier tier' →
    iprop(claim capacity era tier va ppn ⊢ claim capacity era tier' va ppn)
  access : ∀ era tier ξ va dq value,
    iprop(byte capacity era tier ξ va dq value ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ physicalByte capacity era ξ (physical ppn va) dq value ∗
      (∀ newValue, physicalByte capacity era ξ (physical ppn va) dq newValue -∗
        byte capacity era tier ξ va dq newValue))
  agree : ∀ era tier tier' ξ ξ' va dq dq' value value',
    iprop(⊢ byte capacity era tier ξ va dq value -∗ byte capacity era tier' ξ' va dq' value' -∗
      ⌜value = value'⌝)
  mono : ∀ era tier tier' ξ va dq value, Tier.Le tier tier' →
    iprop(byte capacity era tier ξ va dq value ⊢ byte capacity era tier' ξ va dq value)
  identity_access : ∀ era ξ va dq value,
    iprop(byte capacity era .identity ξ va dq value ⊢
      physicalByte capacity era ξ va dq value ∗
      (∀ newValue, physicalByte capacity era ξ va dq newValue -∗
        byte capacity era .identity ξ va dq newValue))
  word_mono : ∀ era tier tier' ξ va dq value, Tier.Le tier tier' →
    iprop(word capacity era tier ξ va dq value ⊢ word capacity era tier' ξ va dq value)

end Xv6.Kernel.KernelDatum
