import Xv6.Kernel.KernelDatumWord4Defs

namespace Xv6.Kernel.KernelDatumWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open KernelDatum

structure PureSpec : Prop where
  page_window : ∀ va, Aligned va → va.toNat % 4096 + 4 ≤ 4096
  vpn_offset : ∀ va j, Aligned va → j < 4 →
    vpn (addressAdd va j) = vpn va
  physical_offset : ∀ va ppn j, Aligned va → j < 4 →
    physical ppn (addressAdd va j) = addressAdd (physical ppn va) j
  physical_aligned : ∀ va ppn, Aligned va → Aligned (physical ppn va)

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  access : ∀ era tier ξ va dq value,
    iprop(word capacity era tier ξ va dq value ⊢ ∃ ppn,
      claims capacity era tier va ppn ∗
      physicalWord capacity era ξ (physical ppn va) dq value ∗
      (∀ newValue, physicalWord capacity era ξ (physical ppn va) dq newValue -∗
        word capacity era tier ξ va dq newValue))
  close : ∀ era tier ξ va dq value ppn, Aligned va →
    iprop(⊢ claims capacity era tier va ppn -∗
      physicalWord capacity era ξ (physical ppn va) dq value -∗
      word capacity era tier ξ va dq value)
  head : ∀ era tier va ppn,
    iprop(claims capacity era tier va ppn ⊢ claim capacity era tier va ppn)

end Xv6.Kernel.KernelDatumWord4
