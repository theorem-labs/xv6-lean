import Xv6.Kernel.KernelDatumWordDefs

namespace Xv6.Kernel.KernelDatumWord
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open KernelDatum

structure PureSpec : Prop where
  page_window : ∀ va, TsoContextWord.Aligned va → va.toNat % 4096 + 8 ≤ 4096
  vpn_offset : ∀ va j, TsoContextWord.Aligned va → j < 8 →
    vpn (addressAdd va j) = vpn va
  physical_offset : ∀ va ppn j, TsoContextWord.Aligned va → j < 8 →
    physical ppn (addressAdd va j) = addressAdd (physical ppn va) j
  physical_aligned : ∀ va ppn, TsoContextWord.Aligned va → TsoContextWord.Aligned (physical ppn va)

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  access : ∀ era tier ξ va dq value,
    iprop(KernelDatum.word capacity era tier ξ va dq value ⊢ ∃ ppn,
      claims capacity era tier va ppn ∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq value ∗
      (∀ newValue, TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq newValue -∗
        KernelDatum.word capacity era tier ξ va dq newValue))
  close : ∀ era tier ξ va dq value ppn, TsoContextWord.Aligned va →
    iprop(⊢ claims capacity era tier va ppn -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq value -∗
      KernelDatum.word capacity era tier ξ va dq value)
  head : ∀ era tier va ppn,
    iprop(claims capacity era tier va ppn ⊢ claim capacity era tier va ppn)

end Xv6.Kernel.KernelDatumWord
