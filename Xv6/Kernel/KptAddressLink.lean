import Xv6.Kernel.KptAddressProofs

namespace Xv6.Kernel.KptAddress
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

theorem nativeResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : ResourceSpec capacity := resourceSpec capacity

/-- Every component is supplied by its native implementation. Neither
translation-body WPs nor invariant/state restoration are caller premises. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

/-- The stronger named-value postcondition closes directly to the original
source residue, retaining the exact reservation and all actual receipts. -/
theorem resources_close {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) era cpu rs shares N root data address ppn permission rr outcome :
    iprop(resources capacity era cpu rs shares N root data address ppn permission rr outcome ⊢
      auxiliaryCells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root ∗
      KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (afterReservation address rr outcome) ∗ receipts capacity era cpu address outcome) := by
  iintro Hresources
  iunfold resources at Hresources
  icases Hresources with ⟨Haux,Hopened,Hmap,Hresv,Hreceipts⟩
  ihave Hresidue := close_residue capacity era cpu rs N root _ $$ Hopened
  iframe Haux Hresidue Hmap Hresv Hreceipts

theorem registryResourceSpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    ResourceSpec KptOwnership.registryCapacity := nativeResourceSpec KptOwnership.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptAddress
