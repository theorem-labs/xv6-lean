import Xv6.Kernel.Sv39AddressPlan
import Xv6.Kernel.Sv39AddressProofs
import Xv6.Kernel.KptResidueLink

namespace Xv6.Kernel.Sv39Address
open Iris MachCSL.Machine MachCSL.Logic

/-- Actual generated register plans and complete exception classification. -/
theorem nativePureSpec : PureSpec :=
  ⟨unique, mode, satp, rooted, exception, suffix, canonical, noncanonical⟩

/-- The canonical result remains the explicit exact translation-body WP
boundary. No successful translation is inferred by the outer prefix. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity nativePureSpec

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity.machine := nativeSpec KptOwnership.registryCapacity.machine

end Xv6.Kernel.Sv39Address
