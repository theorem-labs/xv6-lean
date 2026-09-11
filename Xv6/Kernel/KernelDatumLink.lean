import Xv6.Kernel.KernelDatumProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KernelDatum
open Iris MachCSL.Logic

theorem nativePureSpec : PureSpec :=
  ⟨order_cases,pin_mono,pin_identity,pin_intro,canonical⟩

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelDatum
