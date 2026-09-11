import Xv6.Kernel.KernelMapStaticProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KernelMapStatic
open Iris

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelMapStatic
