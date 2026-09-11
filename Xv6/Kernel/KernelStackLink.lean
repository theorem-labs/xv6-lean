import Xv6.Kernel.KernelStackProofs

namespace Xv6.Kernel.KernelStack
open Iris

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelStack
