import Xv6.Kernel.HardwareConfigProofs

namespace Xv6.Kernel.HardwareConfig
open Iris

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.HardwareConfig
