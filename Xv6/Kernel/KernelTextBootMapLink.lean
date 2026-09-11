import Xv6.Kernel.KernelTextBootMapProofs

namespace Xv6.Kernel.KernelTextBootMap
open Iris

/-- The name-installing boot-text producer is fully backed by the native
static-map and machine-era allocators, with the real identity-text bridge. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  allocate := allocate capacity
  allocate_frame := allocate_frame capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.KernelTextBootMap
