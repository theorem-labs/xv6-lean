import Xv6.Kernel.BootTextPmaMapProofs

namespace Xv6.Kernel.BootTextPmaMap
open Iris MachCSL.Logic

/-- Actual map/era/text allocation and actual full-cell persistence, with
all component premises discharged by their existing native implementations. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  produce := produce capacity
  allocate := allocate capacity
  allocate_frame := allocate_frame capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.BootTextPmaMap
