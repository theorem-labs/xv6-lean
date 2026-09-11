import Xv6.Kernel.KptMemoryProofs

namespace Xv6.Kernel.KptMemory
open Iris MachCSL.Machine MachCSL.Logic

/-- Actual shared translation, context forwarding, physical permission and
reservation rules are all supplied by their native implementations. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptMemory
