import Xv6.Kernel.KptExclusiveEventProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KptExclusiveEvent
open Iris MachCSL.Machine MachCSL.Logic

/-- All ownership, current-heap and native exclusive-event dependencies are
proved at the supplied capacity. No physical-read callback remains. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (KptOwnership.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptExclusiveEvent
