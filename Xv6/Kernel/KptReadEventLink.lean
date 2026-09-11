import Xv6.Kernel.KptReadEventProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KptReadEvent
open Iris MachCSL.Machine MachCSL.Logic

/-- No caller-supplied slot accessor, invariant restoration or read result
remains in the native shared event rule. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity (KptOwnership.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptReadEvent
