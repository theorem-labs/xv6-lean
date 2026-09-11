import Xv6.Kernel.KptWriteEventProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KptWriteEvent
open Iris MachCSL.Machine MachCSL.Logic

/-- Both resource and event rules use constructed native ownership laws;
no client-supplied slot, update, restoration, or successful response remains. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity (KptOwnership.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptWriteEvent
