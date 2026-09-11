import Xv6.Kernel.KptADProofs

namespace Xv6.Kernel.KptAD
open Iris MachCSL.Machine MachCSL.Logic

/-- Constructed shared-KPT A/D rules. Every register prefix and memory
boundary is discharged by native rules; the only WP argument is the final
continuation, guarded by the number of actual memory events. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptAD
