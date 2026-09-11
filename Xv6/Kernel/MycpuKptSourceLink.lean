import Xv6.Kernel.MycpuKptSourceProofs
import Xv6.Kernel.MycpuKptLink

namespace Xv6.Kernel.MycpuKptSource
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : ResourceSpec capacity := resourceSpec capacity

/-- Both original source tiers are preserved by the actual native KPT
function. Every implementation dependency is discharged here. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (MycpuKpt.nativeSpec capacity) MycpuKpt.nativePureSpec

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuKptSource
