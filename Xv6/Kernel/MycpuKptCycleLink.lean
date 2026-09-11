import Xv6.Kernel.MycpuKptCycleProofs
import Xv6.Kernel.MycpuKptBodyLink

namespace Xv6.Kernel.MycpuKptCycle
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec := pureSpec

/-- Actual component implementations discharge every internal interface.
Only the genuine guarded returned-cycle continuation remains in Spec. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (MycpuKptBody.nativeSpec capacity)

abbrev registryCapacity := MycpuRegimeShell.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec registryCapacity := nativeSpec registryCapacity

end Xv6.Kernel.MycpuKptCycle
