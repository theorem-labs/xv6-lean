import Xv6.Kernel.MycpuCallSconfKptPure
import Xv6.Kernel.MycpuCallSconfKptProofs
import Xv6.Kernel.KptJalSconfLink

namespace Xv6.Kernel.MycpuCallSconfKpt
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

/-- Actual JAL and complete native function supply all internal execution
rules. The caller supplies only source resources and its returned continuation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (KptJalSconf.nativeSpec capacity) (KptJal.nativeResourceSpec capacity) pureSpec

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuCallSconfKpt
