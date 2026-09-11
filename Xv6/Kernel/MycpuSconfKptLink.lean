import Xv6.Kernel.MycpuSconfKptProofs
import Xv6.Kernel.MycpuKptLink

namespace Xv6.Kernel.MycpuSconfKpt
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

/-- Every component is the actual native implementation. The only remaining
WP premise is the source caller's genuine post-return continuation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (MycpuKpt.nativeSpec capacity) MycpuKpt.nativePureSpec

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuSconfKpt
