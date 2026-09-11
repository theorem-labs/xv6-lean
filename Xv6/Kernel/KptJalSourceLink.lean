import Xv6.Kernel.KptJalSourceProofs
import Xv6.Kernel.KptJalLink

namespace Xv6.Kernel.KptJalSource
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

/-- The actual native JAL cycle supplies the private implementation
parameter. No component WP or selected execution is assumed by callers. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity (KptJal.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.KptJalSource
