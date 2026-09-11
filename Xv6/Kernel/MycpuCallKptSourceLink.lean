import Xv6.Kernel.MycpuCallKptSourceProofs
import Xv6.Kernel.KptJalSourceLink

namespace Xv6.Kernel.MycpuCallKptSource
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

/-- Actual JAL and the complete source function discharge all internal
execution dependencies, retaining only the genuine final continuation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (KptJalSource.nativeSpec capacity) (KptJal.nativeResourceSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuCallKptSource
