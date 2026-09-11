import Xv6.Kernel.MycpuSconfProofs
import Xv6.Kernel.MycpuBareSourceLink
import Xv6.Kernel.MycpuKptSourceLink

namespace Xv6.Kernel.MycpuSconf
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

/-- Both native branch implementations are supplied here. The caller
provides only the unopened source input and actual returned continuation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (MycpuBareSource.nativeSpec capacity) (MycpuKptSource.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuSconf
