import Xv6.Kernel.MycpuCallSconfProofs
import Xv6.Kernel.JalSconfLink
import Xv6.Kernel.KptJalResources

namespace Xv6.Kernel.MycpuCallSconf
open Iris MachCSL.Machine MachCSL.Logic

/-- All branch and function dependencies are supplied by their actual native
implementations; only the genuine final continuation remains a WP input. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (JalSconf.nativeSpec capacity) (KptJal.nativeResourceSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuCallSconf
