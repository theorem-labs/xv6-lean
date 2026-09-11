import Xv6.Kernel.JalSconfProofs
import Xv6.Kernel.BareJalSourceLink
import Xv6.Kernel.KptJalSourceLink

namespace Xv6.Kernel.JalSconf
open Iris MachCSL.Machine MachCSL.Logic

/-- All branch and function dependencies are supplied by their actual native
implementations; only the genuine final continuation remains a WP input. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (BareJalSource.nativeSpec capacity) (KptJalSource.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.JalSconf
