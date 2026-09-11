import Xv6.Kernel.MycpuBareSourceProofs
import Xv6.Kernel.MycpuOffLink

namespace Xv6.Kernel.MycpuBareSource
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

theorem nativeResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : ResourceSpec capacity := resourceSpec capacity

/-- The complete existing Bare function supplies the sole implementation
dependency; no component or per-cycle WP premise remains. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity (MycpuOff.nativeSpec (bareCapacity capacity))

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuBareSource
