import Xv6.Kernel.MycpuKptMemoryProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.MycpuKptMemory
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

/-- Reuses the existing source supervisor-bit, machine and KPT capacities. -/
abbrev registryCapacity := MycpuRegimeShell.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec registryCapacity := nativeSpec registryCapacity

end Xv6.Kernel.MycpuKptMemory
