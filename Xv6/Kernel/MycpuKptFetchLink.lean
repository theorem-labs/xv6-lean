import Xv6.Kernel.MycpuKptFetchProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.MycpuKptFetch
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registryResourceSpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    ResourceSpec MycpuRegimeShell.registryCapacity := nativeResourceSpec MycpuRegimeShell.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec MycpuRegimeShell.registryCapacity

end Xv6.Kernel.MycpuKptFetch
