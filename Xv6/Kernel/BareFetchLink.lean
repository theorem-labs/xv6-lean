import Xv6.Kernel.BareFetchProofs
import Xv6.Kernel.MycpuRegimeShellLink
namespace Xv6.Kernel.BareFetch
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity.translation := nativeSpec _
end Xv6.Kernel.BareFetch
