import Xv6.Kernel.PushOffScalarProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.PushOffScalar
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.PushOffScalar
