import Xv6.Kernel.PushOffStackProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.PushOffStack
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec := pureSpec

theorem nativeResourceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : ResourceSpec capacity :=
  resourceSpec capacity

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.PushOffStack
