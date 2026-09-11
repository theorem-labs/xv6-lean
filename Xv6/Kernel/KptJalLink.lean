import Xv6.Kernel.KptJalProofs

namespace Xv6.Kernel.KptJal
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

abbrev registryCapacity := MycpuRegimeShell.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] : Spec registryCapacity :=
  nativeSpec registryCapacity

end Xv6.Kernel.KptJal
