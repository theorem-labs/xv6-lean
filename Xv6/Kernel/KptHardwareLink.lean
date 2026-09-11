import Xv6.Kernel.KptHardwareProofs

namespace Xv6.Kernel.KptHardware
open Iris MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptHardware
