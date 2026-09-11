import Xv6.Kernel.KptFetchHalfProofs

namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptFetchHalf
