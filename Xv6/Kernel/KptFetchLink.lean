import Xv6.Kernel.KptFetchProofs
import Xv6.Kernel.KptFetchHalfLink

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- All actual generated instruction-fetch calls are proved internally. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registryResourceSpec : ResourceSpec KptOwnership.registryCapacity :=
  nativeResourceSpec KptOwnership.registryCapacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptFetch
