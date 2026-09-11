import Xv6.Kernel.KptSharedProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.KptShared
open Iris MachCSL.Logic

/-- Every ownership, ghost and invariant dependency is discharged by its
native implementation, at the same machine and view capacities. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (KptOwnership.nativeSpec capacity)

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptShared
