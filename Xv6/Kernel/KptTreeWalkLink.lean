import Xv6.Kernel.KptTreeWalkProofs

namespace Xv6.Kernel.KptTreeWalk
open Iris MachCSL.Machine MachCSL.Logic

/-- The native implementation discharges every register factor and shared
memory event internally. The only WP premise is the real continuation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptTreeWalk
