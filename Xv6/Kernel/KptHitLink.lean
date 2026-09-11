import Xv6.Kernel.KptHitProofs
import Xv6.Kernel.KptADLink

namespace Xv6.Kernel.KptHit
open Iris MachCSL.Logic

/-- Full shared hit composition with every A/D, event and register rule
supplied by its native implementation. No memory-remainder WP is an input. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity (KptAD.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptHit
