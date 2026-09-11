import Xv6.Kernel.KptResidueProofs

namespace Xv6.Kernel.KptResidue
open Iris MachCSL.Logic

/-- All resource laws are implemented by the existing native register,
PMP, snapshot and invariant cameras, without an additional authority. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptResidue
