import Xv6.Kernel.KptTranslateProofs
import Xv6.Kernel.KptHitLink
import Xv6.Kernel.KptMissLink

namespace Xv6.Kernel.KptTranslate
open Iris MachCSL.Logic

theorem nativePureSpec : PureSpec := ⟨program_factor, lookup_mapped, lookup_plan⟩

/-- Closed native implementation: both dispatch arms use their complete
shared-invariant implementations, with no caller-supplied event callback. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (KptHit.nativeSpec capacity) (KptMiss.nativeSpec capacity)

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KptTranslate
