import Xv6.Kernel.Sv39WalkProofs

namespace Xv6.Kernel.Sv39Walk
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem nativePureSpec : PureSpec := pureSpec

/-- Full direct-slot three-level walk; shared KPT and TLB integration are
separate contracts and are not assumed by this implementation. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.Sv39Walk
