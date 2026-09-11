import Xv6.Kernel.MycpuBareProofs

namespace Xv6.Kernel.MycpuBare
open Iris MachCSL.Logic LeanPaperStock.Functions

/-- Both function contracts discharge every native component specification. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.MycpuBare
