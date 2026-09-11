import Xv6.Kernel.MycpuCycleProofs

namespace Xv6.Kernel.MycpuCycle
open Iris MachCSL.Logic LeanPaperStock.Functions

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.MycpuCycle
