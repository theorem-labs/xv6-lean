import Xv6.Kernel.MycpuMemoryProofs

namespace Xv6.Kernel.MycpuMemory
open Iris MachCSL.Logic LeanPaperStock.Functions

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.MycpuMemory
