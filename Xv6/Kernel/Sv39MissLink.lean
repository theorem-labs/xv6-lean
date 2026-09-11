import Xv6.Kernel.Sv39MissProofs

namespace Xv6.Kernel.Sv39Miss
open Iris MachCSL.Logic MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.Sv39Miss
