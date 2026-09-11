import MachCSL.Logic.TimerCapProofs

namespace MachCSL.Logic.TimerCap
open Iris

theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.TimerCap
