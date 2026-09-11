import MachCSL.Logic.SupervisorMemOuterProofs

namespace MachCSL.Logic.SupervisorMemOuter
open Iris MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorMemOuter
