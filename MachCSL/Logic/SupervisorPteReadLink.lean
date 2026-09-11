import MachCSL.Logic.SupervisorPteReadProofs

namespace MachCSL.Logic.SupervisorPteRead
open Iris MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorPteRead
