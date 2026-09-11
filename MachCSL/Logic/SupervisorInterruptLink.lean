import MachCSL.Logic.SupervisorInterruptProofs

namespace MachCSL.Logic.SupervisorInterrupt
open Iris Iris.BI MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorInterrupt
