import MachCSL.Logic.SupervisorClockProofs

namespace MachCSL.Logic.SupervisorClock
open Iris MachCSL.Machine

/-- Existing machine register ownership supplies every clock cell; no new camera. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorClock
