import MachCSL.Logic.SupervisorPmpProofs

namespace MachCSL.Logic.SupervisorPmp
open Iris Iris.BI MachCSL.Machine

/-- No new ghost functor: the same machine register capacity supplies both cells. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorPmp
