import MachCSL.Logic.SupervisorRead4Proofs

namespace MachCSL.Logic.SupervisorRead4
open Iris MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorRead4
