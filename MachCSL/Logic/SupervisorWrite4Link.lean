import MachCSL.Logic.SupervisorWrite4Proofs

namespace MachCSL.Logic.SupervisorWrite4
open Iris MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorWrite4
