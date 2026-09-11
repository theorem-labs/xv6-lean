import MachCSL.Logic.SupervisorBareFetchProofs

namespace MachCSL.Logic.SupervisorBareFetch
open Iris MachCSL.Machine LeanPaperStock.Functions

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorBareFetch
