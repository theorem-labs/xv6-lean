import MachCSL.Logic.SupervisorBareReadProofs

namespace MachCSL.Logic.SupervisorBareRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open SupervisorRead

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorBareRead
