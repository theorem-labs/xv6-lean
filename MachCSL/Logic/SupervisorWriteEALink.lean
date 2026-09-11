import MachCSL.Logic.SupervisorWriteEAProofs

namespace MachCSL.Logic.SupervisorWriteEA
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorWriteEA
