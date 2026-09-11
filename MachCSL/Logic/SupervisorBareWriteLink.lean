import MachCSL.Logic.SupervisorBareWriteProofs

namespace MachCSL.Logic.SupervisorBareWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions TsoContextReadWP

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.SupervisorBareWrite
