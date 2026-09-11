import MachCSL.Logic.TsoContextBytesWriteWPProofs

namespace MachCSL.Logic.TsoContextBytesWriteWP
open Iris MachCSL.Machine

/-- The native adapter constructs the context payer from actual byte ownership;
no resource callback or successful state correspondence is a caller input. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.TsoContextBytesWriteWP
