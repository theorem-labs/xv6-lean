import MachCSL.Logic.SupervisorPteADProofs

namespace MachCSL.Logic.SupervisorPteAD
open Iris MachCSL.Machine LeanPaperStock.Functions

/-- Fully constructed native direct-slot composition; no KPT accessor,
validator callback or successful-response premise remains in this contract. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

/-- The cached no-update path performs no free event at all. -/
theorem cached_program vpn address cached access mxr doSum
    (unchanged : update_PTE_Bits cached access = none) :
    program vpn address cached access mxr doSum = pure (.Ok (none, ())) := by
  rw [program_eq, unchanged]

/-- The actual false response is an internal error, not a retry of the walk. -/
theorem write_false (word : BitVec 64) :
    afterWrite word () (.Ok false) =
      internal_error "sys/vmem.sail" 226 "PTE conditional write failed" := rfl

end MachCSL.Logic.SupervisorPteAD
