import MachCSL.Logic.SupervisorRetirementFactorDefs

namespace MachCSL.Logic.SupervisorRetirement
open MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail _root_.Sail.ConcurrencyInterfaceV1
open _root_.PreSail _root_.Sail.ConcurrencyInterfaceV1.Free

/-- Exact free-tree equality, not merely equality of final register values.
No original `Step` outcome or body branch has been removed. -/
theorem try_step_factor [Platform] (stepNo : Nat) (exitWait : Bool) :
    try_step stepNo exitWait = (do
      setup
      let value ← ((do
        match (← readReg .hart_state) with
        | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
        | .HART_ACTIVE () => run_hart_active stepNo) : SailM _root_.Step)
      postlude value) := rfl

end MachCSL.Logic.SupervisorRetirement
