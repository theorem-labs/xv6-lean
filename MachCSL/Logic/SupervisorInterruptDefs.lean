import MachCSL.Machine.SupervisorInterruptDefs
import MachCSL.Logic.RegisterPlanDefs

namespace MachCSL.Logic.SupervisorInterrupt
open Iris Iris.BI MachCSL.Machine

structure Shares where
  misa : DFrac
  status : DFrac
  enable : DFrac
  delegation : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.misa, shares.misa), (.mstatus, shares.status),
   (.mie, shares.enable), (.mideleg, shares.delegation)]

abbrev Returns (shares : Shares) (rs : RegisterFile) (program : SailM α)
    (value : α) (after : RegisterFile) : Prop :=
  RegisterPlan.Returns (footprint shares) rs program value after

/-- Only the four source register facts needed for dispatch suppression.
The surrounding SIE ghost, privilege and translation resources can frame. -/
def registers {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (γ : GName) (shares : Shares) : IProp GF :=
  iprop(∃ rs : RegisterFile, ⌜Machine.SupervisorInterrupt.Disabled rs⌝ ∗
    RegisterFootprint.cells capacity γ rs (footprint shares))

end MachCSL.Logic.SupervisorInterrupt
