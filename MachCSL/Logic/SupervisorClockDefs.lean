import MachCSL.Logic.RegisterPlanDefs

/-! Value-agnostic clock footprint, from `HartMCycle.v:556–590,693–715`.
All generated read-result branches remain present, including Sstc. -/
namespace MachCSL.Logic.SupervisorClock
open Iris Iris.BI MachCSL.Machine

/-- The only registers written by the actual clock subprogram. -/
def clockRegisters : List Register := [.mcycle, .mtime, .mip]

/-- A relation on symbolic footprint files, not an assertion about unowned
physical registers. The execution plan changes only these three fields. -/
def OffClock (before after : RegisterFile) : Prop :=
  ∀ r, r ∉ clockRegisters → after r = before r

abbrev Framed (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (program : SailM α) :=
  RegisterPlan.Plan fp rs program (fun _ after => OffClock rs after)

def clockFootprint : RegisterFootprint.Footprint :=
  [(.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1)]

/-- Source `clock_res`: three full cells with existential values, no invariant. -/
def clockRes {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (γ : GName) : IProp GF :=
  iprop(∃ rs : RegisterFile, RegisterFootprint.cells capacity γ rs clockFootprint)

end MachCSL.Logic.SupervisorClock
