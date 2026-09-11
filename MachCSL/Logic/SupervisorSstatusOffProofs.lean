import MachCSL.Logic.SupervisorSstatusOffPlan

/-! Concrete ordinary-kernel regression certificates. Saved MPELP/SPELP,
SUM, SPP/SPIE, MIE/MPIE, nonstandard UXL and a reserved high bit are nonzero.
Only MPP varies; invalid encoding 2 exercises the real User fallback. -/
namespace MachCSL.Logic.SupervisorSstatusOff
open Iris MachCSL.Machine LeanPaperStock.Functions

def exampleStatus (mpp : BitVec 2) : BitVec 64 :=
  _update_Mstatus_MPP 0x4020b008401a8#64 mpp

theorem example_fields :
    _get_Mstatus_SPELP (exampleStatus 0#2) = 1#1 ∧
    _get_Mstatus_MPELP (exampleStatus 0#2) = 1#1 ∧
    _get_Mstatus_SPP (exampleStatus 0#2) = 1#1 ∧
    _get_Mstatus_SPIE (exampleStatus 0#2) = 1#1 ∧
    _get_Mstatus_SIE (exampleStatus 0#2) = 0#1 := by decide

theorem example_nominal_facts :
    SupervisorBits.MsFacts (exampleStatus 0#2) ∧
    SupervisorBits.MsFacts (exampleStatus 1#2) ∧
    SupervisorBits.MsFacts (exampleStatus 3#2) := by
  unfold SupervisorBits.MsFacts
  decide

theorem example_all_mpp :
    ([0#2, 1#2, 2#2, 3#2].map fun mpp =>
      legalized (exampleStatus mpp) (exampleStatus mpp)) =
    [exampleStatus 0#2, exampleStatus 1#2, exampleStatus 0#2, exampleStatus 3#2] := by decide

theorem example_invalid_not_nominal :
    SupervisorBits.haveNominalValue (_get_Mstatus_MPP (exampleStatus 2#2)) = false := by decide

/-- Full actual legalizer plans, including invalid MPP, follow the generic
event proof. No executable-evaluator success premise is introduced. -/
theorem example_actual_plans (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (dq : DFrac) (member : (.misa, dq) ∈ fp) (misa : rs .misa = misaValue)
    (mpp : BitVec 2) :
    RegisterPlan.Returns fp rs
      (legalize_mstatus (exampleStatus mpp) (exampleStatus mpp))
      (legalized (exampleStatus mpp) (exampleStatus mpp)) rs :=
  legalize_plan fp rs dq member misa _ _

end MachCSL.Logic.SupervisorSstatusOff
