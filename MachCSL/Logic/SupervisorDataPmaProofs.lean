import MachCSL.Logic.SupervisorDataPmaSpec
import MachCSL.Machine.SupervisorPhysicalPlan

namespace MachCSL.Logic.SupervisorDataPma
open Iris MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs : RegisterFile} {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs := .read member (.pure ⟨rfl, rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem except_bind {fp : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : RegisterPlan.Returns fp rs program.run (.ok a) rs)
    (second : RegisterPlan.Returns fp rs (next a).run b rs) :
    RegisterPlan.Returns fp rs (program >>= next).run b rs := returns_bind first second

/-- Actual ordinary data PMA grant, with the non-conditional assertion retained. -/
theorem check {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ fp) (kind : Kind) (address : BitVec 64) (n : Nat) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : Grant kind (override_PMA region.attributes .PBMT_PMA))
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    RegisterPlan.Returns fp rs (program kind address n)
      (.Ok SupervisorPhysical.alignedInfo) rs := by
  unfold program pmaCheck _root_.Sail.SailME.run PreSail.PreSailME.run
  refine returns_bind (value := Except.ok (.Ok SupervisorPhysical.alignedInfo)) ?_ (pure_plan fp rs _)
  refine except_bind (a := override_PMA region.attributes .PBMT_PMA) ?_ ?_
  · refine except_bind (lift_except (read_plan rs .pma_regions dq member) _) ?_
    rw [matched]
    exact pure_plan fp rs _
  cases kind <;> simp only [Grant, access] at *
  all_goals
    refine except_bind (a := true) ?_ ?_
    · rw [grant]
      exact pure_plan fp rs _
    · simp only [LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine except_bind (lift_except (value := .Ok (.CannotSplit, 0)) ?_ _) ?_
      · unfold mag_pma_check is_mag_applicable_access
        refine returns_bind (pure_plan fp rs _) ?_
        simp only [aligned, Bool.true_or, ↓reduceIte]
        exact pure_plan fp rs _
      · exact pure_plan fp rs _

/-- The successful priority wrapper performs PMA before the later loop's PMP. -/
theorem priority_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ fp) (kind : Kind) (address : BitVec 64) (n : Nat) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : Grant kind (override_PMA region.attributes .PBMT_PMA))
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    RegisterPlan.Returns fp rs
      (priority kind address n)
      (.Ok SupervisorPhysical.alignedInfo) rs := by
  unfold priority check_pma_with_pmp_priority
  exact returns_bind (check rs dq member kind address n region matched grant aligned) (pure_plan fp rs _)

end MachCSL.Logic.SupervisorDataPma
