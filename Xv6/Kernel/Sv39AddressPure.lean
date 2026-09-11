import Xv6.Kernel.Sv39AddressSpec
import MachCSL.Machine.SupervisorBarePlan

namespace Xv6.Kernel.Sv39Address
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

private theorem bind_returns {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

theorem unique shares : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorBare.footprint]

theorem mode shares rs root (config : Config rs root) :
    RegisterPlan.Returns (footprint shares) rs (translationMode .Supervisor) .Sv39 rs := by
  unfold translationMode
  apply bind_returns (SupervisorBare.architecture_plan rs shares.status (by simp [footprint, SupervisorBare.footprint]) config.sxl)
  apply bind_returns (value := 8#4)
  · apply bind_returns (value := ()) (.pure ⟨rfl,rfl⟩)
    apply RegisterPlan.Plan.read (dq := shares.satp) (by simp [footprint, SupervisorBare.footprint])
    change RegisterPlan.Returns (footprint shares) rs (pure (_get_Satp64_Mode (Mk_Satp64 (rs .satp)))) (8#4) rs
    rw [config.rooted.1]
    exact .pure ⟨rfl,rfl⟩
  · exact .pure ⟨rfl,rfl⟩

theorem satp shares rs :
    RegisterPlan.Returns (footprint shares) rs (get_satp 39) (rs .satp) rs := by
  unfold get_satp
  apply bind_returns (value := ()) (.pure ⟨rfl,rfl⟩)
  exact .read (dq := shares.satp) (by simp [footprint, SupervisorBare.footprint]) (.pure ⟨rfl,rfl⟩)

theorem rooted rs root (config : Config rs root) :
    (satp_to_asid (k_n := 64) (rs .satp)).zeroExtend 16 = 0#16 ∧
    satp_to_ppn (k_n := 64) (rs .satp) = root := config.rooted.2

theorem exception access (supported : Supported access) error :
    translationException access error = pure (fault access error) := by
  cases supported <;> cases error <;> rfl

theorem suffix rs address access (supported : Supported access) response :
    RegisterPlan.Returns [] rs (resume address access response) (resumed address access response) rs := by
  cases response with
  | Ok pair => rcases pair with ⟨ppn,pbmt,ext⟩; exact .pure ⟨rfl,rfl⟩
  | Err pair =>
    rcases pair with ⟨error,ext⟩
    simp only [resume, exception access supported, BootPmp.sail_pure_bind]
    exact .pure ⟨rfl,rfl⟩

end Xv6.Kernel.Sv39Address
