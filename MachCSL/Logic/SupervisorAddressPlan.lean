import MachCSL.Logic.SupervisorAddressDefs
import MachCSL.Machine.SupervisorBarePlan

namespace MachCSL.Logic.SupervisorAddress
open Iris MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

theorem mode_plan (shares : Shares) (rs : RegisterFile) (mode : SATPMode)
    (sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2)
    (decoded : satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (rs .satp))) = some mode) :
    RegisterPlan.Returns (footprint shares) rs (translationMode .Supervisor) mode rs := by
  unfold translationMode
  refine returns_bind (SupervisorBare.architecture_plan rs shares.status (by simp [footprint]) sxl) ?_
  refine returns_bind (value := _get_Satp64_Mode (Mk_Satp64 (rs .satp))) ?_ ?_
  · refine returns_bind (pure_plan (footprint shares) rs ()) ?_
    exact returns_bind (read_plan rs .satp shares.satp (by simp [footprint])) (pure_plan (footprint shares) rs _)
  · rw [decoded]
    exact pure_plan (footprint shares) rs _

theorem applicable_plan (shares : Shares) (rs : RegisterFile) (kind : Kind)
    (mxr : _get_Mstatus_MXR (rs .mstatus) = 0#1) :
    RegisterPlan.Returns (footprint shares) rs (is_pmm_applicable (access kind) .Supervisor) true rs := by
  unfold is_pmm_applicable
  refine returns_bind (read_plan rs .mstatus shares.status (by simp [footprint])) ?_
  rw [mxr]
  cases kind <;> exact pure_plan (footprint shares) rs _

theorem pmlen_plan (shares : Shares) (rs : RegisterFile) (kind : Kind)
    (mxr : _get_Mstatus_MXR (rs .mstatus) = 0#1)
    (disabled : pmm_mode_backwards (_get_MEnvcfg_PMM (rs .menvcfg)) = .PMM_Disabled) :
    RegisterPlan.Returns (footprint shares) rs (get_pmlen (access kind) .Supervisor) 0 rs := by
  unfold get_pmlen
  refine returns_bind (applicable_plan shares rs kind mxr) ?_
  refine returns_bind (value := PointerMaskingMode.PMM_Disabled) ?_ ?_
  · unfold get_pmm
    refine returns_bind (read_plan rs .menvcfg shares.envcfg (by simp [footprint])) ?_
    rw [disabled]
    exact pure_plan (footprint shares) rs _
  · exact pure_plan (footprint shares) rs _

theorem physical_zero (address : BitVec 64) : pm_transform_PA (.Virtaddr address) 0 = .Virtaddr address := by
  change virtaddr.Virtaddr (BitVec.zeroExtend 64 (BitVec.extractLsb 63 0 address)) = .Virtaddr address
  simp [BitVec.extractLsb, BitVec.extractLsb']

theorem virtual_zero (address : BitVec 64) : pm_transform_VA (.Virtaddr address) 0 = .Virtaddr address := by
  change virtaddr.Virtaddr (BitVec.signExtend 64 (BitVec.extractLsb 63 0 address)) = .Virtaddr address
  simp [BitVec.extractLsb, BitVec.extractLsb']

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

theorem program_plan (shares : Shares) (rs : RegisterFile) (mode : SATPMode)
    (config : Config rs mode) (address : BitVec 64) (kind : Kind) :
    RegisterPlan.Returns (footprint shares) rs (program address kind) (.Virtaddr address) rs := by
  unfold program transform_effective_address
  refine returns_bind (read_plan rs .mstatus shares.status (by simp [footprint])) ?_
  refine returns_bind (read_plan rs .cur_privilege shares.privilege (by simp [footprint])) ?_
  rw [config.privilege, SupervisorBare.effective_supervisor rs (access kind) (Or.inr config.mprv)]
  refine returns_bind (pure_plan (footprint shares) rs Privilege.Supervisor) ?_
  refine returns_bind (pmlen_plan shares rs kind config.mxr config.pmm) ?_
  refine returns_bind (mode_plan shares rs mode config.sxl config.decoded) ?_
  simp only [Int.toNat_zero]
  split
  · rw [physical_zero]
    exact pure_plan (footprint shares) rs _
  · rw [virtual_zero]
    exact pure_plan (footprint shares) rs _

end MachCSL.Logic.SupervisorAddress
