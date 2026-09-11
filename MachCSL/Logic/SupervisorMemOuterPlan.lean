import MachCSL.Logic.SupervisorMemOuterDefs
import MachCSL.Machine.SupervisorBareProofs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.SupervisorWritePlan

namespace MachCSL.Logic.SupervisorMemOuter
open Iris MachCSL.Machine LeanPaperStock.Functions

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs middle after : RegisterFile} {program : SailM α} {next : α → SailM β}
    {value : α} {result : β} (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

theorem effective_plan (shares : Shares) (rs : RegisterFile)
    (access : MemoryAccessType mem_payload) (priv : rs .cur_privilege = .Supervisor)
    (allowed : SupervisorBare.Effective rs access) :
    RegisterPlan.Returns (footprint shares) rs (effective access) .Supervisor rs := by
  unfold effective
  refine returns_bind (RegisterPlan.Plan.read (dq := shares.status) (by simp [footprint])
    (.pure ⟨rfl, rfl⟩)) ?_
  refine returns_bind (RegisterPlan.Plan.read (dq := shares.privilege) (by simp [footprint])
    (.pure ⟨rfl, rfl⟩)) ?_
  rw [priv, SupervisorBare.effective_supervisor rs access allowed]
  exact .pure ⟨rfl, rfl⟩

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

/-- Both callback arms are the actual pure callbacks; no error result is removed. -/
theorem read_meta_eq (access : MemoryAccessType mem_payload) (priv : Privilege)
    (address : BitVec 64) (n : Nat) :
    mem_read_priv_meta access .PBMT_PMA priv (.Physaddr address) n false false false false =
      checked_mem_read access .PBMT_PMA priv (.Physaddr address) n false false false false := by
  unfold mem_read_priv_meta
  change (_ >>= Pure.pure) = _
  exact EventPlan.sail_bind_pure_eq _

theorem read_factor (kind : SupervisorRead.Kind) (address : BitVec 64) :
    readProgram kind address = (effective (SupervisorRead.access kind) >>= fun priv =>
      mem_read_priv (SupervisorRead.access kind) .PBMT_PMA priv (.Physaddr address) 8 false false false) := rfl

theorem read_supervisor (kind : SupervisorRead.Kind) (address : BitVec 64) :
    mem_read_priv (SupervisorRead.access kind) .PBMT_PMA .Supervisor (.Physaddr address) 8 false false false =
      (SupervisorRead.program kind address >>= fun result => pure (MemoryOpResult_drop_meta result)) := by
  unfold mem_read_priv
  rw [read_meta_eq]
  rfl

theorem write_factor (address word : BitVec 64) :
    writeProgram address word = (effective (.Store .Data) >>= fun priv =>
      mem_write_value_priv_meta (.Physaddr address) 8 word (.Store .Data)
        .PBMT_PMA priv () false false false) := rfl

end MachCSL.Logic.SupervisorMemOuter
