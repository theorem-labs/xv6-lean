import MachCSL.Logic.SupervisorMemOuter4Spec
import MachCSL.Logic.SupervisorMemOuterPlan
import MachCSL.Machine.SupervisorBareProofs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.SupervisorWritePlan

namespace MachCSL.Logic.SupervisorMemOuter4
open Iris MachCSL.Machine LeanPaperStock.Functions

/-- Both callback arms are the actual pure callbacks; no error result is removed. -/
theorem read_meta_eq (access : MemoryAccessType mem_payload) (priv : Privilege)
    (address : BitVec 64) (n : Nat) :
    mem_read_priv_meta access .PBMT_PMA priv (.Physaddr address) n false false false false =
      checked_mem_read access .PBMT_PMA priv (.Physaddr address) n false false false false := by
  unfold mem_read_priv_meta
  change (_ >>= Pure.pure) = _
  exact EventPlan.sail_bind_pure_eq _

theorem read_factor (address : BitVec 64) :
    readProgram address = (effective (.Load .Data) >>= fun priv =>
      mem_read_priv (.Load .Data) .PBMT_PMA priv (.Physaddr address) 4 false false false) := rfl

theorem read_supervisor (address : BitVec 64) :
    mem_read_priv (.Load .Data) .PBMT_PMA .Supervisor (.Physaddr address) 4 false false false =
      (SupervisorRead4.program address >>= fun result => pure (MemoryOpResult_drop_meta result)) := by
  unfold mem_read_priv
  rw [read_meta_eq]
  rfl

theorem write_factor (address : BitVec 64) (word : BitVec 32) :
    writeProgram address word = (effective (.Store .Data) >>= fun priv =>
      mem_write_value_priv_meta (.Physaddr address) 4 word (.Store .Data)
        .PBMT_PMA priv () false false false) := rfl


theorem write_supervisor (address : BitVec 64) (word : BitVec 32) :
    mem_write_value_priv_meta (.Physaddr address) 4 word (.Store .Data) .PBMT_PMA .Supervisor () false false false =
      SupervisorWrite4.program address word := by
  unfold mem_write_value_priv_meta
  change (_ >>= Pure.pure) = _
  exact EventPlan.sail_bind_pure_eq _

theorem nativePureSpec : PureSpec := ⟨read_factor,read_supervisor,write_factor,write_supervisor⟩

end MachCSL.Logic.SupervisorMemOuter4
