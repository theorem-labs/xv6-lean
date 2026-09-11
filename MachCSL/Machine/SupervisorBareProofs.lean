import MachCSL.Machine.SupervisorBareDefs

namespace MachCSL.Machine.SupervisorBare
open LeanPaperStock.Functions

/-- These cases introduce no register reads, including arbitrary AMOSWAP annotations. -/
theorem not_shadow (access : MemoryAccessType mem_payload) (supported : Supported access) :
    is_shadow_stack_access access = (pure false : SailM Bool) := by
  cases supported <;> rfl

theorem effective_supervisor (rs : RegisterFile) (access : MemoryAccessType mem_payload)
    (effective : Effective rs access) :
    effectivePrivilege access (rs .mstatus) .Supervisor = (pure .Supervisor : SailM Privilege) := by
  rcases effective with rfl | clear
  · rfl
  · unfold effectivePrivilege
    rw [clear]
    simp only [show ((0#1) == (1#1)) = false from rfl, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]

theorem architecture_rv64 : architecture_bits_backwards 2#2 = (pure .RV64 : SailM Architecture) := rfl

theorem satp_bare : satpMode_of_bits .RV64 0#4 = some .Bare := rfl

theorem footprint_unique (shares : Shares) :
    MachCSL.Logic.RegisterFootprint.Unique (footprint shares) := by
  simp [MachCSL.Logic.RegisterFootprint.Unique, footprint]

end MachCSL.Machine.SupervisorBare
