import MachCSL.Machine.SpinlockFamilyScalar

namespace MachCSL.Machine.SpinlockFamily
open Logic.SpinlockProtocol

theorem select_completed {cpu rs phase} (h : Ready cpu ⟨2, by decide⟩ rs phase) :
    Completed cpu (SpinlockControl.branchAfter false rs) phase := by
  obtain ⟨idle, value⟩ := h.operands.stage
  by_cases participant : cpu.val < 2
  · have branch : SpinlockControl.branchAfter false rs = rs := by
      simp [SpinlockControl.branchAfter, value, participant]
    rw [branch]
    exact ⟨h.core, ⟨(⟨3, by decide⟩ : Fin 17),
      ⟨fun _ _ => participant, by simp, by simp, by exact idle⟩, ready_next h (by decide)⟩⟩
  · have branch : SpinlockControl.branchAfter false rs =
        Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨16, by decide⟩) := by
      simp [SpinlockControl.branchAfter, value, participant]
    rw [branch]
    exact ⟨SpinlockCore.write h.core _ trivial, ⟨(⟨16, by decide⟩ : Fin 17),
      ⟨by simp, by simp, by simp, idle, by omega⟩, rfl⟩⟩

theorem retry_completed {cpu rs phase} (h : Ready cpu ⟨9, by decide⟩ rs phase) :
    Completed cpu (SpinlockControl.branchAfter true rs) phase := by
  rcases h.operands.stage with ⟨idle, value⟩ | ⟨B, v, t, held, value⟩
  · have branch : SpinlockControl.branchAfter true rs =
        Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨6, by decide⟩) := by
      simp [SpinlockControl.branchAfter, value]
    rw [branch]
    exact ⟨SpinlockCore.write h.core _ trivial, ⟨(⟨6, by decide⟩ : Fin 17),
      ⟨fun _ _ => h.operands.participant (by decide) (by decide),
        fun _ _ => h.operands.base (by decide) (by decide),
        fun _ _ => h.operands.one (by decide) (by decide), by exact idle⟩, rfl⟩⟩
  · have branch : SpinlockControl.branchAfter true rs = rs := by
      simp [SpinlockControl.branchAfter, value]
    rw [branch]
    exact ⟨h.core, ⟨(⟨10, by decide⟩ : Fin 17),
      ⟨fun _ _ => h.operands.participant (by decide) (by decide),
        fun _ _ => h.operands.base (by decide) (by decide),
        fun _ _ => h.operands.one (by decide) (by decide), by exact ⟨B, v, t, held⟩⟩,
      ready_next h (by decide)⟩⟩

theorem loop_completed {cpu rs phase} (h : Ready cpu ⟨15, by decide⟩ rs phase) :
    Completed cpu (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨6, by decide⟩)) phase := by
  exact ⟨SpinlockCore.write h.core _ trivial, ⟨(⟨6, by decide⟩ : Fin 17),
    ⟨fun _ _ => h.operands.participant (by decide) (by decide),
      fun _ _ => h.operands.base (by decide) (by decide),
      fun _ _ => h.operands.one (by decide) (by decide), by exact h.operands.stage⟩, rfl⟩⟩

theorem park_completed {cpu rs phase} (h : Ready cpu ⟨16, by decide⟩ rs phase) :
    Completed cpu (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨16, by decide⟩)) phase := by
  exact ⟨SpinlockCore.write h.core _ trivial, ⟨(⟨16, by decide⟩ : Fin 17),
    operands_write h.operands .nextPC _ (by simp [OperandRegister]), rfl⟩⟩

end MachCSL.Machine.SpinlockFamily
