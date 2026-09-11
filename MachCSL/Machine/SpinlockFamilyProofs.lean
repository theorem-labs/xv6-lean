import MachCSL.Machine.SpinlockFamilyDefs

namespace MachCSL.Machine.SpinlockFamily
open Logic.SpinlockProtocol

/-- Only these six general-purpose cells occur in the operand predicate. -/
def OperandRegister : Register → Prop
  | .x5 | .x6 | .x10 | .x14 | .x15 | .x16 => True
  | _ => False

theorem operands_congr {cpu i rs phase} (h : Operands cpu i rs phase) (after : RegisterFile)
    (same : ∀ r, OperandRegister r → after r = rs r) : Operands cpu i after phase := by
  refine ⟨h.participant, ?_, ?_, ?_⟩
  · intro lo hi; exact (same .x10 trivial).trans (h.base lo hi)
  · intro lo hi; exact (same .x14 trivial).trans (h.one lo hi)
  · have ha := h.stage
    unfold At at ha ⊢
    simp only [same .x5 trivial, same .x6 trivial, same .x10 trivial,
      same .x15 trivial, same .x16 trivial]
    exact ha

theorem operands_write {cpu i rs phase} (h : Operands cpu i rs phase)
    (r : Register) (value : RegisterType r) (outside : ¬ OperandRegister r) :
    Operands cpu i (Sail.Registers.write rs r value) phase := by
  apply operands_congr h
  intro s inside
  have different : s ≠ r := by rintro rfl; exact outside inside
  exact Sail.Registers.write_other rs r s value (Ne.symm different)

theorem boot (g : State) (facts : BootFacts SpinlockImage.image g) (cpu : CPU) :
    Family cpu ⟨0, by decide⟩ (g.registers cpu) .idle := by
  have static := BootUniversal.bootFacts_static SpinlockImage.image g facts cpu
  exact ⟨SpinlockCore.boot _ g facts cpu,
    ⟨by simp, by simp, by simp, rfl⟩, static.pc, static.nextPC⟩

theorem ready {cpu i rs phase} (h : Family cpu i rs phase) :
    Ready cpu i (SpinlockCycle.prepare (JalLoopPlan.enableAfter rs)) phase := by
  exact ⟨SpinlockCore.prepare (SpinlockCore.enable h.core),
    operands_write (operands_write h.operands .minstret_increment _ (by simp [OperandRegister])) .nextPC _ (by simp [OperandRegister]),
    h.pc, rfl⟩

theorem finish_operands {cpu i rs phase} (h : Operands cpu i rs phase) (tick : Bool) :
    Operands cpu i (SpinlockCycle.finish tick rs) phase := by
  apply operands_congr h
  intro r inside
  cases r <;> simp only [OperandRegister] at inside
  all_goals first | contradiction | skip
  all_goals
    unfold SpinlockCycle.finish SpinlockCycle.retire SpinlockCycle.tickPC
      JalLoopPlan.clockAfter JalLoopPlan.timeAfter JalLoopPlan.counterAfter JalLoop.clintAfter
    split <;> split <;> first | rfl | (split <;> rfl)

theorem finish {cpu rs phase} (h : Completed cpu rs phase) (tick : Bool) :
    ∃ i, Family cpu i (SpinlockCycle.finish tick rs) phase := by
  obtain ⟨i, operands, next⟩ := h.next
  exact ⟨i, SpinlockCore.finish h.core tick, finish_operands operands tick,
    (SpinlockCore.finish_pc tick rs).trans next,
    (SpinlockCore.finish_nextPC tick rs).trans next⟩

theorem pin {cpu i rs phase} (h : Family cpu i rs phase) (r : Register)
    (isPin : Logic.EventWP.IsPin r) (value : RegisterType r) :
    Family cpu i (Sail.Registers.write rs r value) phase := by
  rcases isPin with rfl | rfl
  all_goals exact ⟨SpinlockCore.write h.core value trivial,
    operands_write h.operands _ value (by simp [OperandRegister]), h.pc, h.nextPC⟩

/-- Both actual PLIC pin-update arms preserve each hart's indexed family. -/
theorem plic (devices : Devices.State) (before after : CPU → RegisterFile)
    (index : CPU → Fin 17) (phase : CPU → Phase)
    (families : ∀ cpu, Family cpu (index cpu) (before cpu) (phase cpu))
    (step : PlicStep devices before after) :
    ∀ cpu, Family cpu (index cpu) (after cpu) (phase cpu) := by
  cases step with
  | supervisor selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact pin (families selected) .sig_seip (Or.inl rfl) _
    · simpa only [updateHart, if_neg same] using families cpu
  | machine selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact pin (families selected) .sig_meip (Or.inr rfl) _
    · simpa only [updateHart, if_neg same] using families cpu

end MachCSL.Machine.SpinlockFamily
