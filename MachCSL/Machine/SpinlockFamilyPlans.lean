import MachCSL.Machine.SpinlockFamilyAccess
import MachCSL.Machine.SpinlockCycleProofs

namespace MachCSL.Machine.SpinlockFamily
open Logic Logic.SpinlockProtocol Logic.EventPlan LeanPaperStock.Functions
variable [Platform]

omit [Platform] in
private theorem from_register {A : Type} {reads : EventWP.ReadAllowed} {cpu rs rr phase}
    {program : SailM A} {value after}
    (plan : EventWP.Returns reads rs program value after) (good : Completed cpu after phase) :
    Plan reads relations rs rr phase program
      (fun result after _ next => result = value ∧ Completed cpu after next) := by
  apply (of_returns plan).mono
  rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, good⟩

private theorem scalar_instruction (reads : EventWP.ReadAllowed) {cpu rs phase} (j : Fin 7)
    (h : Ready cpu (SpinlockScalar.index j) rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction (SpinlockScalar.index j)))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) :=
  from_register (SpinlockScalar.execute_plan reads j rs) (scalar_completed j h)

/-- Every actual decoded instruction, with all protocol-selected memory results
and both control-flow outcomes. The phase and register family are postconditions,
not additional premises on machine events. -/
theorem instruction_plan (reads : EventWP.ReadAllowed) (i : Fin 17) {cpu rs phase}
    (h : Ready cpu i rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction i))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact from_register (SpinlockControl.csr_plan reads rs h.core.privilege) (csr_completed h)
  · exact scalar_instruction reads ⟨0, by decide⟩ h rr
  · exact from_register (SpinlockControl.select_branch_plan reads rs h.pc h.core.misa) (select_completed h)
  · exact scalar_instruction reads ⟨1, by decide⟩ h rr
  · exact scalar_instruction reads ⟨2, by decide⟩ h rr
  · exact scalar_instruction reads ⟨3, by decide⟩ h rr
  · exact scalar_instruction reads ⟨4, by decide⟩ h rr
  · exact amo_plan reads h rr
  · exact scalar_instruction reads ⟨5, by decide⟩ h rr
  · exact from_register (SpinlockControl.retry_branch_plan reads rs h.pc h.core.misa) (retry_completed h)
  · exact load_plan reads h rr
  · exact scalar_instruction reads ⟨6, by decide⟩ h rr
  · exact store_plan reads h rr
  · exact fence_plan reads h rr
  · exact unlock_plan reads h rr
  · exact from_register (SpinlockControl.loop_jump_plan reads rs h.pc h.core.misa) (loop_completed h)
  · exact from_register (SpinlockControl.park_jump_plan reads rs h.pc h.core.misa) (park_completed h)

/-- Actual fetch/decode/execute/retire/clock cycle preserves the seventeen-way
boundary family. Both tick choices and arbitrary architectural counters are covered. -/
theorem cycle_plan (i : Fin 17) {cpu rs phase} (h : Family cpu i rs phase)
    (rr : Option Reservation) (tick : Bool) :
    Plan (SpinlockFetch.CodeRead i) relations rs rr phase (cycle tick)
      (fun _ after _ next => ∃ j, Family cpu j after next) := by
  refine (SpinlockCycle.cycle_plan i relations rs rr phase tick
    (SpinlockCore.atInstruction h.core i h.pc h.nextPC) h.core.off
    (fun after _ next => Completed cpu after next) ?_).mono ?_
  · apply (instruction_plan (SpinlockFetch.CodeRead i) i (ready h) rr).mono
    rintro result after rr' next ⟨retired, good⟩
    exact ⟨retired, good.core.hartState, good.core.menvcfg, good⟩
  · rintro _ _ _ _ ⟨completed, good, rfl⟩
    exact finish good tick

end MachCSL.Machine.SpinlockFamily
