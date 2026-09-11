import MachCSL.Machine.BootUniversalDefs

namespace MachCSL.Machine.BootUniversal

/-- A successful register-only evaluator run determines every completed
auxiliary Run, even though the general handler also admits other event types. -/
theorem registerRun_unique (bus : Bus Device) (fuel : Nat) (program : SailM α)
    (before after : RegisterFile) (value actual : α) (memory : Memory.ByteMap 64)
    (devices : Device) (state : ViewState Device)
    (success : registerRun fuel program before = some (value, after))
    (run : Run bus program ⟨before, memory, devices⟩ actual state) :
    actual = value ∧ state = ⟨after, memory, devices⟩ := by
  induction fuel generalizing program before with
  | zero => simp [registerRun] at success
  | succ fuel ih =>
    obtain ⟨trace, steps⟩ := run
    cases program with
    | pure result =>
      simp only [registerRun, Option.some.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      cases steps with
      | nil => exact ⟨rfl, rfl⟩
      | cons step _ => cases step
    | impure event k =>
      cases steps with
      | cons first rest =>
        cases first with
        | @event event result k beforeState middle handled =>
          cases event <;> simp only [registerRun] at success
          all_goals first | contradiction | skip
          case readReg r =>
            simp only [sequentialHandler] at handled
            obtain ⟨rfl, rfl⟩ := handled
            exact ih _ _ success ⟨_, rest⟩
          case writeReg r v =>
            simp only [sequentialHandler] at handled
            subst middle
            cases result
            exact ih _ _ success ⟨_, rest⟩

end MachCSL.Machine.BootUniversal
