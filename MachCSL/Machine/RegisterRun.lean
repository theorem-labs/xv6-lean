import MachCSL.Machine.Run

/-! A total, fuel-bounded register-only evaluator and its soundness theorem
for the auxiliary sequential relation. Unsupported events return `none`;
the evaluator is a proof tool, never the concurrent machine semantics. -/
namespace MachCSL.Machine

def registerRun {α : Type} : Nat → SailM α → RegisterFile → Option (α × RegisterFile)
  | 0, _, _ => none
  | _ + 1, .pure value, registers => some (value, registers)
  | fuel + 1, .impure event k, registers => match event with
    | .readReg r => registerRun fuel (k (registers r)) registers
    | .writeReg r value => registerRun fuel (k ()) (Sail.Registers.write registers r value)
    | _ => none

theorem registerRun_sound (bus : Bus Device) (fuel : Nat) (program : SailM α)
    (registers registers' : RegisterFile) (value : α) (memory : Memory.ByteMap 64)
    (devices : Device) (h : registerRun fuel program registers = some (value, registers')) :
    Run bus program ⟨registers, memory, devices⟩ value ⟨registers', memory, devices⟩ := by
  induction fuel generalizing program registers with
  | zero => simp [registerRun] at h
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [registerRun, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨[], .nil _⟩
    | impure event k =>
      cases event <;> simp only [registerRun] at h
      all_goals first | solve | contradiction
                      | skip
      case readReg r =>
        obtain ⟨trace, rest⟩ := ih _ registers h
        exact ⟨_ :: trace, .cons (.event ⟨rfl, rfl⟩) rest⟩
      case writeReg r v =>
        obtain ⟨trace, rest⟩ := ih _ (Sail.Registers.write registers r v) h
        exact ⟨_ :: trace, .cons (.event rfl) rest⟩

end MachCSL.Machine
