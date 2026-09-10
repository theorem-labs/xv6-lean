import MachCSL.Machine.Node

/-! The source's auxiliary sequential `run` relation, using finite free-event
executions. It is used to state the reset witness, not to collapse CPU steps.
The actual CPU relation remains the sub-instruction `NodeStep`. -/
namespace MachCSL.Machine

open Memory
open _root_.Sail.ConcurrencyInterfaceV1.Free

structure ViewState (Device : Type) where
  registers : RegisterFile
  memory : ByteMap 64
  devices : Device

def sequentialHandler (bus : Bus Device) :
    Sail.Execution.Handler RegisterType exception (ViewState Device) :=
  fun event s result s' => match event with
    | .readReg r => result = s.registers r ∧ s' = s
    | .writeReg r v => s' = { s with registers := Sail.Registers.write s.registers r v }
    | .readMem n req =>
      if deviceAddress req.pa then
        ∃ w d, bus.read s.devices req.pa n = some (w, d) ∧
          result = .Ok (w, none) ∧ s' = { s with devices := d }
      else ∃ w, (∀ j, j < n → s.memory (addressAdd req.pa j) = some (nthByte w j)) ∧
          result = .Ok (w, none) ∧ s' = s
    | .writeMem n req => match req.value with
      | none => False
      | some v =>
        if deviceAddress req.pa then
          ∃ d, bus.write s.devices req.pa n v = some d ∧
            result = .Ok none ∧ s' = { s with devices := d }
        else result = .Ok none ∧ s' = { s with memory := writeBytes s.memory req.pa n v }
    | .getCycleCount => result = (0 : Nat) ∧ s' = s
    | .error _ | .discard => False
    | _ => s' = s

def Run (bus : Bus Device) (program : SailM α) (s : ViewState Device)
    (value : α) (s' : ViewState Device) : Prop :=
  ∃ trace, Sail.Execution.Steps (sequentialHandler bus) (program, s) trace (.pure value, s')

theorem run_pure (bus : Bus Device) (value : α) (s s' : ViewState Device) :
    Run bus (.pure value) s value s' ↔ s' = s := by
  simp [Run, Sail.Execution.steps_pure_iff, Prod.mk.injEq]

theorem run_bind (bus : Bus Device) (program : SailM α) (next : α → SailM β)
    (s s' : ViewState Device) (value : β) :
    Run bus (program >>= next) s value s' ↔
      ∃ intermediate middle, Run bus program s intermediate middle ∧
        Run bus (next intermediate) middle value s' := by
  simp only [Run, Sail.Execution.completes_bind_iff]
  constructor
  · rintro ⟨trace, result, middle, before, after, _, left, right⟩
    exact ⟨result, middle, ⟨before, left⟩, ⟨after, right⟩⟩
  · rintro ⟨result, middle, ⟨before, left⟩, ⟨after, right⟩⟩
    exact ⟨before ++ after, result, middle, before, after, rfl, left, right⟩

end MachCSL.Machine
