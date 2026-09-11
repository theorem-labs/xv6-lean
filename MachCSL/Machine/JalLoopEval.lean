import MachCSL.Machine.RegisterRun
import MachCSL.Machine.FetchRun
import MachCSL.Sail.Registers

/-! Compositional finite register-event executions for the clock/dispatch slice.
The trace relation is the existing free-event semantics, and its bridge below
retains every actual register read and write as a NodeStep. -/
namespace MachCSL.Machine.JalLoop
open _root_.Sail.ConcurrencyInterfaceV1.Free

abbrev RegisterExec (program : SailM α) (before : RegisterFile) (value : α)
    (after : RegisterFile) : Prop :=
  ∃ trace, Sail.Execution.Steps (Sail.Registers.handler (RegisterType := RegisterType) (ue := exception))
    (program, before) trace (.pure value, after)

theorem registerExec_pure (value : α) (before after : RegisterFile) :
    RegisterExec (.pure value) before value after ↔ after = before := by
  simp [RegisterExec, Sail.Execution.steps_pure_iff, Prod.mk.injEq]

theorem registerExec_bind (program : SailM α) (next : α → SailM β)
    (before after : RegisterFile) (value : β) :
    RegisterExec (program >>= next) before value after ↔
      ∃ middleValue middle, RegisterExec program before middleValue middle ∧
        RegisterExec (next middleValue) middle value after := by
  simp only [RegisterExec, Sail.Execution.completes_bind_iff]
  constructor
  · rintro ⟨trace, result, middle, left, right, _, hl, hr⟩
    exact ⟨result, middle, ⟨left, hl⟩, ⟨right, hr⟩⟩
  · rintro ⟨result, middle, ⟨left, hl⟩, ⟨right, hr⟩⟩
    exact ⟨left ++ right, result, middle, left, right, rfl, hl, hr⟩

theorem RegisterExec.bind {program : SailM α} {next : α → SailM β}
    {before middle after : RegisterFile} {a : α} {b : β}
    (first : RegisterExec program before a middle)
    (second : RegisterExec (next a) middle b after) :
    RegisterExec (program >>= next) before b after :=
  (registerExec_bind _ _ _ _ _).mpr ⟨a, middle, first, second⟩

theorem registerExec_read (before : RegisterFile) (r : Register) :
    RegisterExec (PreSail.readReg r) before (before r) before :=
  ⟨_, .cons (Sail.Registers.read_step before r _) (.nil _)⟩

theorem registerExec_write (before : RegisterFile) (r : Register) (value : RegisterType r) :
    RegisterExec (PreSail.writeReg r value) before () (Sail.Registers.write before r value) :=
  ⟨_, .cons (Sail.Registers.write_step before r value _) (.nil _)⟩

/-- The evaluator's register-only success has the same event trace semantics. -/
theorem registerRun_exec (fuel : Nat) (program : SailM α) (before after : RegisterFile)
    (value : α) (success : registerRun fuel program before = some (value, after)) :
    RegisterExec program before value after := by
  induction fuel generalizing program before with
  | zero => simp [registerRun] at success
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [registerRun, Option.some.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨[], .nil _⟩
    | impure event k =>
      cases event <;> simp only [registerRun] at success
      all_goals first | contradiction | skip
      case readReg r =>
        obtain ⟨trace, rest⟩ := ih _ before success
        exact ⟨_ :: trace, .cons (.event ⟨rfl, rfl⟩) rest⟩
      case writeReg r v =>
        obtain ⟨trace, rest⟩ := ih _ (Sail.Registers.write before r v) success
        exact ⟨_ :: trace, .cons (.event rfl) rest⟩

/-- Register-only event traces embed into the concurrent node relation without
changing shared state or dropping read events. -/
theorem registerSteps_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent) (image : Memory.ByteMap 64)
    (state : LocalState Device) (before after : RegisterFile) (program next : SailM Unit)
    (trace : List (Sail.Execution.Observation RegisterType exception))
    (steps : Sail.Execution.Steps (Sail.Registers.handler (RegisterType := RegisterType) (ue := exception))
      (program, before) trace (next, after)) :
    NodeSteps bus others hart image program { state with registers := before }
      next { state with registers := after } := by
  induction trace generalizing before program with
  | nil => cases steps; exact .nil _ _
  | cons label trace ih =>
    cases steps with
    | cons first rest =>
      cases first with
      | @event event result continuation before middle handled =>
        cases event <;> simp only [Sail.Registers.handler] at handled
        all_goals first | contradiction | skip
        case readReg r =>
          obtain ⟨rfl, rfl⟩ := handled
          exact .cons (read_register_step bus others hart image _ r continuation)
            (ih _ _ rest)
        case writeReg r value =>
          subst middle
          cases result
          exact .cons (write_register_step bus others hart image _ r value continuation)
            (ih _ _ rest)

theorem registerExec_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent) (image : Memory.ByteMap 64)
    (state : LocalState Device) (program : SailM Unit) (after : RegisterFile)
    (run : RegisterExec program state.registers () after) :
    NodeSteps bus others hart image program state (.pure ()) { state with registers := after } := by
  obtain ⟨trace, steps⟩ := run
  have result := registerSteps_nodeSteps bus others hart image state state.registers after
    program (.pure ()) trace steps
  simpa using result

end MachCSL.Machine.JalLoop
