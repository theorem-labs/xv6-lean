import MachCSL.Machine.Node
import MachCSL.Memory.ReadBytes

/-!
A fuel-bounded proof evaluator for register events and nonexclusive RAM reads.
Its successes embed into finite sequences of the actual sub-instruction
`NodeStep` relation. Rejected evaluator events do not restrict that relation.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Machine

open _root_.Sail.ConcurrencyInterfaceV1.Free

/-- The RAM map may be the TSO observation at a chosen, fixed reader view. -/
def fetchRun {α : Type} (memory : Memory.ByteMap 64) :
    Nat → SailM α → RegisterFile → Option (α × RegisterFile)
  | 0, _, _ => none
  | _ + 1, .pure value, registers => some (value, registers)
  | fuel + 1, .impure event k, registers => match event with
    | .readReg r => fetchRun memory fuel (k (registers r)) registers
    | .writeReg r value => fetchRun memory fuel (k ()) (Sail.Registers.write registers r value)
    | .readMem n req =>
      if deviceAddress req.pa || accessExclusive req.access_kind then none else
      match Memory.readBytes memory req.pa n with
      | none => none
      | some value => fetchRun memory fuel (k (.Ok (value, none))) registers
    | _ => none

/-- Mapping the returned value does not change events or fuel consumption. -/
theorem fetchRun_bind_pure (memory : Memory.ByteMap 64) (fuel : Nat) (program : SailM α)
    (registers : RegisterFile) (f : α → β) :
    fetchRun memory fuel (program >>= fun a => pure (f a)) registers =
      (fetchRun memory fuel program registers).map (fun (a, rs) => (f a, rs)) := by
  induction fuel generalizing program registers with
  | zero => rfl
  | succ fuel ih =>
    cases program with
    | pure a => rfl
    | impure event k =>
      cases event
      all_goals first | rfl | skip
      case readReg r => exact ih (k (registers r)) registers
      case writeReg r v => exact ih (k ()) (Sail.Registers.write registers r v)
      case readMem n req =>
        change (if deviceAddress req.pa || accessExclusive req.access_kind then none else
            match Memory.readBytes memory req.pa n with
            | none => none
            | some word => fetchRun memory fuel (k (.Ok (word, none)) >>= fun a => pure (f a)) registers) = _
        by_cases hg : (deviceAddress req.pa || accessExclusive req.access_kind) = true
        · simp [fetchRun, hg]
        · cases hw : Memory.readBytes memory req.pa n with
          | none => simp [fetchRun, hg, hw]
          | some word => simpa [fetchRun, hg, hw] using ih (k (.Ok (word, none))) registers

/-- Finite closure with no extra stutter or terminal rule beyond reflexivity. -/
inductive NodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent) (image : Memory.ByteMap 64) :
    SailM Unit → LocalState Device → SailM Unit → LocalState Device → Prop
  | nil (program : SailM Unit) (state : LocalState Device) : NodeSteps bus others hart image program state program state
  | cons {program next final : SailM Unit} {state middle last : LocalState Device} :
    NodeStep bus others hart image state program next middle →
    NodeSteps bus others hart image next middle final last →
    NodeSteps bus others hart image program state final last

/-- Successful evaluation follows allowed node steps at the current common read
view. It changes only registers, retaining RAM, devices, log and reservations. -/
theorem fetchRun_sound [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent) (image memory : Memory.ByteMap 64)
    (fuel : Nat) (program : SailM Unit) (state : LocalState Device) (registers' : RegisterFile)
    (value : Unit) (hview : state.view ≤ state.log.length)
    (hread : ∀ a, memory a = Memory.read image state.log hart state.view a)
    (h : fetchRun memory fuel program state.registers = some (value, registers')) :
    NodeSteps bus others hart image program state (.pure value) { state with registers := registers' } := by
  induction fuel generalizing program state with
  | zero => simp [fetchRun] at h
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [fetchRun, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, hregs⟩
      cases result
      cases value
      rw [← hregs]
      exact .nil _ _
    | impure event k =>
      cases event <;> simp only [fetchRun] at h
      all_goals first | solve | contradiction
                      | skip
      case readReg r =>
        exact .cons (read_register_step bus others hart image state r k)
          (ih _ state hview hread h)
      case writeReg r v =>
        exact .cons (write_register_step bus others hart image state r v k)
          (ih _ (state.setReg r v) hview hread h)
      case readMem n req =>
        split at h
        · contradiction
        · rename_i hgate
          have hgate' : deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false := by
            simpa using hgate
          cases hw : Memory.readBytes memory req.pa n with
          | none => simp [hw] at h
          | some word =>
            simp only [hw] at h
            have bytes := Memory.readBytes_spec memory req.pa n word hw
            have readable : Memory.ReadsBytes image state.log hart state.view req.pa n word := by
              intro j hj
              rw [← hread]
              exact bytes j hj
            have step : NodeStep bus others hart image state (.impure (.readMem n req) k)
                (k (.Ok (word, none))) state := by
              simp only [NodeStep, hgate'.1, Bool.false_eq_true, ↓reduceIte]
              exact Or.inl ⟨hgate'.2, state.view, word, Nat.le_refl _, hview, readable, rfl, rfl⟩
            exact .cons step (ih _ state hview hread h)

/-- Initial empty-log RAM reads use the loaded image itself. -/
theorem empty_log_read (image : Memory.ByteMap 64) (hart : Memory.Agent) (a : Memory.PhysicalAddress) :
    Memory.read image [] hart 0 a = image a := rfl

end MachCSL.Machine
