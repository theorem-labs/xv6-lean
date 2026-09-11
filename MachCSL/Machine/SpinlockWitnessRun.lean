import MachCSL.Machine.FetchRun

/-! A proof evaluator for finite prefixes ending at their exact Sail continuation.
Unexecuted events are pauses, not invented transitions or progress witnesses. -/
namespace MachCSL.Machine.SpinlockWitness
open _root_.Sail.ConcurrencyInterfaceV1.Free

/-- Execute register events and plain RAM reads; retain the exact program at
every other event. Fuel exhaustion is failure, and a pause consumes no step. -/
def pauseRun (memory : Memory.ByteMap 64) :
    Nat → SailM Unit → RegisterFile → Option (SailM Unit × RegisterFile)
  | 0, _, _ => none
  | _ + 1, .pure value, registers => some (.pure value, registers)
  | fuel + 1, program@(.impure event k), registers => match event with
    | .readReg r => pauseRun memory fuel (k (registers r)) registers
    | .writeReg r value => pauseRun memory fuel (k ()) (Sail.Registers.write registers r value)
    | .readMem n req =>
      if deviceAddress req.pa || accessExclusive req.access_kind then some (program, registers) else
      match Memory.readBytes memory req.pa n with
      | none => none
      | some value => pauseRun memory fuel (k (.Ok (value, none))) registers
    | _ => some (program, registers)

/-- A successful prefix embeds into the existing machine relation. This also
covers a zero-step pause at an unsupported event, without asserting progress. -/
theorem pauseRun_sound [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image memory : Memory.ByteMap 64) (fuel : Nat) (program : SailM Unit)
    (state : LocalState Device) (rest : SailM Unit) (registers' : RegisterFile)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, memory a = Memory.read image state.log hart state.view a)
    (h : pauseRun memory fuel program state.registers = some (rest, registers')) :
    NodeSteps bus others hart image program state rest { state with registers := registers' } := by
  induction fuel generalizing program state with
  | zero => simp [pauseRun] at h
  | succ fuel ih =>
    cases program with
    | pure value =>
      simp only [pauseRun, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hregs⟩
      rw [← hregs]
      exact .nil _ _
    | impure event k =>
      cases event <;> simp only [pauseRun, Option.some.injEq, Prod.mk.injEq] at h
      all_goals first
        | (rcases h with ⟨rfl, hregs⟩; rw [← hregs]; exact .nil _ _)
        | skip
      case readReg r =>
        exact .cons (read_register_step bus others hart image state r k)
          (ih _ state hview hread h)
      case writeReg r v =>
        exact .cons (write_register_step bus others hart image state r v k)
          (ih _ (state.setReg r v) hview hread h)
      case readMem n req =>
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, hregs⟩
          rw [← hregs]
          exact .nil _ _
        · rename_i hgate
          have gates : deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false := by
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
              simp only [NodeStep, gates.1, Bool.false_eq_true, ↓reduceIte]
              exact Or.inl ⟨gates.2, state.view, word, Nat.le_refl _, hview, readable, rfl, rfl⟩
            exact .cons step (ih _ state hview hread h)

theorem nodeSteps_trans [Platform] (first : NodeSteps bus others hart image a s b t)
    (second : NodeSteps bus others hart image b t c u) :
    NodeSteps bus others hart image a s c u := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

/-- Successive real cycles, with an explicit restart between each pair. -/
def cyclesRun [Platform] (memory : Memory.ByteMap 64) (fuel : Nat)
    (initial : RegisterFile) : Nat → Option RegisterFile
  | 0 => some initial
  | n + 1 => do
    let rs ← cyclesRun memory fuel initial n
    let (_, after) ← fetchRun memory fuel (cycle false) rs
    pure after

theorem cyclesRun_sound [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image memory : Memory.ByteMap 64) (fuel rounds : Nat)
    (state : LocalState Device) (after : RegisterFile)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, memory a = Memory.read image state.log hart state.view a)
    (hreservation : state.reservation = none)
    (h : cyclesRun memory fuel state.registers rounds = some after) :
    NodeSteps bus others hart image (.pure ()) state (.pure ())
      { state with registers := after } := by
  induction rounds generalizing after with
  | zero =>
    simp only [cyclesRun, Option.some.injEq] at h
    rw [← h]
    exact .nil _ _
  | succ rounds ih =>
    cases hp : cyclesRun memory fuel state.registers rounds with
    | none => simp [cyclesRun, hp] at h
    | some prior =>
      cases hr : fetchRun memory fuel (cycle false) prior with
      | none => simp [cyclesRun, hp, hr] at h
      | some result =>
        obtain ⟨value, registers⟩ := result
        cases value
        have heq : registers = after := by simpa [cyclesRun, hp, hr] using h
        subst registers
        have earlier := ih prior hp
        have run := fetchRun_sound bus others hart image memory fuel (cycle false)
          { state with registers := prior } after () hview hread hr
        have restart : NodeStep bus others hart image { state with registers := prior }
            (.pure ()) (cycle false) { state with registers := prior } := by
          simpa only [hreservation] using
            restart_step bus others hart image { state with registers := prior } false
        exact nodeSteps_trans earlier (.cons restart run)

end MachCSL.Machine.SpinlockWitness
