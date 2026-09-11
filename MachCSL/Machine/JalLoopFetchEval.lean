import MachCSL.Machine.JalLoopEval

/-! Finite execution certificates allowing actual register events and ordinary
RAM reads. The handler preserves every request and typed result. -/
namespace MachCSL.Machine.JalLoop
open _root_.Sail.ConcurrencyInterfaceV1.Free

def fetchHandler (memory : Memory.ByteMap 64) :
    Sail.Execution.Handler RegisterType exception RegisterFile
  | .readMem n req, before, result, after =>
      deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false ∧
      ∃ word, Memory.readBytes memory req.pa n = some word ∧
        result = .Ok (word, none) ∧ after = before
  | event, before, result, after => Sail.Registers.handler event before result after

abbrev FetchExec (memory : Memory.ByteMap 64) (program : SailM α)
    (before : RegisterFile) (value : α) (after : RegisterFile) : Prop :=
  ∃ trace, Sail.Execution.Steps (fetchHandler memory) (program, before) trace (.pure value, after)

theorem fetchExec_bind (memory : Memory.ByteMap 64) (program : SailM α)
    (next : α → SailM β) (before after : RegisterFile) (value : β) :
    FetchExec memory (program >>= next) before value after ↔
      ∃ middleValue middle, FetchExec memory program before middleValue middle ∧
        FetchExec memory (next middleValue) middle value after := by
  simp only [FetchExec, Sail.Execution.completes_bind_iff]
  constructor
  · rintro ⟨trace, result, middle, left, right, _, hl, hr⟩
    exact ⟨result, middle, ⟨left, hl⟩, ⟨right, hr⟩⟩
  · rintro ⟨result, middle, ⟨left, hl⟩, ⟨right, hr⟩⟩
    exact ⟨left ++ right, result, middle, left, right, rfl, hl, hr⟩

theorem FetchExec.bind {memory : Memory.ByteMap 64} {program : SailM α}
    {next : α → SailM β} {before middle after : RegisterFile} {a : α} {b : β}
    (first : FetchExec memory program before a middle)
    (second : FetchExec memory (next a) middle b after) :
    FetchExec memory (program >>= next) before b after :=
  (fetchExec_bind _ _ _ _ _ _).mpr ⟨a, middle, first, second⟩

theorem FetchExec.liftExcept {memory : Memory.ByteMap 64} {program : SailM α}
    {before after : RegisterFile} {value : α}
    (exec : FetchExec memory program before value after) (ε : Type) :
    FetchExec memory (monadLift program : SailME ε α).run before (.ok value) after := by
  change FetchExec memory (program >>= fun a => pure (Except.ok a)) before (.ok value) after
  apply exec.bind
  exact ⟨[], .nil _⟩

theorem FetchExec.exceptBind {memory : Memory.ByteMap 64} {program : SailME ε α}
    {next : α → SailME ε β} {before middle after : RegisterFile} {a : α} {b : β}
    (first : FetchExec memory program.run before (.ok a) middle)
    (second : FetchExec memory (next a).run middle (.ok b) after) :
    FetchExec memory (program >>= next).run before (.ok b) after :=
  first.bind second

private theorem registerSteps_fetch (memory : Memory.ByteMap 64)
    {first last : SailM α × RegisterFile} {trace}
    (steps : Sail.Execution.Steps
      (Sail.Registers.handler (RegisterType := RegisterType) (ue := exception)) first trace last) :
    Sail.Execution.Steps (fetchHandler memory) first trace last := by
  induction steps with
  | nil => exact .nil _
  | cons step _ ih =>
    apply Sail.Execution.Steps.cons _ ih
    cases step with
    | @event event result k before after handled =>
      apply Sail.Execution.Step.event
      cases event <;> simp_all [fetchHandler, Sail.Registers.handler]

theorem RegisterExec.fetchExec (memory : Memory.ByteMap 64) {program : SailM α}
    {before after : RegisterFile} {value : α}
    (exec : RegisterExec program before value after) :
    FetchExec memory program before value after := by
  obtain ⟨trace, steps⟩ := exec
  exact ⟨trace, registerSteps_fetch memory steps⟩

/-- An incomplete snapshot rejects every unlisted register. Thus successful
certificates establish that no other register was read and no register was written. -/
abbrev Snapshot := (r : Register) → Option (RegisterType r)

def snapshotRun (memory : Memory.ByteMap 64) (snapshot : Snapshot) :
    Nat → SailM α → Option α
  | 0, _ => none
  | _ + 1, .pure value => some value
  | fuel + 1, .impure event k => match event with
    | .readReg r => (snapshot r).bind fun value => snapshotRun memory snapshot fuel (k value)
    | .readMem n req =>
      if deviceAddress req.pa || accessExclusive req.access_kind then none else
      (Memory.readBytes memory req.pa n).bind fun word =>
        snapshotRun memory snapshot fuel (k (.Ok (word, none)))
    | _ => none

def Covers (snapshot : Snapshot) (registers : RegisterFile) : Prop :=
  ∀ r value, snapshot r = some value → registers r = value

theorem snapshotRun_exec (memory : Memory.ByteMap 64) (snapshot : Snapshot)
    (rs : RegisterFile) (covered : Covers snapshot rs) (fuel : Nat)
    (program : SailM α) (value : α)
    (success : snapshotRun memory snapshot fuel program = some value) :
    FetchExec memory program rs value rs := by
  induction fuel generalizing program with
  | zero => simp [snapshotRun] at success
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [snapshotRun, Option.some.injEq] at success
      subst result
      exact ⟨[], .nil _⟩
    | impure event k =>
      cases event <;> simp only [snapshotRun] at success
      all_goals first | contradiction | skip
      case readReg r =>
        cases hs : snapshot r with
        | none => simp [hs] at success
        | some value' =>
          simp only [hs, Option.bind_some] at success
          obtain ⟨trace, steps⟩ := ih _ success
          exact ⟨_ :: trace, .cons (.event ⟨(covered r value' hs).symm, rfl⟩) steps⟩
      case readMem n req =>
        split at success
        · contradiction
        · rename_i hgate
          have gate : deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false := by
            simpa using hgate
          cases hw : Memory.readBytes memory req.pa n with
          | none => simp [hw] at success
          | some word =>
            simp only [hw, Option.bind_some] at success
            obtain ⟨trace, steps⟩ := ih _ success
            exact ⟨_ :: trace, .cons (.event ⟨gate.1, gate.2, word, hw, rfl, rfl⟩) steps⟩

theorem fetchExec_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image memory : Memory.ByteMap 64) (state : LocalState Device)
    (program : SailM Unit) (after : RegisterFile)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, memory a = Memory.read image state.log hart state.view a)
    (exec : FetchExec memory program state.registers () after) :
    NodeSteps bus others hart image program state (.pure ()) { state with registers := after } := by
  obtain ⟨trace, steps⟩ := exec
  have general : ∀ (before : RegisterFile) (program next : SailM Unit),
      Sail.Execution.Steps (fetchHandler memory) (program, before) trace (next, after) →
      NodeSteps bus others hart image program {state with registers := before}
        next {state with registers := after} := by
    clear steps
    induction trace with
    | nil => intro before program next steps; cases steps; exact .nil _ _
    | cons label trace ih =>
      intro before program next steps
      cases steps with
      | cons first rest =>
        cases first with
        | @event event result k before middle handled =>
          cases event <;> simp only [fetchHandler, Sail.Registers.handler] at handled
          all_goals first | contradiction | skip
          case readReg r =>
            obtain ⟨rfl, rfl⟩ := handled
            exact .cons (read_register_step bus others hart image _ r k) (ih _ _ _ rest)
          case writeReg r value =>
            subst middle
            cases result
            exact .cons (write_register_step bus others hart image _ r value k) (ih _ _ _ rest)
          case readMem n req =>
            obtain ⟨device, exclusive, word, hw, rfl, rfl⟩ := handled
            have readable : Memory.ReadsBytes image state.log hart state.view req.pa n word := by
              intro j hj
              rw [← hread]
              exact Memory.readBytes_spec memory req.pa n word hw j hj
            apply NodeSteps.cons _ (ih _ _ _ rest)
            simp only [NodeStep, device, Bool.false_eq_true, ↓reduceIte]
            exact Or.inl ⟨exclusive, state.view, word, Nat.le_refl _, hview, readable, rfl, rfl⟩
  simpa using general state.registers program (.pure ()) steps

end MachCSL.Machine.JalLoop
