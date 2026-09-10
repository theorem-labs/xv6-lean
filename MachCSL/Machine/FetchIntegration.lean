import MachCSL.Machine.FetchJal
import MachCSL.Machine.Reachability

/-!
Embedding the checked fetched-JAL node execution into the concrete eight-hart
machine and Iris thread-pool relation. These are finite execution witnesses,
not a whole-system safety or adequacy theorem.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Machine

@[simp] theorem updateHart_same (files : CPU → α) (cpu : CPU) (value : α) :
    updateHart files cpu value cpu = value := by simp [updateHart]

theorem updateHart_other (files : CPU → α) (cpu other : CPU) (value : α) (h : other ≠ cpu) :
    updateHart files cpu value other = files other := by simp [updateHart, h]

@[simp] theorem updateHart_self (files : CPU → α) (cpu : CPU) :
    updateHart files cpu (files cpu) = files := by
  funext other
  by_cases h : other = cpu <;> simp [updateHart, h]

@[simp] theorem updateHart_twice (files : CPU → α) (cpu : CPU) (first last : α) :
    updateHart (updateHart files cpu first) cpu last = updateHart files cpu last := by
  funext other
  by_cases h : other = cpu <;> simp [updateHart, h]

@[simp] theorem writeBack_focus (g : State) (cpu : CPU) : writeBack g cpu (focus g cpu) = g := by
  simp [writeBack, focus]

@[simp] theorem writeBack_twice (g : State) (cpu : CPU) (first last : LocalState Devices.State) :
    writeBack (writeBack g cpu first) cpu last = writeBack g cpu last := by
  simp [writeBack]

/-- A fixed hart schedule changes no other hart's reservation domain. -/
theorem othersReserved_writeBack (g : State) (cpu : CPU) (after : LocalState Devices.State) :
    othersReserved (writeBack g cpu after).reservations cpu = othersReserved g.reservations cpu := by
  funext address
  apply propext
  constructor
  · rintro ⟨other, hne, reservation, hr, hd⟩
    exact ⟨other, hne, reservation, by simpa [writeBack, updateHart, hne] using hr, hd⟩
  · rintro ⟨other, hne, reservation, hr, hd⟩
    exact ⟨other, hne, reservation, by simpa [writeBack, updateHart, hne] using hr, hd⟩

/-- One local step embeds without changing the stable environment supplied by
other harts. The focused hart may change its own reservation, memory or devices. -/
theorem nodeStep_writeBack [Platform] (g : State) (cpu : CPU)
    (m m' : SailM Unit) (before after : LocalState Devices.State)
    (step : NodeStep Devices.bus (othersReserved g.reservations cpu) (hartAgent cpu)
      g.image before m m' after) :
    HartStep (writeBack g cpu before) cpu m m' (writeBack g cpu after) := by
  refine ⟨after, ?_, (writeBack_twice g cpu before after).symm⟩
  simpa only [othersReserved_writeBack, focus_writeBack, show (writeBack g cpu before).image = g.image from rfl] using step

/-- The same chosen thread is scheduled throughout; other pool entries remain
in place. No claim is made that arbitrary interleavings follow this witness. -/
theorem nodeSteps_poolSteps [Platform] (image : BootImage) (g : State) (cpu : CPU)
    (generation : Nat) (live : ThreadLive g generation) (left right : List Expr)
    (m m' : SailM Unit) (before after : LocalState Devices.State)
    (steps : NodeSteps Devices.bus (othersReserved g.reservations cpu) (hartAgent cpu)
      g.image m before m' after) :
    ∃ n, PoolSteps image n
      (left ++ .hart generation cpu m :: right, writeBack g cpu before) []
      (left ++ .hart generation cpu m' :: right, writeBack g cpu after) := by
  letI := language image
  induction steps with
  | nil program state => exact ⟨0, .refl _⟩
  | @cons program next final state middle last first rest ih =>
    obtain ⟨n, tail⟩ := ih
    have hhart := nodeStep_writeBack g cpu program next state middle first
    have hlive : ThreadLive (writeBack g cpu state) generation := live
    have primitive : Step image (.hart generation cpu program) (writeBack g cpu state) []
        (.hart generation cpu next) (writeBack g cpu middle) [] :=
      .hartLive generation cpu program next _ _ hlive hhart
    have pool : PoolStep image
        (left ++ .hart generation cpu program :: right, writeBack g cpu state) []
        (left ++ .hart generation cpu next :: right, writeBack g cpu middle) := by
      simpa only [PoolStep, writeBack, List.append_nil] using
        (Iris.ProgramLogic.Language.Step.atomic (Λ := language image) primitive left right)
    exact ⟨n + 1, .cons pool tail⟩

/-- Specialized entry point starting with the actual focused global state. -/
theorem focused_nodeSteps_poolSteps [Platform] (image : BootImage) (g : State) (cpu : CPU)
    (generation : Nat) (live : ThreadLive g generation) (left right : List Expr)
    (m m' : SailM Unit) (after : LocalState Devices.State)
    (steps : NodeSteps Devices.bus (othersReserved g.reservations cpu) (hartAgent cpu)
      g.image m (focus g cpu) m' after) :
    ∃ n, PoolSteps image n (left ++ .hart generation cpu m :: right, g) []
      (left ++ .hart generation cpu m' :: right, writeBack g cpu after) := by
  simpa only [writeBack_focus] using
    nodeSteps_poolSteps image g cpu generation live left right m m' (focus g cpu) after steps

/-- Exact final record: only CPU zero's register file changes during this witness. -/
def fetchedJalState [Platform] (before : State) : State :=
  { bootState jalImage before with
    registers := updateHart (bootState jalImage before).registers 0 fetchedJalRegisters }

theorem boot_focus_zero (before : State) :
    focus (bootState jalImage before) 0 = jalLocalState (Devices.reset before.devices) := rfl

theorem fetchedJal_writeBack [Platform] (before : State) :
    writeBack (bootState jalImage before) 0
      { jalLocalState (Devices.reset before.devices) with registers := fetchedJalRegisters } =
      fetchedJalState before := by
  simp [writeBack, fetchedJalState, bootState, jalLocalState]

/-- A nonempty CPU schedule restarts the loop, fetches real bytes, executes JAL
and returns to the loop, retaining all non-CPU-zero state. -/
theorem fetchedJal_pool_loop [Platform] (before : State) (left right : List Expr) :
    ∃ n, 0 < n ∧ PoolSteps jalImage n
      (left ++ loop before.generation 0 :: right, bootState jalImage before) []
      (left ++ loop before.generation 0 :: right, fetchedJalState before) := by
  letI := language jalImage
  let g := bootState jalImage before
  let hartState := jalLocalState (Devices.reset before.devices)
  have live : ThreadLive g before.generation := ⟨rfl, rfl⟩
  have fetched : NodeSteps Devices.bus (othersReserved g.reservations 0) (hartAgent 0)
      g.image (cycle false) (focus g 0) (.pure ()) { hartState with registers := fetchedJalRegisters } :=
    fetchedJal_node_steps Devices.bus _ _
  obtain ⟨n, rest⟩ := focused_nodeSteps_poolSteps jalImage g 0 before.generation live left right
    (cycle false) (.pure ()) _ fetched
  have localRestart : NodeStep Devices.bus (othersReserved g.reservations 0) (hartAgent 0)
      g.image (focus g 0) (.pure ()) (cycle false) (focus g 0) :=
    restart_step Devices.bus _ _ _ _ false
  have hartRestart : HartStep g 0 (.pure ()) (cycle false) g := by
    refine ⟨focus g 0, localRestart, (writeBack_focus g 0).symm⟩
  have primitive : Step jalImage (loop before.generation 0) g []
      (.hart before.generation 0 (cycle false)) g [] :=
    .hartLive before.generation 0 (.pure ()) (cycle false) g g live hartRestart
  have first : PoolStep jalImage (left ++ loop before.generation 0 :: right, g) []
      (left ++ .hart before.generation 0 (cycle false) :: right, g) := by
    simpa only [PoolStep, g, bootState, loop, List.append_nil] using
      (Iris.ProgramLogic.Language.Step.atomic (Λ := language jalImage) primitive left right)
  refine ⟨n + 1, by omega, ?_⟩
  have complete := Iris.ProgramLogic.Language.NSteps.cons first rest
  simpa only [PoolSteps, g, hartState, fetchedJal_writeBack, loop, List.append_nil] using complete

/-- All other harts' register files are exactly those produced by the same boot. -/
theorem fetchedJal_other_registers [Platform] (before : State) (cpu : CPU) (h : cpu ≠ 0) :
    (fetchedJalState before).registers cpu = (bootState jalImage before).registers cpu := by
  simp [fetchedJalState, updateHart, h]

theorem fetchedJal_preserves_shared [Platform] (before : State) :
    (fetchedJalState before).memory = (bootState jalImage before).memory ∧
    (fetchedJalState before).devices = (bootState jalImage before).devices ∧
    (fetchedJalState before).log = [] ∧
    (fetchedJalState before).reservations = (bootState jalImage before).reservations ∧
    (fetchedJalState before).views = (bootState jalImage before).views ∧
    (fetchedJalState before).generation = before.generation ∧
    (fetchedJalState before).power = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- CPU zero is the first worker in the actual power-on fork list. -/
theorem powerFork_cpu_zero (generation : Nat) :
    powerFork generation = loop generation 0 :: (powerFork generation).tail := by
  rfl

/-- One real power-on transition creates all eleven workers; the schedule then
runs CPU zero through its fetched JAL cycle and leaves the other workers intact. -/
theorem powerOn_fetchedJal [Platform] (before : State) (off : before.power = false) :
    ∃ n, 1 < n ∧ PoolSteps jalImage n ([.power], before) [.powerOn]
      (.power :: powerFork before.generation, fetchedJalState before) := by
  letI := language jalImage
  let rest := (powerFork before.generation).tail
  obtain ⟨n, hn, run⟩ := fetchedJal_pool_loop before [.power] rest
  have primitive : Step jalImage .power before [.powerOn] .power (bootState jalImage before)
      (powerFork before.generation) :=
    .power before [.powerOn] (bootState jalImage before) (powerFork before.generation)
      (.on off _ (boot_shape jalImage before))
  have first : PoolStep jalImage ([.power], before) [.powerOn]
      (.power :: powerFork before.generation, bootState jalImage before) := by
    simpa only [PoolStep, powerFork, bootState, List.nil_append, List.cons_append, List.append_nil] using
      (Iris.ProgramLogic.Language.Step.atomic (Λ := language jalImage) primitive [] [])
  have shape : .power :: powerFork before.generation =
      [.power] ++ loop before.generation 0 :: rest := by
    rw [powerFork_cpu_zero]
    rfl
  rw [shape] at first
  refine ⟨n + 1, by omega, ?_⟩
  have complete := Iris.ProgramLogic.Language.NSteps.cons first run
  simpa only [PoolSteps, List.append_nil, ← shape] using complete

/-- The complete power-on/fetch witness retains the medium from its pre-boot state. -/
theorem powerOn_fetchedJal_disk [Platform] (before : State) :
    (fetchedJalState before).devices.virtio.v_disk = before.devices.virtio.v_disk := rfl

/-- The final machine record exposes the checked instruction-retirement result. -/
theorem fetchedJal_state_registers [Platform] (before : State) :
    (fetchedJalState before).registers 0 .PC = jalImage.vector ∧
    (fetchedJalState before).registers 0 .nextPC = jalImage.vector ∧
    (fetchedJalState before).registers 0 .minstret = 1#64 := by
  simpa only [fetchedJalState, updateHart_same] using fetchedJal_registers

end MachCSL.Machine

open Lean Elab Command in
run_cmd do
  for name in #[``MachCSL.Machine.updateHart_same, ``MachCSL.Machine.updateHart_other,
      ``MachCSL.Machine.updateHart_self, ``MachCSL.Machine.updateHart_twice,
      ``MachCSL.Machine.writeBack_focus, ``MachCSL.Machine.writeBack_twice,
      ``MachCSL.Machine.othersReserved_writeBack, ``MachCSL.Machine.nodeStep_writeBack,
      ``MachCSL.Machine.nodeSteps_poolSteps, ``MachCSL.Machine.focused_nodeSteps_poolSteps,
      ``MachCSL.Machine.boot_focus_zero, ``MachCSL.Machine.fetchedJal_writeBack,
      ``MachCSL.Machine.fetchedJal_pool_loop, ``MachCSL.Machine.fetchedJal_other_registers,
      ``MachCSL.Machine.fetchedJal_preserves_shared, ``MachCSL.Machine.powerFork_cpu_zero,
      ``MachCSL.Machine.powerOn_fetchedJal, ``MachCSL.Machine.powerOn_fetchedJal_disk,
      ``MachCSL.Machine.fetchedJal_state_registers] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
