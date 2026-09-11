import MachCSL.Machine.SpinlockWitnessPoolDefs
import MachCSL.Machine.SpinlockWitnessProofs

namespace MachCSL.Machine.SpinlockWitness
open MachCSL.Memory
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prefix_steps (cpu : Fin 2) (devices : Devices.State)
    (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others (hartAgent (cpuId cpu)) (loadedRam SpinlockImage.image)
      (.pure ()) (bootLocal cpu devices) (paused cpu).1 (pausedLocal cpu devices) := by
  have setup := cyclesRun_sound Devices.bus others (hartAgent (cpuId cpu))
    (loadedRam SpinlockImage.image) (loadedRam SpinlockImage.image) 2000 7
    (bootLocal cpu devices) (setupRegisters cpu) (Nat.le_refl 0) (fun _ => rfl) rfl (setupRun_eq cpu)
  let middle : LocalState Devices.State :=
    { bootLocal cpu devices with registers := setupRegisters cpu }
  have pause := pauseRun_sound Devices.bus others (hartAgent (cpuId cpu))
    (loadedRam SpinlockImage.image) (loadedRam SpinlockImage.image) 2000
    (cycle false) middle (paused cpu).1 (paused cpu).2 (Nat.le_refl 0) (fun _ => rfl) (prefixResult_eq cpu)
  have restart : NodeStep Devices.bus others (hartAgent (cpuId cpu))
      (loadedRam SpinlockImage.image) middle (.pure ()) (cycle false) middle :=
    restart_step Devices.bus others _ _ middle false
  exact nodeSteps_trans setup (.cons restart pause)

theorem bothPaused_reservations (before : State) (cpu : CPU) :
    (bothPaused before).reservations cpu = none := by
  simp [bothPaused, firstPaused, writeBack, pausedLocal, bootLocal, bootState]

theorem bothPaused_memory (before : State) :
    (bothPaused before).memory = loadedRam SpinlockImage.image := rfl

theorem afterReadZero_reservations (before : State) :
    (afterReadZero before).reservations =
      updateHart (fun _ => none) 0 (some zeroSnapshot) := by
  funext cpu
  simp only [afterReadZero, writeBack, reservedLocal]
  simp only [updateHart]
  split <;> first | rfl | exact bothPaused_reservations before cpu

theorem zero_read_step (before : State) :
    NodeStep Devices.bus (othersReserved (bothPaused before).reservations 0) (hartAgent 0)
      (bothPaused before).image (focus (bothPaused before) 0) (paused 0).1
      ((readBoundary 0).2 (.Ok (0#32, none))) (reservedLocal before) := by
  rw [paused_program]
  simp only [NodeStep, show deviceAddress (SpinlockAccess.readRequest .lock true).pa = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  refine Or.inr ⟨rfl, Or.inr ⟨?_, 0#32, ?_, rfl, rfl⟩⟩
  · intro address _ reserved
    rcases reserved with ⟨cpu, _, snap, found, _⟩
    rw [bothPaused_reservations] at found
    contradiction
  · exact readBytes_spec (loadedRam SpinlockImage.image) SpinlockImage.lockAddress 4 0#32
      SpinlockImage.lock_initial

theorem zero_snapshot_present (before : State) :
    (afterReadZero before).reservations 0 = some zeroSnapshot := by
  rw [afterReadZero_reservations]
  rfl

theorem one_reservation_none (before : State) :
    (afterReadZero before).reservations 1 = none := by
  rw [afterReadZero_reservations]
  rfl

theorem lock_conflict (before : State) :
    ¬ Disjoint (Footprint SpinlockImage.lockAddress 4)
      (othersReserved (afterReadZero before).reservations 1) := by
  intro disjoint
  apply disjoint SpinlockImage.lockAddress
  · exact ⟨0, by decide, by rfl⟩
  · refine ⟨0, by decide, zeroSnapshot, zero_snapshot_present before, ?_⟩
    exact ⟨0#8, by rfl⟩

/-- The blocked read is a real machine transition even though this hart's
reservation was already empty: it retains exactly the unread Sail program. -/
theorem one_blocked_step (before : State) :
    NodeStep Devices.bus (othersReserved (afterReadZero before).reservations 1) (hartAgent 1)
      (afterReadZero before).image (focus (afterReadZero before) 1) (paused 1).1
      (paused 1).1 (focus (afterReadZero before) 1) := by
  rw [paused_program]
  simp only [NodeStep, show deviceAddress (SpinlockAccess.readRequest .lock true).pa = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  refine Or.inr ⟨rfl, Or.inl ⟨lock_conflict before, trivial, ?_⟩⟩
  have h := one_reservation_none before
  simp only [focus] at ⊢
  rw [h]

theorem pool_trans {image : BootImage} {n m : Nat} {a b c : List Expr × State}
    {observations rest : List Observation}
    (first : PoolSteps image n a observations b) (second : PoolSteps image m b rest c) :
    PoolSteps image (n + m) a (observations ++ rest) c := by
  letI := language image
  induction first with
  | refl => simpa only [Nat.zero_add, List.nil_append] using second
  | @cons n a b c obs obs' first tail ih =>
    simpa only [Nat.add_right_comm, List.append_assoc] using
      Iris.ProgramLogic.Language.NSteps.cons first (ih second)

theorem powerFork_two (generation : Nat) :
    powerFork generation = loop generation 0 :: loop generation 1 :: tailWorkers generation := rfl

/-- Pool framing with abstract programs keeps the proof independent of the
size of the retained generated Sail continuations. -/
theorem two_prefixes_pool (image : BootImage) (g : State) (generation : Nat)
    (live : ThreadLive g generation) (right : List Expr)
    (program0 program1 : SailM Unit) (after0 after1 : LocalState Devices.State)
    (first : NodeSteps Devices.bus (othersReserved g.reservations 0) (hartAgent 0) g.image
      (.pure ()) (focus g 0) program0 after0)
    (second : NodeSteps Devices.bus (othersReserved (writeBack g 0 after0).reservations 1)
      (hartAgent 1) (writeBack g 0 after0).image (.pure ())
      (focus (writeBack g 0 after0) 1) program1 after1) :
    ∃ n, PoolSteps image n
      ([.power, loop generation 0, loop generation 1] ++ right, g) []
      ([.power, .hart generation 0 program0, .hart generation 1 program1] ++ right,
        writeBack (writeBack g 0 after0) 1 after1) := by
  obtain ⟨n, first⟩ := focused_nodeSteps_poolSteps image g 0 generation live [.power]
    (loop generation 1 :: right) (.pure ()) program0 after0 first
  obtain ⟨m, second⟩ := focused_nodeSteps_poolSteps image (writeBack g 0 after0) 1
    generation live [.power, .hart generation 0 program0] right (.pure ()) program1 after1 second
  exact ⟨n + m, pool_trans first second⟩

/-- Normalize the two finite-index carriers before comparing boot register
files; conversion must not re-evaluate boot to discover that both IDs are one. -/
theorem firstPaused_focus_one (before : State) :
    focus (firstPaused before) 1 = bootLocal 1 (Devices.reset before.devices) := by
  simp only [firstPaused, focus, writeBack,
    updateHart_other _ _ _ _ (show (1 : CPU) ≠ 0 from by decide),
    pausedLocal, bootLocal, bootState,
    show (1 : CPU).val = 1 from rfl, show (1 : Fin 2).val = 1 from rfl]

theorem firstPaused_image (before : State) :
    (firstPaused before).image = loadedRam SpinlockImage.image := rfl

theorem bothPaused_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (.power :: powerFork before.generation, bootState SpinlockImage.image before) []
      (bothPausedPool before.generation, bothPaused before) := by
  let g := bootState SpinlockImage.image before
  have live : ThreadLive g before.generation := ⟨rfl, rfl⟩
  have focus0 : focus g 0 = bootLocal 0 (Devices.reset before.devices) := rfl
  have first : NodeSteps Devices.bus (othersReserved g.reservations 0) (hartAgent 0) g.image
      (.pure ()) (focus g 0) (paused 0).1 (pausedLocal 0 (Devices.reset before.devices)) := by
    rw [focus0]
    exact prefix_steps 0 (Devices.reset before.devices) _
  have second : NodeSteps Devices.bus (othersReserved (firstPaused before).reservations 1)
      (hartAgent 1) (firstPaused before).image (.pure ()) (focus (firstPaused before) 1)
      (paused 1).1 (pausedLocal 1 (Devices.reset before.devices)) := by
    rw [firstPaused_focus_one, firstPaused_image]
    exact prefix_steps 1 (Devices.reset before.devices) _
  have joined := two_prefixes_pool SpinlockImage.image g before.generation live
    (tailWorkers before.generation) (paused 0).1 (paused 1).1
    (pausedLocal 0 (Devices.reset before.devices)) (pausedLocal 1 (Devices.reset before.devices))
    first second
  exact joined

theorem hart_pool_step (image : BootImage) (g g' : State) (generation : Nat) (cpu : CPU)
    (program next : SailM Unit) (left right : List Expr)
    (live : ThreadLive g generation) (hart : HartStep g cpu program next g') :
    PoolStep image (left ++ .hart generation cpu program :: right, g) []
      (left ++ .hart generation cpu next :: right, g') := by
  letI := language image
  have step : Step image (.hart generation cpu program) g [] (.hart generation cpu next) g' [] :=
    .hartLive generation cpu program next g g' live hart
  simpa only [PoolStep, List.append_nil] using
    Iris.ProgramLogic.Language.Step.atomic (Λ := language image) step left right

theorem zero_read_pool (before : State) :
    PoolStep SpinlockImage.image
      (bothPausedPool before.generation, bothPaused before) []
      (conflictPool before.generation, afterReadZero before) := by
  exact hart_pool_step SpinlockImage.image (bothPaused before) (afterReadZero before)
    before.generation 0 (paused 0).1 ((readBoundary 0).2 (.Ok (0#32, none)))
    [.power] (.hart before.generation 1 (paused 1).1 :: tailWorkers before.generation)
    ⟨rfl, rfl⟩ ⟨reservedLocal before, zero_read_step before, rfl⟩

theorem one_blocked_pool (before : State) :
    PoolStep SpinlockImage.image
      (conflictPool before.generation, afterReadZero before) []
      (conflictPool before.generation, afterReadZero before) := by
  exact hart_pool_step SpinlockImage.image (afterReadZero before) (afterReadZero before)
    before.generation 1 (paused 1).1 (paused 1).1
    [.power, .hart before.generation 0 ((readBoundary 0).2 (.Ok (0#32, none)))]
    (tailWorkers before.generation) ⟨rfl, rfl⟩
    ⟨focus (afterReadZero before) 1, one_blocked_step before, (writeBack_focus _ _).symm⟩

/-- Actual power-on, both generated setup prefixes, one successful exclusive
read and one explicitly counted blocked exclusive read in the full worker pool. -/
theorem powerOn_first_conflict (before : State) (off : before.power = false) :
    ∃ n, 2 < n ∧ PoolSteps SpinlockImage.image n ([.power], before) [.powerOn]
      (conflictPool before.generation, afterReadZero before) := by
  letI := language SpinlockImage.image
  obtain ⟨n, prefixes⟩ := bothPaused_pool before
  have two : PoolSteps SpinlockImage.image 2
      (bothPausedPool before.generation, bothPaused before) []
      (conflictPool before.generation, afterReadZero before) :=
    .cons (zero_read_pool before) (.cons (one_blocked_pool before) (.refl _))
  have tail := pool_trans prefixes two
  have primitive : Step SpinlockImage.image .power before [.powerOn] .power
      (bootState SpinlockImage.image before) (powerFork before.generation) :=
    .power before [.powerOn] (bootState SpinlockImage.image before) (powerFork before.generation)
      (.on off _ (boot_shape SpinlockImage.image before))
  have first : PoolStep SpinlockImage.image ([.power], before) [.powerOn]
      (.power :: powerFork before.generation, bootState SpinlockImage.image before) := by
    simpa only [PoolStep, powerFork, bootState, List.nil_append, List.cons_append, List.append_nil] using
      Iris.ProgramLogic.Language.Step.atomic (Λ := language SpinlockImage.image) primitive [] []
  refine ⟨n + 2 + 1, by omega, ?_⟩
  exact Iris.ProgramLogic.Language.NSteps.cons first tail

theorem conflict_pool_length (generation : Nat) : (conflictPool generation).length = 12 := by
  simp [conflictPool, tailWorkers, powerFork_length]

theorem conflict_disk_preserved (before : State) :
    (afterReadZero before).devices.virtio.v_disk = before.devices.virtio.v_disk := rfl

theorem conflict_no_writes (before : State) :
    (afterReadZero before).memory = loadedRam SpinlockImage.image ∧
    (afterReadZero before).log = [] := ⟨rfl, rfl⟩

theorem conflict_other_registers (before : State) (cpu : CPU)
    (notZero : cpu ≠ 0) (notOne : cpu ≠ 1) :
    (afterReadZero before).registers cpu =
      (bootState SpinlockImage.image before).registers cpu := by
  simp [afterReadZero, bothPaused, firstPaused, writeBack, updateHart, notZero, notOne]

theorem conflict_generation (before : State) :
    (afterReadZero before).generation = before.generation ∧
    (afterReadZero before).power = true := ⟨rfl, rfl⟩

/-- A closed existential execution, with arbitrary supplied initial device state
and durable disk. The two concrete conflict steps are part of its schedule. -/
theorem concrete_first_conflict (devices : Devices.State) :
    ∃ n, 2 < n ∧ PoolSteps SpinlockImage.image n ([.power], initialState devices) [.powerOn]
      (conflictPool 0, afterReadZero (initialState devices)) :=
  powerOn_first_conflict (initialState devices) rfl

end MachCSL.Machine.SpinlockWitness
