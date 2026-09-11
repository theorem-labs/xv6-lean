import MachCSL.Machine.SpinlockWitnessHolderDefs

namespace MachCSL.Machine.SpinlockWitnessHolder
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Machine.SpinlockWitnessRelease
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem cycles_two (memory : ByteMap 64) (fuel : Nat) (before middle after : RegisterFile)
    (first : fetchRun memory fuel (cycle false) before = some ((), middle))
    (second : fetchRun memory fuel (cycle false) middle = some ((), after)) :
    cyclesRun memory fuel before 2 = some after := by
  change ((fetchRun memory fuel (cycle false) before >>= fun pair => some pair.2) >>=
    fun rs => fetchRun memory fuel (cycle false) rs >>= fun pair => some pair.2) = some after
  rw [first]
  change (fetchRun memory fuel (cycle false) middle >>= fun pair => some pair.2) = some after
  rw [second]
  rfl

theorem remaining_work : cyclesRun readOne 2000 (workAfter 2) 2 = some (workAfter 4) :=
  cycles_two readOne 2000 (workAfter 2) (workAfter 3) (workAfter 4) work2 work3

theorem reach_local (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 0 (loadedRam SpinlockImage.image)
      (swapResume 0 0#32 (.Ok none)) (swapLocal devices) (.pure ()) (boundaryLocal devices) := by
  let afterSwap := { swapLocal devices with registers := acquiredRegisters }
  have finish := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000
    _ (swapLocal devices) (.pure ()) acquiredRegisters (Nat.le_refl 1) (fun _ => rfl) swap_tail
  have work := cyclesRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000 2
    afterSwap (workAfter 2) (Nat.le_refl 1) (fun _ => rfl) rfl (work_all 2 (by decide))
  exact nodeSteps_trans finish work

theorem leave_local (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 0 (loadedRam SpinlockImage.image)
      (.pure ()) (boundaryLocal devices) counterProgram (counterLocal devices) := by
  let afterWork := { boundaryLocal devices with registers := workAfter 4 }
  have work := cyclesRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000 2
    (boundaryLocal devices) (workAfter 4) (Nat.le_refl 1) (fun _ => rfl) rfl remaining_work
  have restart : NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      afterWork (.pure ()) (cycle false) afterWork := restart_step Devices.bus others _ _ afterWork false
  have next := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000
    (cycle false) afterWork counterProgram counterRegisters (Nat.le_refl 1) (fun _ => rfl) counter_result
  exact nodeSteps_trans work (.cons restart next)

theorem state_focus (before : State) : focus (state before) 0 = boundaryLocal (Devices.reset before.devices) :=
  focus_writeBack _ _ _

theorem holder_pc (before : State) :
    (state before).registers 0 .PC = SpinlockImage.instructionAddress ⟨10, by decide⟩ := by
  simp only [state, writeBack, updateHart_same, boundaryLocal, localAt]
  rfl

theorem holder_member (before : State) :
    Expr.hart (state before).generation 0 (.pure ()) ∈ pool before.generation := by
  change Expr.hart before.generation 0 (.pure ()) ∈ _
  simp only [pool, pairPool, List.mem_append, List.mem_cons]
  exact Or.inl (Or.inr (Or.inl trivial))

theorem reach_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (swapResume 0 0#32 (.Ok none)) (paused 1).1, swapped before) []
      (pool before.generation, state before) := by
  apply zero_steps (swapped before) before.generation ⟨rfl, rfl⟩
  rw [swapped_focus]
  exact reach_local _ _

theorem leave_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pool before.generation, state before) []
      (pairPool before.generation counterProgram (paused 1).1, counterReady before) := by
  have steps : NodeSteps Devices.bus (othersReserved (state before).reservations 0) 0
      (state before).image (.pure ()) (focus (state before) 0)
      counterProgram (counterLocal (Devices.reset before.devices)) := by
    rw [state_focus]
    exact leave_local _ _
  obtain ⟨n, framed⟩ := zero_steps (state before) before.generation ⟨rfl, rfl⟩
    (.pure ()) counterProgram (paused 1).1 _ steps
  have same : writeBack (state before) 0 (counterLocal (Devices.reset before.devices)) =
      counterReady before := writeBack_twice (swapped before) 0 _ _
  rw [same] at framed
  exact ⟨n, framed⟩

theorem powerOn_holder (before : State) (off : before.power = false) :
    ∃ n, 2 < n ∧ PoolSteps SpinlockImage.image n ([.power], before) [.powerOn]
      (pool before.generation, state before) := by
  obtain ⟨n₀, positive, first⟩ := powerOn_first_conflict before off
  obtain ⟨n₁, preSchedule⟩ := swap_prefix_pool before
  obtain ⟨n₂, body⟩ := reach_pool before
  have result := pool_trans (pool_trans (pool_trans first preSchedule) (single (swap_commit_pool before))) body
  exact ⟨n₀ + n₁ + 1 + n₂, by omega, result⟩

theorem holder_to_final (before : State) :
    ∃ n, 9 ≤ n ∧ PoolSteps SpinlockImage.image n
      (pool before.generation, state before) []
      (finalPool before.generation, finalState before) := by
  obtain ⟨n₀, counterPrefix⟩ := leave_pool before
  obtain ⟨n₁, onePrefix⟩ := one_prefix_pool before
  obtain ⟨n₂, unlockPrefix⟩ := unlock_prefix_pool before
  obtain ⟨n₃, positive, finish⟩ := finish_schedule before
  have a := pool_trans counterPrefix (single (counter_commit_pool before))
  have b := pool_trans a (single (read_one_pool before))
  have c := pool_trans b onePrefix
  have d := pool_trans c unlockPrefix
  have e := pool_trans d (single (unlock_blocked_pool before))
  have result := pool_trans e finish
  exact ⟨n₀ + 1 + 1 + n₁ + n₂ + 1 + n₃, by omega, result⟩

/-- The reachable body boundary lies on a real execution ending at the same
seven-message state, retaining both blocked events in the composed phases. -/
theorem through_holder (before : State) (off : before.power = false) :
    ∃ n m, 2 < n ∧ 9 ≤ m ∧
      PoolSteps SpinlockImage.image n ([.power], before) [.powerOn]
        (pool before.generation, state before) ∧
      PoolSteps SpinlockImage.image m (pool before.generation, state before) []
        (finalPool before.generation, finalState before) ∧
      PoolSteps SpinlockImage.image (n + m) ([.power], before) [.powerOn]
        (finalPool before.generation, finalState before) := by
  obtain ⟨n, positive, first⟩ := powerOn_holder before off
  obtain ⟨m, positive', rest⟩ := holder_to_final before
  exact ⟨n, m, positive, positive', first, rest, pool_trans first rest⟩

theorem scheduled_trans {first rest : List SpinlockPool.ScheduledEvent}
    {a b c : SpinlockPool.Config}
    (preSchedule : SpinlockPool.ScheduledSteps first a b)
    (suffix : SpinlockPool.ScheduledSteps rest b c) :
    SpinlockPool.ScheduledSteps (first ++ rest) a c := by
  induction preSchedule with
  | refl => exact suffix
  | cons first tail ih => exact .cons first (ih suffix)

/-- A genuine operational holder, obtained by annotating the actual machine
preSchedule. The same annotation continues through to the exact seven-write end. -/
theorem annotated_holder (before : State) (off : before.power = false)
    (zero : before.generation = 0) :
    ∃ n m preSchedule suffix middle final,
      2 < n ∧ 9 ≤ m ∧ preSchedule.length = n ∧ suffix.length = m ∧
      SpinlockPool.scheduleObservations preSchedule = [.powerOn] ∧
      SpinlockPool.scheduleObservations suffix = [] ∧
      AnnotatedPool.eraseConfig middle = (pool before.generation, state before) ∧
      AnnotatedPool.eraseConfig final = (finalPool before.generation, finalState before) ∧
      SpinlockPool.ScheduledSteps preSchedule ([(.power, .worker)], before) middle ∧
      SpinlockPool.ScheduledSteps suffix middle final ∧
      SpinlockPool.ScheduledSteps (preSchedule ++ suffix) ([(.power, .worker)], before) final ∧
      SpinlockPool.PoolInv middle ∧ SpinlockPool.Holds middle 0 ∧ SpinlockPool.PoolInv final := by
  obtain ⟨n, m, positive, positive', first, rest, _⟩ := through_holder before off
  obtain ⟨preSchedule, ⟨annotated, g⟩, length, events, erased, scheduled, inv, _, _⟩ :=
    SpinlockPool.annotate_run before off zero n (pool before.generation, state before) [.powerOn] first
  have stateEq : g = state before := congrArg Prod.snd erased
  subst g
  have poolEq : AnnotatedPool.erase annotated = pool before.generation := congrArg Prod.fst erased
  obtain ⟨cursor, member⟩ := SpinlockPool.erased_hart_label inv.1
    (show Expr.hart (state before).generation 0 (.pure ()) ∈ AnnotatedPool.erase annotated from by
      rw [poolEq]; exact holder_member before)
  have held : SpinlockPool.Holds (annotated, state before) 0 :=
    SpinlockPool.boundary_holds inv rfl member (holder_pc before) (by decide) (by decide)
  have rest' : PoolSteps SpinlockImage.image m (AnnotatedPool.eraseConfig (annotated, state before)) []
      (finalPool before.generation, finalState before) := by rw [erased]; exact rest
  obtain ⟨final, finalEq, annotatedRest, finalInv⟩ :=
    AnnotatedPool.lift_steps SpinlockImage.image SpinlockPool.Transition SpinlockPool.PoolInv SpinlockPool.covers
      (annotated, state before) (finalPool before.generation, finalState before) m [] inv rest'
  obtain ⟨suffix, suffixLength, suffixEvents, suffixSteps⟩ := SpinlockPool.steps_have_schedule annotatedRest
  exact ⟨n, m, preSchedule, suffix, (annotated, state before), final,
    positive, positive', length, suffixLength, events, suffixEvents, erased, finalEq,
    scheduled, suffixSteps, scheduled_trans scheduled suffixSteps, inv, held, finalInv⟩

theorem concrete_holder (devices : Devices.State) :
    ∃ schedule annotated,
      SpinlockPool.ScheduledSteps schedule ([(.power, .worker)], initialState devices) annotated ∧
      SpinlockPool.Holds annotated 0 := by
  obtain ⟨n, m, preSchedule, suffix, middle, final, _, _, _, _, _, _, _, _, first, _, _, _, held, _⟩ :=
    annotated_holder (initialState devices) rfl rfl
  exact ⟨preSchedule, middle, first, held⟩

end MachCSL.Machine.SpinlockWitnessHolder
