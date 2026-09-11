import MachCSL.Machine.SpinlockWitnessHeldStateProofs

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem zero_steps (g : State) (generation : Nat) (live : ThreadLive g generation)
    (program next other : SailM Unit) (after : LocalState Devices.State)
    (steps : NodeSteps Devices.bus (othersReserved g.reservations 0) 0 g.image
      program (focus g 0) next after) :
    ∃ n, PoolSteps SpinlockImage.image n (pairPool generation program other, g) []
      (pairPool generation next other, writeBack g 0 after) :=
  focused_nodeSteps_poolSteps SpinlockImage.image g 0 generation live [.power]
    (.hart generation 1 other :: tailWorkers generation) program next after steps

theorem one_steps (g : State) (generation : Nat) (live : ThreadLive g generation)
    (other program next : SailM Unit) (after : LocalState Devices.State)
    (steps : NodeSteps Devices.bus (othersReserved g.reservations 1) 1 g.image
      program (focus g 1) next after) :
    ∃ n, PoolSteps SpinlockImage.image n (pairPool generation other program, g) []
      (pairPool generation other next, writeBack g 1 after) :=
  focused_nodeSteps_poolSteps SpinlockImage.image g 1 generation live
    [.power, .hart generation 0 other] (tailWorkers generation) program next after steps

theorem zero_step (g : State) (generation : Nat) (live : ThreadLive g generation)
    (program next other : SailM Unit) (after : LocalState Devices.State)
    (step : NodeStep Devices.bus (othersReserved g.reservations 0) 0 g.image
      (focus g 0) program next after) :
    PoolStep SpinlockImage.image (pairPool generation program other, g) []
      (pairPool generation next other, writeBack g 0 after) :=
  hart_pool_step SpinlockImage.image g (writeBack g 0 after) generation 0 program next
    [.power] (.hart generation 1 other :: tailWorkers generation) live ⟨after, step, rfl⟩

theorem one_step (g : State) (generation : Nat) (live : ThreadLive g generation)
    (other program next : SailM Unit) (after : LocalState Devices.State)
    (step : NodeStep Devices.bus (othersReserved g.reservations 1) 1 g.image
      (focus g 1) program next after) :
    PoolStep SpinlockImage.image (pairPool generation other program, g) []
      (pairPool generation other next, writeBack g 1 after) :=
  hart_pool_step SpinlockImage.image g (writeBack g 1 after) generation 1 program next
    [.power, .hart generation 0 other] (tailWorkers generation) live ⟨after, step, rfl⟩

theorem single {a b : List Expr × State} (step : PoolStep SpinlockImage.image a [] b) :
    PoolSteps SpinlockImage.image 1 a [] b := by
  letI := language SpinlockImage.image
  exact .cons step (.refl _)

theorem swap_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (conflictPool before.generation, afterReadZero before) []
      (pairPool before.generation (swapProgram 0 0#32) (paused 1).1, afterReadZero before) := by
  have steps : NodeSteps Devices.bus (othersReserved (afterReadZero before).reservations 0) 0
      (afterReadZero before).image ((readBoundary 0).2 (.Ok (0#32, none)))
      (focus (afterReadZero before) 0) (swapProgram 0 0#32) (startingLocal (Devices.reset before.devices)) := by
    rw [starting_focus]
    exact swap_prefix_zero _ _
  obtain ⟨n, framed⟩ := zero_steps (afterReadZero before) before.generation ⟨rfl, rfl⟩
    _ _ (paused 1).1 _ steps
  have same : writeBack (afterReadZero before) 0 (startingLocal (Devices.reset before.devices)) =
      afterReadZero before := by rw [← starting_focus, writeBack_focus]
  rw [same] at framed
  exact ⟨n, framed⟩

theorem swap_commit_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (swapProgram 0 0#32) (paused 1).1, afterReadZero before) []
      (pairPool before.generation (swapResume 0 0#32 (.Ok none)) (paused 1).1, swapped before) := by
  apply zero_step (afterReadZero before) before.generation ⟨rfl, rfl⟩
  rw [starting_focus]
  exact swap_commit _ _ (swap_free before)

theorem counter_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (swapResume 0 0#32 (.Ok none)) (paused 1).1, swapped before) []
      (pairPool before.generation counterProgram (paused 1).1, counterReady before) := by
  apply zero_steps (swapped before) before.generation ⟨rfl, rfl⟩
  rw [swapped_focus]
  exact advance_counter _ _

theorem counter_commit_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation counterProgram (paused 1).1, counterReady before) []
      (pairPool before.generation (counterResume (.Ok none)) (paused 1).1, counterCommitted before) := by
  apply zero_step (counterReady before) before.generation ⟨rfl, rfl⟩
  rw [counter_focus]
  exact counter_commit _ _ (counter_free before)

theorem read_one_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (counterResume (.Ok none)) (paused 1).1, counterCommitted before) []
      (pairPool before.generation (counterResume (.Ok none)) ((readBoundary 1).2 (.Ok (1#32, none))),
        oneReserved before) := by
  apply one_step (counterCommitted before) before.generation ⟨rfl, rfl⟩
  rw [waiting_focus]
  exact read_one _ _ (reader_free before)

theorem one_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (counterResume (.Ok none)) ((readBoundary 1).2 (.Ok (1#32, none))),
        oneReserved before) []
      (pairPool before.generation (counterResume (.Ok none)) (swapProgram 1 1#32), oneReserved before) := by
  have steps : NodeSteps Devices.bus (othersReserved (oneReserved before).reservations 1) 1
      (oneReserved before).image ((readBoundary 1).2 (.Ok (1#32, none))) (focus (oneReserved before) 1)
      (swapProgram 1 1#32) (readerLocal (Devices.reset before.devices)) := by
    rw [reader_focus]
    exact swap_prefix_one _ _
  obtain ⟨n, framed⟩ := one_steps (oneReserved before) before.generation ⟨rfl, rfl⟩
    (counterResume (.Ok none)) _ _ _ steps
  have same : writeBack (oneReserved before) 1 (readerLocal (Devices.reset before.devices)) =
      oneReserved before := by rw [← reader_focus, writeBack_focus]
  rw [same] at framed
  exact ⟨n, framed⟩

theorem unlock_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (counterResume (.Ok none)) (swapProgram 1 1#32), oneReserved before) []
      (blockedPool before.generation, unlockReady before) := by
  apply zero_steps (oneReserved before) before.generation ⟨rfl, rfl⟩
  rw [committed_other_focus]
  exact advance_unlock _ _

/-- An explicitly counted unsuccessful unlock: the other hart's snapshot
blocks the actual plain RAM-write event without changing either continuation. -/
theorem unlock_blocked_pool (before : State) :
    PoolStep SpinlockImage.image (blockedPool before.generation, unlockReady before) []
      (blockedPool before.generation, unlockReady before) := by
  have node : NodeStep Devices.bus (othersReserved (unlockReady before).reservations 0) 0
      (unlockReady before).image (focus (unlockReady before) 0) unlockProgram unlockProgram
      (focus (unlockReady before) 0) := by
    rw [unlock_focus]
    exact unlock_blocked _ _ (unlock_conflict before)
  exact hart_pool_step SpinlockImage.image (unlockReady before) (unlockReady before)
    before.generation 0 unlockProgram unlockProgram [.power]
    (.hart before.generation 1 (swapProgram 1 1#32) :: tailWorkers before.generation)
    ⟨rfl, rfl⟩ ⟨_, node, (writeBack_focus _ _).symm⟩

theorem first_to_unlock_conflict (before : State) :
    ∃ n, 0 < n ∧ PoolSteps SpinlockImage.image n
      (conflictPool before.generation, afterReadZero before) []
      (blockedPool before.generation, unlockReady before) := by
  obtain ⟨n0, swapPrefix⟩ := swap_prefix_pool before
  obtain ⟨n1, counterPrefix⟩ := counter_prefix_pool before
  obtain ⟨n2, onePrefix⟩ := one_prefix_pool before
  obtain ⟨n3, unlockPrefix⟩ := unlock_prefix_pool before
  have a := pool_trans swapPrefix (single (swap_commit_pool before))
  have b := pool_trans a counterPrefix
  have c := pool_trans b (single (counter_commit_pool before))
  have d := pool_trans c (single (read_one_pool before))
  have e := pool_trans d onePrefix
  have f := pool_trans e unlockPrefix
  have result := pool_trans f (single (unlock_blocked_pool before))
  exact ⟨n0 + 1 + n1 + 1 + 1 + n2 + n3 + 1, by omega, result⟩

theorem powerOn_unlock_conflict (before : State) (off : before.power = false) :
    ∃ n, 3 < n ∧ PoolSteps SpinlockImage.image n ([.power], before) [.powerOn]
      (blockedPool before.generation, unlockReady before) := by
  obtain ⟨n, firstPositive, first⟩ := powerOn_first_conflict before off
  obtain ⟨m, nextPositive, next⟩ := first_to_unlock_conflict before
  exact ⟨n + m, by omega, pool_trans first next⟩

theorem concrete_unlock_conflict (devices : Devices.State) :
    ∃ n, 3 < n ∧ PoolSteps SpinlockImage.image n ([.power], initialState devices) [.powerOn]
      (blockedPool 0, unlockReady (initialState devices)) :=
  powerOn_unlock_conflict (initialState devices) rfl

end MachCSL.Machine.SpinlockWitnessHeld
