import MachCSL.Machine.SpinlockWitnessReleaseStateProofs

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem failed_commit_pool (before : State) :
    PoolStep SpinlockImage.image (blockedPool before.generation, unlockReady before) []
      (pairPool before.generation unlockProgram (swapResume 1 1#32 (.Ok none)), failedState before) := by
  apply one_step (unlockReady before) before.generation ⟨rfl, rfl⟩
  rw [reader_other_focus]
  exact failed_commit _ _ (failed_free before)

theorem first_release_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation unlockProgram (swapResume 1 1#32 (.Ok none)), failedState before) []
      (pairPool before.generation (unlockResume (.Ok none)) (swapResume 1 1#32 (.Ok none)), releasedState before) := by
  apply zero_step (failedState before) before.generation ⟨rfl, rfl⟩
  rw [first_release_focus]
  exact first_release _ _ (clear_free _ _ _ _ (failed_reservations before))

theorem retry_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (unlockResume (.Ok none)) (swapResume 1 1#32 (.Ok none)), releasedState before) []
      (pairPool before.generation (unlockResume (.Ok none)) retryProgram, retryState before) := by
  apply one_steps (releasedState before) before.generation ⟨rfl, rfl⟩
  rw [retry_start_focus]
  exact advance_retry _ _

theorem retry_read_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (unlockResume (.Ok none)) retryProgram, retryState before) []
      (pairPool before.generation (unlockResume (.Ok none)) (retryResume (.Ok (0#32, none))), retryReadState before) := by
  apply one_step (retryState before) before.generation ⟨rfl, rfl⟩
  rw [retry_focus]
  exact retry_read _ _ (clear_free _ _ _ _ (retry_reservations before))

theorem win_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (unlockResume (.Ok none)) (retryResume (.Ok (0#32, none))), retryReadState before) []
      (pairPool before.generation (unlockResume (.Ok none)) winProgram, retryReadState before) := by
  have steps : NodeSteps Devices.bus (othersReserved (retryReadState before).reservations 1) 1
      (retryReadState before).image (retryResume (.Ok (0#32, none))) (focus (retryReadState before) 1)
      winProgram (retryReadLocal (Devices.reset before.devices)) := by
    rw [retry_read_focus]
    exact win_prefix _ _
  obtain ⟨n, framed⟩ := one_steps (retryReadState before) before.generation ⟨rfl, rfl⟩
    (unlockResume (.Ok none)) _ _ _ steps
  have same : writeBack (retryReadState before) 1 (retryReadLocal (Devices.reset before.devices)) =
      retryReadState before := by rw [← retry_read_focus, writeBack_focus]
  rw [same] at framed
  exact ⟨n, framed⟩

theorem win_commit_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (unlockResume (.Ok none)) winProgram, retryReadState before) []
      (pairPool before.generation (unlockResume (.Ok none)) (winResume (.Ok none)), wonState before) := by
  apply one_step (retryReadState before) before.generation ⟨rfl, rfl⟩
  rw [retry_read_focus]
  exact win_commit _ _ (win_free before)

theorem increment_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (unlockResume (.Ok none)) (winResume (.Ok none)), wonState before) []
      (pairPool before.generation (unlockResume (.Ok none)) incrementProgram, incrementState before) := by
  apply one_steps (wonState before) before.generation ⟨rfl, rfl⟩
  rw [won_focus]
  exact advance_increment _ _

theorem increment_commit_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (unlockResume (.Ok none)) incrementProgram, incrementState before) []
      (pairPool before.generation (unlockResume (.Ok none)) (incrementResume (.Ok none)), incrementedState before) := by
  apply one_step (incrementState before) before.generation ⟨rfl, rfl⟩
  rw [increment_focus]
  exact increment_commit _ _ (clear_free _ _ _ _ (increment_reservations before))

theorem release_prefix_pool (before : State) :
    ∃ n, PoolSteps SpinlockImage.image n
      (pairPool before.generation (unlockResume (.Ok none)) (incrementResume (.Ok none)), incrementedState before) []
      (pairPool before.generation (unlockResume (.Ok none)) releaseProgram, releaseState before) := by
  apply one_steps (incrementedState before) before.generation ⟨rfl, rfl⟩
  rw [incremented_focus]
  exact advance_release _ _

theorem release_commit_pool (before : State) :
    PoolStep SpinlockImage.image
      (pairPool before.generation (unlockResume (.Ok none)) releaseProgram, releaseState before) []
      (finalPool before.generation, finalState before) := by
  apply one_step (releaseState before) before.generation ⟨rfl, rfl⟩
  rw [release_focus]
  exact release_commit _ _ (clear_free _ _ _ _ (release_reservations before))

/-- Five further real appends, one successful exclusive read, and the actual
failed-swap retry and counter instructions. -/
theorem finish_schedule (before : State) :
    ∃ n, 6 ≤ n ∧ PoolSteps SpinlockImage.image n
      (blockedPool before.generation, unlockReady before) []
      (finalPool before.generation, finalState before) := by
  obtain ⟨n0, retryPrefix⟩ := retry_prefix_pool before
  obtain ⟨n1, winPrefix⟩ := win_prefix_pool before
  obtain ⟨n2, incrementPrefix⟩ := increment_prefix_pool before
  obtain ⟨n3, releasePrefix⟩ := release_prefix_pool before
  have a := pool_trans (single (failed_commit_pool before)) (single (first_release_pool before))
  have b := pool_trans a retryPrefix
  have c := pool_trans b (single (retry_read_pool before))
  have d := pool_trans c winPrefix
  have e := pool_trans d (single (win_commit_pool before))
  have f := pool_trans e incrementPrefix
  have g := pool_trans f (single (increment_commit_pool before))
  have h := pool_trans g releasePrefix
  have result := pool_trans h (single (release_commit_pool before))
  exact ⟨1 + 1 + n0 + 1 + n1 + 1 + n2 + 1 + n3 + 1, by omega, result⟩

/-- The complete schedule starts from actual power-on. Both earlier blocked
steps occur in the composed prefixes, before either corresponding retry. -/
theorem powerOn_seven_messages (before : State) (off : before.power = false) :
    ∃ n, 9 < n ∧ PoolSteps SpinlockImage.image n ([.power], before) [.powerOn]
      (finalPool before.generation, finalState before) := by
  obtain ⟨n, firstPositive, first⟩ := powerOn_unlock_conflict before off
  obtain ⟨m, nextPositive, next⟩ := finish_schedule before
  exact ⟨n + m, by omega, pool_trans first next⟩

/-- Expose the two conflict checkpoints and their actual blocked transitions
on the same composed execution, with all generated continuations retained. -/
theorem scheduled_conflicts (before : State) (off : before.power = false) :
    ∃ n₀ n₁ n₂,
      PoolSteps SpinlockImage.image n₀ ([.power], before) [.powerOn]
        (conflictPool before.generation, afterReadZero before) ∧
      PoolStep SpinlockImage.image (conflictPool before.generation, afterReadZero before) []
        (conflictPool before.generation, afterReadZero before) ∧
      PoolSteps SpinlockImage.image n₁ (conflictPool before.generation, afterReadZero before) []
        (blockedPool before.generation, unlockReady before) ∧
      PoolStep SpinlockImage.image (blockedPool before.generation, unlockReady before) []
        (blockedPool before.generation, unlockReady before) ∧
      PoolSteps SpinlockImage.image n₂ (blockedPool before.generation, unlockReady before) []
        (finalPool before.generation, finalState before) := by
  obtain ⟨n₀, _, first⟩ := powerOn_first_conflict before off
  obtain ⟨n₁, _, held⟩ := first_to_unlock_conflict before
  obtain ⟨n₂, _, finish⟩ := finish_schedule before
  exact ⟨n₀, n₁, n₂, first, one_blocked_pool before, held, unlock_blocked_pool before, finish⟩

theorem concrete_seven_messages (devices : Devices.State) :
    ∃ n, 9 < n ∧ PoolSteps SpinlockImage.image n ([.power], initialState devices) [.powerOn]
      (finalPool 0, finalState (initialState devices)) :=
  powerOn_seven_messages (initialState devices) rfl

end MachCSL.Machine.SpinlockWitnessRelease
