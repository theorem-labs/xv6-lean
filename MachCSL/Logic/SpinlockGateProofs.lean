import MachCSL.Logic.SpinlockIntegrationProofs
import MachCSL.Machine.SpinlockWitnessHolderProofs

namespace MachCSL.Logic.SpinlockIntegration
open MachCSL.Machine MachCSL.Memory SpinlockWitnessRelease
attribute [local instance] SpinlockWitness.platform

/-- One fully concrete gate witness: the actual holder checkpoint and final
seven-write endpoint are on the same recorded schedule. Native safety and
unique annotation certify that execution, and holder exclusion is inhabited.
The other six CPUs are unscheduled, and unlock continuations remain intact. -/
theorem complete_gate (devices : Devices.State) :
    let before := SpinlockWitness.initialState devices
    ∃ preSchedule suffix middle final,
      2 < preSchedule.length ∧ 9 ≤ suffix.length ∧
      SpinlockPool.ScheduledSteps preSchedule ([(.power, .worker)], before) middle ∧
      SpinlockPool.Holds middle 0 ∧
      (∀ cpu, SpinlockPool.Holds middle cpu → cpu = 0) ∧
      SpinlockPool.ScheduledSteps suffix middle final ∧
      AnnotatedPool.eraseConfig final = (finalPool 0, finalState before) ∧
      (∀ other, SpinlockPool.ScheduledSteps (preSchedule ++ suffix)
        ([(.power, .worker)], before) other → other = final) ∧
      CertifiedRun (preSchedule.length + suffix.length) before [.powerOn]
        (finalPool 0, finalState before) ∧
      readBytes (finalState before).memory SpinlockImage.lockAddress 4 = some 0#32 ∧
      readBytes (finalState before).memory SpinlockImage.counterAddress 4 = some 2#32 ∧
      (finalState before).log.map Message.author = [0, 0, 1, 0, 1, 1, 1] ∧
      (∀ cpu, (finalState before).reservations cpu = none) ∧
      (finalPool 0).length = 12 ∧
      (finalState before).devices.virtio.v_disk = devices.virtio.v_disk := by
  let before := SpinlockWitness.initialState devices
  obtain ⟨n, m, preSchedule, suffix, middle, final, positive, positive', preLength,
    suffixLength, preEvents, suffixEvents, middleEq, finalEq, first, rest, both,
    middleInv, held, finalInv⟩ := SpinlockWitnessHolder.annotated_holder before rfl rfl
  have events : SpinlockPool.scheduleObservations (preSchedule ++ suffix) = [.powerOn] := by
    change (preSchedule ++ suffix).flatMap SpinlockPool.ScheduledEvent.observations = _
    rw [List.flatMap_append]
    change SpinlockPool.scheduleObservations preSchedule ++ SpinlockPool.scheduleObservations suffix = _
    rw [preEvents, suffixEvents]
    rfl
  have actual := AnnotatedPool.erase_steps SpinlockImage.image SpinlockPool.Transition
    (SpinlockPool.scheduled_steps_erase both)
  rw [List.length_append, events, finalEq] at actual
  have certified : CertifiedRun (preSchedule.length + suffix.length) before [.powerOn]
      (finalPool 0, finalState before) := by
    refine ⟨actual, SpinlockMachineSafety.safe before rfl rfl _ _ _ _ actual, ?_⟩
    exact ⟨preSchedule ++ suffix, final, List.length_append, events, finalEq, both, finalInv,
      fun other run => SpinlockPool.scheduled_steps_functional run both,
      fun cpu other left right => SpinlockPool.holder_exclusion finalInv left right⟩
  exact ⟨preSchedule, suffix, middle, final, by omega, by omega, first, held,
    fun cpu other => SpinlockPool.holder_exclusion middleInv other held, rest, finalEq,
    fun other run => SpinlockPool.scheduled_steps_functional run both, certified,
    (final_values before).1, (final_values before).2, final_log_authors before,
    final_reservations before, final_pool_length 0, final_disk before⟩

end MachCSL.Logic.SpinlockIntegration
