import MachCSL.Logic.SpinlockIntegrationDefs
import MachCSL.Logic.SpinlockMachineSafetyProofs
import MachCSL.Machine.SpinlockPoolReachability
import MachCSL.Machine.SpinlockWitnessReleasePoolProofs

namespace MachCSL.Logic.SpinlockIntegration
open MachCSL.Machine MachCSL.Memory

/-- Every actual finite execution from the powered-off, generation-zero
machine satisfies both parts of the integration gate. -/
theorem certify [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0)
    (n : Nat) (events : List Observation) (after : Configuration)
    (steps : PoolSteps SpinlockImage.image n ([.power], initial) events after) :
    CertifiedRun n initial events after :=
  ⟨steps, SpinlockMachineSafety.safe initial off zero n events after.1 after.2 steps,
    SpinlockPool.annotate_run initial off zero n after events steps⟩

open SpinlockWitnessRelease
attribute [local instance] SpinlockWitness.platform

/-- The seven-write positive witness has the same actual-run safety and
unique operational annotation as arbitrary executions. The endpoint is just
after the successful unlock writes, with their continuations retained. -/
theorem seven_messages_certified (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) :
    ∃ n, 9 < n ∧
      CertifiedRun n initial [.powerOn] (finalPool initial.generation, finalState initial) ∧
      readBytes (finalState initial).memory SpinlockImage.lockAddress 4 = some 0#32 ∧
      readBytes (finalState initial).memory SpinlockImage.counterAddress 4 = some 2#32 ∧
      (finalState initial).log.map Message.author = [0, 0, 1, 0, 1, 1, 1] ∧
      (∀ cpu, (finalState initial).reservations cpu = none) ∧
      (finalPool initial.generation).length = 12 ∧
      (finalState initial).devices.virtio.v_disk = initial.devices.virtio.v_disk := by
  obtain ⟨n, positive, steps⟩ := powerOn_seven_messages initial off
  exact ⟨n, positive, certify initial off zero n [.powerOn] _ steps,
    (final_values initial).1, (final_values initial).2, final_log_authors initial,
    final_reservations initial, final_pool_length initial.generation, final_disk initial⟩

/-- The combined witness has inhabited initial conditions for every actual
device state, with explicit pure platform predicates and no logical premise. -/
theorem concrete_certified_run (devices : Devices.State) :
    ∃ n, 9 < n ∧ CertifiedRun n (SpinlockWitness.initialState devices) [.powerOn]
      (finalPool 0, finalState (SpinlockWitness.initialState devices)) := by
  obtain ⟨n, positive, certified, _⟩ :=
    seven_messages_certified (SpinlockWitness.initialState devices) rfl rfl
  exact ⟨n, positive, certified⟩

end MachCSL.Logic.SpinlockIntegration
