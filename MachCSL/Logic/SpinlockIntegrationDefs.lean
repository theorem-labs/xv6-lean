import MachCSL.Logic.MachineAdequacyDefs
import MachCSL.Machine.SpinlockPoolScheduleDefs

namespace MachCSL.Logic.SpinlockIntegration
open MachCSL.Machine MachCSL.Memory

/-- One actual execution, with native safety and its unique annotation for
the recorded occurrence-indexed schedule. No software contract is a field. -/
structure CertifiedRun [Platform] (n : Nat) (initial : State)
    (events : List Observation) (after : Configuration) : Prop where
  steps : PoolSteps SpinlockImage.image n ([.power], initial) events after
  safe : MachineAdequacy.SafeConfiguration SpinlockImage.image after.1 after.2 events
  annotation : ∃ schedule annotated,
    schedule.length = n ∧ SpinlockPool.scheduleObservations schedule = events ∧
    AnnotatedPool.eraseConfig annotated = after ∧
    SpinlockPool.ScheduledSteps schedule ([(.power, .worker)], initial) annotated ∧
    SpinlockPool.PoolInv annotated ∧
    (∀ other, SpinlockPool.ScheduledSteps schedule ([(.power, .worker)], initial) other →
      other = annotated) ∧
    (∀ cpu other, SpinlockPool.Holds annotated cpu → SpinlockPool.Holds annotated other →
      cpu = other)

end MachCSL.Logic.SpinlockIntegration
