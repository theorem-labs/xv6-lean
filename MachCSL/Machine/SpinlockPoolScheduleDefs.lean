import MachCSL.Machine.SpinlockPoolCoverProofs
import MachCSL.Machine.AnnotatedPoolProofs

namespace MachCSL.Machine.SpinlockPool

/-- A fixed actual scheduler choice and its full observable/physical outcome.
Occurrence indices are explicit: erased configuration traces need not identify
which of several equal worker expressions was selected. -/
structure ScheduledEvent where
  index : Nat
  result : Expr
  state : State
  observations : List Observation
  forks : List Expr

/-- The graph annotation of one actual event at the recorded pool occurrence. -/
inductive ScheduledStep [Platform] (event : ScheduledEvent) : Config → Config → Prop where
  | atomic {e label g label' annotatedForks}
      (actual : Step SpinlockImage.image e g event.observations event.result event.state event.forks)
      (annotation : Transition (e, label) g event.observations (event.result, label') event.state annotatedForks)
      (forks : AnnotatedPool.erase annotatedForks = event.forks)
      (left right : Pool) (index : left.length = event.index) :
      ScheduledStep event (left ++ (e, label) :: right, g)
        (left ++ (event.result, label') :: right ++ annotatedForks, event.state)

inductive ScheduledSteps [Platform] : List ScheduledEvent → Config → Config → Prop where
  | refl (config : Config) : ScheduledSteps [] config config
  | cons {event schedule before middle after}
      (first : ScheduledStep event before middle) (rest : ScheduledSteps schedule middle after) :
      ScheduledSteps (event :: schedule) before after

def scheduleObservations (schedule : List ScheduledEvent) : List Observation :=
  schedule.flatMap ScheduledEvent.observations

end MachCSL.Machine.SpinlockPool
