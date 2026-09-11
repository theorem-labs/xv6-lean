import MachCSL.Machine.SpinlockPoolScheduleDefs

namespace MachCSL.Machine.SpinlockPool

theorem scheduled_step_functional [Platform] {event : ScheduledEvent} {before firstAfter secondAfter : Config}
    (first : ScheduledStep event before firstAfter) (second : ScheduledStep event before secondAfter) :
    firstAfter = secondAfter := by
  cases first with
  | @atomic e label g labelA forksA actualA annotationA forkEqA leftA rightA indexA =>
    generalize source : (leftA ++ (e, label) :: rightA, g) = config at second
    cases second with
    | @atomic eB labelB gB labelB' forksB actualB annotationB forkEqB leftB rightB indexB =>
      have state : g = gB := congrArg Prod.snd source
      subst gB
      have pools : leftA ++ (e, label) :: rightA = leftB ++ (eB, labelB) :: rightB :=
        congrArg Prod.fst source
      obtain ⟨rfl, tails⟩ := List.append_inj pools (indexA.trans indexB.symm)
      obtain ⟨entries, rfl⟩ := List.cons.inj tails
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj entries
      obtain ⟨rfl, rfl⟩ := transition_functional annotationA annotationB
      rfl

theorem scheduled_steps_functional [Platform] {schedule : List ScheduledEvent} {before firstAfter secondAfter : Config}
    (first : ScheduledSteps schedule before firstAfter) (second : ScheduledSteps schedule before secondAfter) :
    firstAfter = secondAfter := by
  induction first generalizing secondAfter with
  | refl config => cases second; rfl
  | cons first rest ih =>
    cases second with
    | cons first' rest' =>
      have same := scheduled_step_functional first first'
      cases same
      exact ih rest'

theorem scheduled_step_preserves [Platform] {event : ScheduledEvent} {before after : Config}
    (inv : PoolInv before) (step : ScheduledStep event before after) : PoolInv after := by
  cases step with
  | atomic actual annotation forks left right index =>
    obtain ⟨label', annotatedForks, erase, chosen, preserved⟩ := covers left right _ _ _ _ _ _ _ inv actual
    obtain ⟨rfl, rfl⟩ := transition_functional annotation chosen
    exact preserved

theorem scheduled_steps_preserve [Platform] {schedule : List ScheduledEvent} {before after : Config}
    (inv : PoolInv before) (steps : ScheduledSteps schedule before after) : PoolInv after := by
  induction steps with
  | refl config => exact inv
  | cons first rest ih => exact ih (scheduled_step_preserves inv first)

theorem scheduled_step_erases [Platform] {event : ScheduledEvent} {before after : Config}
    (step : ScheduledStep event before after) :
    AnnotatedPool.AStep SpinlockImage.image Transition before event.observations after := by
  cases step with
  | atomic actual annotation forks left right index =>
    exact .atomic (by simpa only [forks] using actual) annotation left right

theorem scheduled_steps_erase [Platform] {schedule : List ScheduledEvent} {before after : Config}
    (steps : ScheduledSteps schedule before after) :
    AnnotatedPool.ASteps SpinlockImage.image Transition schedule.length before (scheduleObservations schedule) after := by
  induction steps with
  | refl config => exact .refl config
  | cons first rest ih => exact .cons (scheduled_step_erases first) ih

theorem step_has_schedule [Platform] {before after : Config} {observations : List Observation}
    (step : AnnotatedPool.AStep SpinlockImage.image Transition before observations after) :
    ∃ event, event.observations = observations ∧ ScheduledStep event before after := by
  cases step with
  | @atomic e label g observations e' label' g' forks actual annotation left right =>
    exact ⟨⟨left.length, e', g', observations, AnnotatedPool.erase forks⟩, rfl,
      .atomic actual annotation rfl left right rfl⟩

theorem steps_have_schedule [Platform] {n : Nat} {before after : Config} {observations : List Observation}
    (steps : AnnotatedPool.ASteps SpinlockImage.image Transition n before observations after) :
    ∃ schedule, schedule.length = n ∧ scheduleObservations schedule = observations ∧ ScheduledSteps schedule before after := by
  induction steps with
  | refl config => exact ⟨[], rfl, rfl, .refl config⟩
  | cons first rest ih =>
    obtain ⟨event, events, selected⟩ := step_has_schedule first
    obtain ⟨schedule, length, observations, annotated⟩ := ih
    exact ⟨event :: schedule, by simp [length], by simp [scheduleObservations, events, ← observations],
      .cons selected annotated⟩

end MachCSL.Machine.SpinlockPool
