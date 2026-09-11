import MachCSL.Machine.SpinlockPoolScheduleProofs
import MachCSL.Machine.SpinlockPoolBoundaryProofs

namespace MachCSL.Machine.SpinlockPool

/-- Every actual finite machine run has a unique annotation for its recorded
occurrence-indexed schedule. States, observations, fork order and step count
are preserved; the caller supplies no ghost resources or preservation premise. -/
theorem annotate_run [Platform] (initialState : State)
    (off : initialState.power = false) (zero : initialState.generation = 0)
    (n : Nat) (after : Configuration) (observations : List Observation)
    (steps : PoolSteps SpinlockImage.image n ([.power], initialState) observations after) :
    ∃ schedule annotated,
      schedule.length = n ∧ scheduleObservations schedule = observations ∧
      AnnotatedPool.eraseConfig annotated = after ∧
      ScheduledSteps schedule ([(.power, .worker)], initialState) annotated ∧
      PoolInv annotated ∧
      (∀ other, ScheduledSteps schedule ([(.power, .worker)], initialState) other → other = annotated) ∧
      (∀ cpu other, Holds annotated cpu → Holds annotated other → cpu = other) := by
  obtain ⟨annotated, erased, annotatedSteps, inv⟩ :=
    AnnotatedPool.lift_steps SpinlockImage.image Transition PoolInv covers
      ([(.power, .worker)], initialState) after n observations (initial initialState off zero) steps
  obtain ⟨schedule, length, events, scheduled⟩ := steps_have_schedule annotatedSteps
  exact ⟨schedule, annotated, length, events, erased, scheduled, inv,
    fun other run => scheduled_steps_functional run scheduled,
    fun cpu other left right => holder_exclusion inv left right⟩

/-- Exclusion for every realization of every actual recorded schedule from
the powered-off initial machine, throughout the full event-defined window. -/
theorem scheduled_holder_exclusion [Platform] (initialState : State)
    (off : initialState.power = false) (zero : initialState.generation = 0)
    {schedule : List ScheduledEvent} {after : Config}
    (steps : ScheduledSteps schedule ([(.power, .worker)], initialState) after)
    {cpu other : CPU} (left : Holds after cpu) (right : Holds after other) : cpu = other :=
  holder_exclusion (scheduled_steps_preserve (initial initialState off zero) steps) left right

/-- The physical-PC corollary is restricted to completed-instruction
boundaries. No mid-instruction PC assertion or extra boot premise is used. -/
theorem scheduled_boundary_exclusion [Platform] (initialState : State)
    (off : initialState.power = false) (zero : initialState.generation = 0)
    {schedule : List ScheduledEvent} {pool : Pool} {g : State}
    (steps : ScheduledSteps schedule ([(.power, .worker)], initialState) (pool, g))
    (on : g.power = true) {cpu other : CPU} {c d : Cursor} {i j : Fin 17}
    (left : (Expr.hart g.generation cpu (.pure ()), Label.hart c) ∈ pool)
    (right : (Expr.hart g.generation other (.pure ()), Label.hart d) ∈ pool)
    (leftPC : g.registers cpu .PC = SpinlockImage.instructionAddress i)
    (rightPC : g.registers other .PC = SpinlockImage.instructionAddress j)
    (leftBody : 10 ≤ i.val ∧ i.val ≤ 13) (rightBody : 10 ≤ j.val ∧ j.val ≤ 13) : cpu = other :=
  boundary_exclusion (scheduled_steps_preserve (initial initialState off zero) steps) on
    left right leftPC rightPC leftBody rightBody

theorem erased_hart_label {pool : Pool} {g : State} {gen : Nat} {cpu : CPU} {program : SailM Unit}
    (shape : Shape pool g) (member : Expr.hart gen cpu program ∈ AnnotatedPool.erase pool) :
    ∃ c, (Expr.hart gen cpu program, Label.hart c) ∈ pool := by
  obtain ⟨⟨e, label⟩, member, same⟩ := List.mem_map.mp member
  change e = Expr.hart gen cpu program at same
  subst e
  cases label with
  | hart c => exact ⟨c, member⟩
  | worker => exact False.elim (shape.labels _ _ member)

/-- Direct physical-machine boundary exclusion for every actual PoolSteps
run. Clients supply only real expression membership and register PCs; labels,
the schedule and the invariant are constructed internally. -/
theorem reachable_boundary_exclusion [Platform] (initialState : State)
    (off : initialState.power = false) (zero : initialState.generation = 0)
    (n : Nat) (pool : List Expr) (g : State) (observations : List Observation)
    (steps : PoolSteps SpinlockImage.image n ([.power], initialState) observations (pool, g))
    (on : g.power = true) {cpu other : CPU} {i j : Fin 17}
    (left : Expr.hart g.generation cpu (.pure ()) ∈ pool)
    (right : Expr.hart g.generation other (.pure ()) ∈ pool)
    (leftPC : g.registers cpu .PC = SpinlockImage.instructionAddress i)
    (rightPC : g.registers other .PC = SpinlockImage.instructionAddress j)
    (leftBody : 10 ≤ i.val ∧ i.val ≤ 13) (rightBody : 10 ≤ j.val ∧ j.val ≤ 13) : cpu = other := by
  obtain ⟨schedule, ⟨annotated, finalState⟩, length, events, erased, run, inv, unique, exclusion⟩ :=
    annotate_run initialState off zero n (pool, g) observations steps
  have state : finalState = g := congrArg Prod.snd erased
  subst finalState
  have erasedPool : AnnotatedPool.erase annotated = pool := congrArg Prod.fst erased
  obtain ⟨c, leftLabel⟩ := erased_hart_label inv.1 (by rw [erasedPool]; exact left)
  obtain ⟨d, rightLabel⟩ := erased_hart_label inv.1 (by rw [erasedPool]; exact right)
  exact boundary_exclusion inv on leftLabel rightLabel leftPC rightPC leftBody rightBody

end MachCSL.Machine.SpinlockPool
