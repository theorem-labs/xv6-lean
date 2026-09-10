import MachCSL.Machine.Invariants

/-! Lifting structural invariants through Iris's actual thread-pool semantics.
These results quantify over arbitrary finite schedules, including thread forks.
They do not assert that every hart is reducible. -/
namespace MachCSL.Machine

abbrev Configuration := List Expr × State

abbrev PoolStep [Platform] (image : BootImage) :=
  @Iris.ProgramLogic.Language.Step Expr Empty State Observation (language image)

abbrev PoolSteps [Platform] (image : BootImage) :=
  @Iris.ProgramLogic.Language.NSteps Expr Empty State Observation (language image)

theorem poolStep_invariant [Platform] (image : BootImage) (P : State → Prop)
    (preserves : ∀ e e' g g' observations forks,
      P g → Step image e g observations e' g' forks → P g')
    (before after : Configuration) (observations)
    (initial : P before.2) (step : PoolStep image before observations after) : P after.2 := by
  cases step with
  | atomic h left right => exact preserves _ _ _ _ _ _ initial h

theorem poolSteps_invariant [Platform] (image : BootImage) (P : State → Prop)
    (preserves : ∀ e e' g g' observations forks,
      P g → Step image e g observations e' g' forks → P g')
    (n : Nat) (before after : Configuration) (observations)
    (initial : P before.2) (steps : PoolSteps image n before observations after) : P after.2 := by
  induction steps with
  | refl => exact initial
  | cons first rest ih =>
    exact ih (poolStep_invariant image P preserves _ _ _ initial first)

theorem reachable_memory_ok [Platform] (image : BootImage) (n : Nat)
    (before after : Configuration) (observations) (initial : MemoryOK before.2)
    (steps : PoolSteps image n before observations after) : MemoryOK after.2 :=
  poolSteps_invariant image MemoryOK (step_memory_ok image) _ _ _ _ initial steps

theorem reachable_reservations_ok [Platform] (image : BootImage) (n : Nat)
    (before after : Configuration) (observations) (initial : ReservationsOK before.2)
    (steps : PoolSteps image n before observations after) : ReservationsOK after.2 :=
  poolSteps_invariant image ReservationsOK (step_reservations_ok image) _ _ _ _ initial steps

theorem reachable_generation_monotone [Platform] (image : BootImage) (n : Nat)
    (before after : Configuration) (observations)
    (steps : PoolSteps image n before observations after) :
    before.2.generation ≤ after.2.generation := by
  apply poolSteps_invariant image (fun g => before.2.generation ≤ g.generation)
      (fun e e' g g' obs forks initial step =>
        Nat.le_trans initial (step_generation_monotone image e e' g g' obs forks step))
      n before after observations (Nat.le_refl _) steps

end MachCSL.Machine
