import MachCSL.Machine.Language
import MachCSL.Machine.NodeInvariants

/-! Pure state invariants for every CPU/device/power transition. These cover
memory bookkeeping and reservations, including wild DMA. They do not establish
kernel integrity, queue well-formedness, reducibility of harts, or filesystem safety. -/
namespace MachCSL.Machine
open Memory

theorem step_memory_ok [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (observations forks) (initial : MemoryOK g)
    (step : Step image e g observations e' g' forks) : MemoryOK g' := by
  cases step with
  | hartLive generation cpu m m' g g' live h => exact hart_memory_ok _ _ _ _ _ initial h
  | hartDead => exact initial
  | uartLive => exact initial
  | uartDead => exact initial
  | diskLive generation g next writes log live h publish reserved =>
    obtain ⟨flatEq, bounds, coverage⟩ := initial
    rcases publish with ⟨rfl, rfl⟩ | ⟨nonempty, rfl⟩
    · exact ⟨by simpa using flatEq, bounds, coverage⟩
    · refine ⟨?_, ?_, coverage⟩
      · dsimp
        rw [flat_append, flatEq]
      · intro cpu
        have := bounds cpu
        simpa using Nat.le_trans this (Nat.le_succ g.log.length)
  | diskDead => exact initial
  | plicLive => exact initial
  | plicDead => exact initial
  | power g observations next forks h =>
    cases h with
    | off => exact initial
    | on off next shape => exact boot_memory_ok image _ shape.2.2

theorem step_reservations_ok [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (observations forks) (initial : ReservationsOK g)
    (step : Step image e g observations e' g' forks) : ReservationsOK g' := by
  cases step with
  | hartLive generation cpu m m' g g' live h => exact hart_reservations_ok _ _ _ _ _ initial h
  | hartDead => exact initial
  | uartLive => exact initial
  | uartDead => exact initial
  | diskLive generation g next writes log live h publish reserved =>
    intro cpu r hr a b hb
    change overlay writes g.memory a = some b
    rw [reserved a ⟨cpu, r, hr, b, hb⟩]
    exact initial cpu r hr a b hb
  | diskDead => exact initial
  | plicLive => exact initial
  | plicDead => exact initial
  | power g observations next forks h =>
    cases h with
    | off => exact initial
    | on off next shape => exact boot_reservations_ok image _ shape.2.2

theorem step_generation_monotone [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (observations forks) (step : Step image e g observations e' g' forks) :
    g.generation ≤ g'.generation := by
  cases step with
  | hartLive generation cpu m m' g g' live h =>
    rw [hart_generation _ _ _ _ _ h]
    exact Nat.le_refl _
  | hartDead => exact Nat.le_refl _
  | uartLive => exact Nat.le_refl _
  | uartDead => exact Nat.le_refl _
  | diskLive => exact Nat.le_refl _
  | diskDead => exact Nat.le_refl _
  | plicLive => exact Nat.le_refl _
  | plicDead => exact Nat.le_refl _
  | power g observations next forks h =>
    cases h with
    | off => exact Nat.le_succ _
    | on off next shape =>
      rw [shape.1]
      exact Nat.le_refl _

end MachCSL.Machine
