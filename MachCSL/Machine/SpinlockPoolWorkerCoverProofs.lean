import MachCSL.Machine.SpinlockPoolWorkerFrames
import MachCSL.Machine.SpinlockPoolPowerOffProofs

namespace MachCSL.Machine.SpinlockPool

/-- The exact global coverage conclusion at one selected occurrence. The
selected entry remains visible, including its label, left and right contexts. -/
def Covered [Platform] (left right : Pool) (e : Expr) (label : Label) (g : State)
    (observations : List Observation) (e' : Expr) (g' : State) (forks : List Expr) : Prop :=
  ∃ label' annotatedForks,
    AnnotatedPool.erase annotatedForks = forks ∧
    Transition (e, label) g observations (e', label') g' annotatedForks ∧
    PoolInv (left ++ (e', label') :: right ++ annotatedForks, g')

theorem cover_uart [Platform] {left right : Pool} {gen : Nat} {g g' : State}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.uart gen, .worker) :: right, g))
    (step : Step SpinlockImage.image (.uart gen) g observations e' g' forks) :
    Covered left right (.uart gen) .worker g observations e' g' forks := by
  obtain ⟨rfl, rfl, frame⟩ := uart_step_frame step inv
  exact ⟨.worker, [], rfl, .uart, by simpa only [List.append_nil] using frame⟩

theorem cover_plic [Platform] {left right : Pool} {gen : Nat} {g g' : State}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.plic gen, .worker) :: right, g))
    (step : Step SpinlockImage.image (.plic gen) g observations e' g' forks) :
    Covered left right (.plic gen) .worker g observations e' g' forks := by
  obtain ⟨rfl, rfl, rfl, frame⟩ := plic_step_frame step inv
  exact ⟨.worker, [], rfl, .plic, by simpa only [List.append_nil] using frame⟩

theorem cover_disk [Platform] {left right : Pool} {gen : Nat} {g g' : State}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.disk gen, .worker) :: right, g))
    (step : Step SpinlockImage.image (.disk gen) g observations e' g' forks) :
    Covered left right (.disk gen) .worker g observations e' g' forks := by
  obtain ⟨rfl, rfl, rfl, rfl, frame⟩ := disk_step_frame step inv
  exact ⟨.worker, [], rfl, .disk, by simpa only [List.append_nil] using frame⟩

theorem cover_stale_hart [Platform] {left right : Pool} {gen : Nat} {cpu : CPU}
    {program : SailM Unit} {c : Cursor} {g g' : State}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.hart gen cpu program, .hart c) :: right, g))
    (dead : ¬ ThreadLive g gen)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations e' g' forks) :
    Covered left right (.hart gen cpu program) (.hart c) g observations e' g' forks := by
  cases step with
  | hartDead =>
    exact ⟨.hart c, [], rfl, .stale dead, by simpa only [List.append_nil] using inv⟩
  | hartLive generation cpu m m' g g' live action => exact False.elim (dead live)

theorem cover_power_off [Platform] {left right : Pool} {g g' : State}
    {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.power, .worker) :: right, g))
    (step : Step SpinlockImage.image .power g [.powerOff] e' g' forks) :
    Covered left right .power .worker g [.powerOff] e' g' forks := by
  cases step with
  | power g observations next forks action =>
    cases action with
    | off on =>
      exact ⟨.worker, [], rfl, .powerOff on,
        by simpa only [List.append_nil] using power_off_frame inv⟩

end MachCSL.Machine.SpinlockPool
