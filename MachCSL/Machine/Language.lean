import MachCSL.Machine.Power
import MachCSL.Machine.DiskSteps
import Iris.ProgramLogic.Language

/-! Concrete CPU/device/power interleaving language, porting the five arms
of `iris/RiscvLang.v:prim_step`. The image parameter is shared by the small
machine-code gate and eventual xv6 instantiation. No safety/adequacy theorem
is implied by constructing this language instance. -/
namespace MachCSL.Machine
open Memory

inductive Step [Platform] (image : BootImage) :
    Expr → State → List Observation → Expr → State → List Expr → Prop where
  | hartLive (generation cpu m m' g g')
      (live : ThreadLive g generation) (step : HartStep g cpu m m' g') :
      Step image (.hart generation cpu m) g [] (.hart generation cpu m') g' []
  | hartDead (generation cpu m g) (dead : ¬ ThreadLive g generation) :
      Step image (.hart generation cpu m) g [] (.hart generation cpu m) g []
  | uartLive (generation g observations next)
      (live : ThreadLive g generation) (step : UartStep g.devices observations next) :
      Step image (.uart generation) g observations (.uart generation) { g with devices := next } []
  | uartDead (generation g) (dead : ¬ ThreadLive g generation) :
      Step image (.uart generation) g [] (.uart generation) g []
  | diskLive (generation g next writes log)
      (live : ThreadLive g generation) (step : DiskStep g.devices g.memory next writes)
      (publish : (writes = empty ∧ log = g.log) ∨
        (writes ≠ empty ∧ log = g.log ++ [⟨writes, diskAgent⟩]))
      (reserved : ∀ a, allReserved g.reservations a → overlay writes g.memory a = g.memory a) :
      Step image (.disk generation) g [] (.disk generation)
        { g with memory := overlay writes g.memory, devices := next, log := log } []
  | diskDead (generation g) (dead : ¬ ThreadLive g generation) :
      Step image (.disk generation) g [] (.disk generation) g []
  | plicLive (generation g registers)
      (live : ThreadLive g generation) (step : PlicStep g.devices g.registers registers) :
      Step image (.plic generation) g [] (.plic generation) { g with registers := registers } []
  | plicDead (generation g) (dead : ¬ ThreadLive g generation) :
      Step image (.plic generation) g [] (.plic generation) g []
  | power (g observations next forks) (step : PowerStep image g observations next forks) :
      Step image .power g observations .power next forks

/-- Explicit instance value: clients choose one fixed boot image for the run. -/
@[reducible] def language [Platform] (image : BootImage) :
    Iris.ProgramLogic.Language Expr State Observation Empty where
  primStep before observations after := Step image before.1 before.2 observations
    after.1 after.2.1 after.2.2
  toVal _ := none
  ofVal := Empty.elim
  coe_of_toVal_eq_some := by intros; contradiction
  toVal_coe := by intro v; cases v
  val_stuck := by intros; rfl

theorem live_error_stuck [Platform] (image : BootImage) (g : State) (generation cpu)
    (error : _root_.Sail.Error exception) (k : Empty → SailM Unit)
    (live : ThreadLive g generation) (observations next g' forks) :
    ¬ Step image (.hart generation cpu (.impure (.error error) k)) g observations next g' forks := by
  intro step
  cases step with
  | hartDead _ _ _ _ dead => exact dead live
  | hartLive _ _ _ _ _ _ _ h =>
    obtain ⟨after, impossible, _⟩ := h
    exact impossible

theorem power_can_step [Platform] (image : BootImage) (g : State) :
    ∃ observations next forks, Step image .power g observations .power next forks := by
  obtain ⟨observations, next, forks, step⟩ := power_reducible image g
  exact ⟨observations, next, forks, .power _ _ _ _ step⟩

end MachCSL.Machine
