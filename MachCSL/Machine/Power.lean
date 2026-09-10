import MachCSL.Machine.Boot
import MachCSL.Machine.DeviceSteps

namespace MachCSL.Machine

inductive Expr where
  | hart (generation : Nat) (cpu : CPU) (program : SailM Unit)
  | uart (generation : Nat)
  | disk (generation : Nat)
  | plic (generation : Nat)
  | power

def loop (generation : Nat) (cpu : CPU) : Expr := .hart generation cpu (.pure ())

def powerFork (generation : Nat) : List Expr :=
  (List.ofFn fun cpu : CPU => loop generation cpu) ++
    [.uart generation, .disk generation, .plic generation]

def powerOff (g : State) : State := { g with generation := g.generation + 1, power := false }

/-- Source power arms: cut power and kill the generation, or run a fresh boot
while retaining the current durable disk. No fs.img reset occurs here. -/
inductive PowerStep (image : BootImage) (g : State) :
    List Observation → State → List Expr → Prop where
  | off (on : g.power = true) : PowerStep image g [.powerOff] (powerOff g) []
  | on (off : g.power = false) (g' : State) (shape : BootShape image g g') :
      PowerStep image g [.powerOn] g' (powerFork g.generation)

theorem powerFork_length (generation : Nat) : (powerFork generation).length = 11 := by
  simp [powerFork]

theorem power_disk (image : BootImage) (g g' : State) (observations forks)
    (step : PowerStep image g observations g' forks) :
    g'.devices.virtio.v_disk = g.devices.virtio.v_disk := by
  cases step with
  | off on => rfl
  | on off g' shape => exact boot_disk_preserved image g g' shape

theorem power_reducible (image : BootImage) (g : State) :
    ∃ observations g' forks, PowerStep image g observations g' forks := by
  cases h : g.power with
  | true => exact ⟨_, _, _, .off h⟩
  | false => exact ⟨_, _, _, .on h (bootState image g) (boot_shape image g)⟩

theorem powerOff_dead (g : State) (generation : Nat) :
    ¬ ThreadLive (powerOff g) generation := by
  simp [ThreadLive, powerOff]

theorem old_generation_dead_after_boot (image : BootImage) (g : State) :
    ¬ ThreadLive (bootState image (powerOff g)) g.generation := by
  simp [ThreadLive, bootState, powerOff]

end MachCSL.Machine
