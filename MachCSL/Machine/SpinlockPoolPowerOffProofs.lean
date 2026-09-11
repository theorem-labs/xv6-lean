import MachCSL.Machine.SpinlockPoolDefs

namespace MachCSL.Machine.SpinlockPool

/-- Killing the current generation preserves every old occurrence and label;
the next generation strictly exceeds each of their generation numbers. -/
theorem power_off_frame {pool : Pool} {g : State} (inv : PoolInv (pool, g)) :
    PoolInv (pool, powerOff g) := by
  refine ⟨⟨inv.1.labels, inv.1.power, ?_, ?_⟩, ?_⟩
  · intro e label member gen found
    have bounded := (inv.1.generations e label member gen found).1
    change gen ≤ g.generation at bounded
    change gen ≤ g.generation + 1 ∧ (false = false → gen < g.generation + 1)
    constructor <;> omega
  · intro impossible
    change false = true at impossible
    contradiction
  · intro impossible
    change false = true at impossible
    contradiction

theorem power_off_no_holders (pool : Pool) (g : State) (cpu : CPU) :
    ¬Holds (pool, powerOff g) cpu := by
  intro held
  have impossible := held.1
  change false = true at impossible
  contradiction

theorem power_off_disk (g : State) :
    (powerOff g).devices.virtio.v_disk = g.devices.virtio.v_disk := rfl

/-- Inverting the actual power primitive prevents an on-event being treated
as a cut. No unlock is required before old holder labels become inactive. -/
theorem power_off_step_frame [Platform] {pool : Pool} {g g' : State}
    {next : Expr} {forks : List Expr}
    (step : Step SpinlockImage.image .power g [.powerOff] next g' forks)
    (inv : PoolInv (pool, g)) :
    next = .power ∧ g' = powerOff g ∧ forks = [] ∧ PoolInv (pool, g') := by
  cases step with
  | power g observations next forks action =>
    cases action with
    | off on => exact ⟨rfl, rfl, rfl, power_off_frame inv⟩

end MachCSL.Machine.SpinlockPool
