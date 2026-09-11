import MachCSL.Machine.JalDevicesDefs
import MachCSL.Devices.Virtio.DmaProofs

namespace MachCSL.Machine.JalDevices
open Devices.Virtio Memory

theorem reset_not_live (v : Devices.Virtio.State) : virtio_live (virtio_reset v).v_cfg = false := rfl

theorem reset_request (v : Devices.Virtio.State) (view : vmem) (head : BitVec 16) :
    virtio_req_step (virtio_reset v) view head = none := by
  rfl

theorem reset_capture (v : Devices.Virtio.State) (view : vmem) (head : BitVec 16) :
    virtio_capture_step (virtio_reset v) view head = none := by
  rfl

theorem reset_pop (v : Devices.Virtio.State) (view : vmem) :
    virtio_pop_step (virtio_reset v) view = none := by
  rfl

theorem reset_drain (v : Devices.Virtio.State) (sector : Int) :
    virtio_drain_step (virtio_reset v) sector = none := by
  simp [virtio_drain_step, virtio_reset]

theorem reset_not_stalled (v : Devices.Virtio.State) (view : vmem) :
    virtio_stalled (virtio_reset v) view = false := by
  rfl

/-- At reset, every non-idle actor arm is ruled out by its original guard.
In particular, the malformed-chain wild-write arm remains in the model. -/
theorem disk_step_idle (d d' : Devices.State) (memory writes : Memory.ByteMap 64)
    (reset : DiskReset d) (step : DiskStep d memory d' writes) :
    d' = d ∧ writes = Memory.empty := by
  obtain ⟨previous, reset⟩ := reset
  cases step with
  | dma view head next writes agrees request =>
    rw [reset, reset_request] at request
    cases request
  | capture view head next agrees captured =>
    rw [reset, reset_capture] at captured
    cases captured
  | pop view next agrees popped =>
    rw [reset, reset_pop] at popped
    cases popped
  | drain sector next drained =>
    rw [reset, reset_drain] at drained
    cases drained
  | wild view writes agrees malformed =>
    rw [reset, reset_not_stalled] at malformed
    cases malformed
  | latch next level latched =>
    simp [Devices.irqLevel, Devices.Plic.virtioIrqId, Devices.Plic.uartIrqId,
      reset, virtio_reset_irq] at level
  | idle => exact ⟨rfl, rfl⟩

theorem uart_preserves_reset (d d' : Devices.State) (events : List Observation)
    (reset : DiskReset d) (step : UartStep d events d') : DiskReset d' := by
  cases step <;> exact reset

theorem boot_reset (image : BootImage) (g : State) (facts : BootFacts image g) : DiskReset g.devices :=
  facts.2.2.2.2.2.1

theorem disk_thread_idle [Platform] (image : BootImage) (generation : Nat) (g : State)
    (events : List Observation) (next : Expr) (g' : State) (forks : List Expr)
    (reset : DiskReset g.devices) (step : Step image (.disk generation) g events next g' forks) :
    next = .disk generation ∧ g' = g ∧ events = [] ∧ forks = [] := by
  cases step with
  | diskDead => exact ⟨rfl, rfl, rfl, rfl⟩
  | diskLive generation g next writes log live action publish reserved =>
    obtain ⟨rfl, rfl⟩ := disk_step_idle g.devices next g.memory writes reset action
    have logEq : log = g.log := by
      rcases publish with ⟨_, eq⟩ | ⟨ne, _⟩
      · exact eq
      · exact False.elim (ne rfl)
    subst log
    simp

end MachCSL.Machine.JalDevices
