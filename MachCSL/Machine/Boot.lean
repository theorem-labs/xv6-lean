import MachCSL.Machine.State
import MachCSL.Machine.ColdBoot
import MachCSL.Machine.Image

/-! Image-parametric power-on predicates and a concrete witness. The byte
function must eventually be instantiated from the checked paper ELF/image maps.
The RAM shape uses equality to a transparent map, an extensional presentation
of the source's RAM-only domain and per-byte contents clauses. -/
namespace MachCSL.Machine
open Memory

def BootFacts (image : BootImage) (g : State) : Prop :=
  g.power = true ∧
  g.memory = loadedRam image ∧
  (∀ cpu : CPU, ∃ before after : RegisterFile,
    Run Devices.bus (bootProgram image.vector (BitVec.ofNat 64 cpu.val) pmaBoot)
      ⟨before, empty, Devices.initial⟩ () ⟨after, empty, Devices.initial⟩ ∧
    g.registers cpu = after) ∧
  g.devices.uart = Devices.Uart.initial ∧
  g.devices.plic = Devices.Plic.initial ∧
  (∃ before, g.devices.virtio = Devices.Virtio.virtio_reset before) ∧
  (∀ cpu, g.reservations cpu = none) ∧
  g.log = [] ∧ g.image = g.memory ∧ (∀ cpu, g.views cpu = 0)

def BootShape (image : BootImage) (before after : State) : Prop :=
  after.generation = before.generation ∧
  after.devices.virtio = Devices.Virtio.virtio_reset before.devices.virtio ∧
  BootFacts image after

def bootState (image : BootImage) (before : State) : State := {
  registers := fun cpu => bootRegisters image.vector (BitVec.ofNat 64 cpu.val)
  memory := loadedRam image
  devices := Devices.reset before.devices
  generation := before.generation
  power := true
  reservations := fun _ => none
  image := loadedRam image
  log := []
  views := fun _ => 0 }

theorem boot_facts (image : BootImage) (before : State) : BootFacts image (bootState image before) := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, ⟨before.devices.virtio, rfl⟩,
    fun _ => rfl, rfl, rfl, fun _ => rfl⟩
  intro cpu
  exact ⟨zeroRegisters, bootRegisters image.vector (BitVec.ofNat 64 cpu.val),
    boot_run Devices.bus _ _ empty Devices.initial, rfl⟩

theorem boot_shape (image : BootImage) (before : State) :
    BootShape image before (bootState image before) := ⟨rfl, rfl, boot_facts image before⟩

theorem boot_disk_preserved (image : BootImage) (before after : State)
    (shape : BootShape image before after) :
    after.devices.virtio.v_disk = before.devices.virtio.v_disk := by
  rw [shape.2.1]
  rfl

theorem boot_memory_ok (image : BootImage) (g : State) (facts : BootFacts image g) :
    MemoryOK g := by
  obtain ⟨_, memory, _, _, _, _, _, log, initial, views⟩ := facts
  refine ⟨?_, ?_, ?_⟩
  · rw [log, flat_nil, initial]
  · intro cpu
    simp [views, log]
  · intro a low high
    rw [initial, memory]
    exact ⟨image.byte a.toNat, by simp [loadedRam, low, high]⟩

theorem boot_reservations_ok (image : BootImage) (g : State) (facts : BootFacts image g) :
    ReservationsOK g := by
  obtain ⟨_, _, _, _, _, _, reservations, _⟩ := facts
  intro cpu r hr
  rw [reservations cpu] at hr
  contradiction

end MachCSL.Machine
