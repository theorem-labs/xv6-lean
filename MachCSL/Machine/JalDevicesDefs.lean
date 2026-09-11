import MachCSL.Machine.Language

/-! Device-side invariant for the one-instruction feasibility image.
It restricts reachable states, never the machine's transition relation. -/
namespace MachCSL.Machine.JalDevices

def DiskReset (devices : Devices.State) : Prop :=
  ∃ previous : Devices.Virtio.State, devices.virtio = Devices.Virtio.virtio_reset previous

end MachCSL.Machine.JalDevices
