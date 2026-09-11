import Xv6.Kernel.KernelTextBootDefs

/-! Persist the actual boot PMA register clients once, keeping the exact
179-register remainder on every hart and every non-register boot client. -/
namespace Xv6.Kernel.BootPma
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelTextBoot.Capacity
abbrev Files := GlobalRegisters.Files

/-- The real generated key is deleted; dependent payloads of all other
registers retain the actual original value and its matching type. -/
def remainingMap (rs : RegisterFile) : Registers.RegisterMap Registers.Value :=
  Iris.Std.PartialMap.delete (Registers.initialMap rs) .pma_regions

def remainingKeys : List Register := Registers.allRegisters.filter (fun r => r != .pma_regions)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def remainingHart (name : GName) (rs : RegisterFile) : IProp GF :=
  letI := capacity.machine.era.registers.registers
  iprop([∗map] r ↦ value ∈ remainingMap rs, ghost_map_elem name (.own 1) r value)

def remainingRegisters (era : Era.Record) (files : Files) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs, remainingHart capacity (era.registers cpu) (files cpu))

def raw (era : Era.Record) (files : Files) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs,
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions (.own 1)
      (files cpu .pma_regions))

def cell (era : Era.Record) (cpu : CPU) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions .discard pmaBoot

def all (era : Era.Record) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs, cell capacity era cpu)

/-- The literal non-register, non-TSO columns of the source era clients.
All heap metadata tokens, including those for carved text, are retained. -/
def nonRegisterClients (era : Era.Record) (memory : Tso.AddressMap Byte) (g : State)
    (diskBytes : Nat) : IProp GF :=
  iprop(([∗map] a ↦ _byte ∈ memory, Heap.token capacity.machine.era.heap ⟨era.heap,era.metadata⟩ a ⊤) ∗
    Device.fragments capacity.machine.era.devices era.deviceNames g.devices ∗
    Disk.imageBytes capacity.machine.era.disk era.disk 0
      (MachCSL.Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
    Reservations.allFragments capacity.machine.era.reservations era.reservations g.reservations)

/-- Era clients after consuming just the eight full PMA cells. The TSO
memory-byte/timestamp/log-length columns are unchanged. -/
def retained (era : Era.Record) (memory : Tso.AddressMap Byte) (g : State)
    (diskBytes : Nat) : IProp GF :=
  iprop(remainingRegisters capacity era g.registers ∗
    Tso.Interp.bootClients capacity.machine.era.tso era.tsoNames memory ∗
    nonRegisterClients capacity era memory g diskBytes)

/-- KernelTextBoot clients after the same eight register cells are consumed.
The exact sparse text deletion remains unchanged in both memory maps. -/
def textRetained (era : Era.Record) (memory : Tso.AddressMap Byte) (g : State)
    (diskBytes : Nat) : IProp GF :=
  iprop(remainingRegisters capacity era g.registers ∗ KernelTextBoot.remainder capacity era memory ∗
    Tso.Views.natLB capacity.machine.era.views era.logLength 0 ∗
    nonRegisterClients capacity era memory g diskBytes)

end Xv6.Kernel.BootPma
