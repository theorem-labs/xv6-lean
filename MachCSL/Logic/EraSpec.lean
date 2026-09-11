import MachCSL.Logic.EraDefs
import MachCSL.Logic.GlobalRegistersSpec
import MachCSL.Logic.HeapSpec
import MachCSL.Logic.DeviceSpec
import MachCSL.Logic.DiskSpec
import MachCSL.Logic.ReservationSpec
import MachCSL.Logic.TsoInterpSpec

namespace MachCSL.Logic.Era
open Iris Iris.BI MachCSL.Machine MachCSL.Memory

/-- Component contracts are explicit; their implementations are imported only
by the final linking module. The byte capacity is shared by construction. -/
structure Contracts {GF : BundledGFunctors} (c : Capacity GF) : Prop where
  registers : GlobalRegisters.GlobalRegisterSpec c.registers
  heap : Heap.HeapSpec c.heap
  devices : Device.DeviceSpec c.devices
  disk : Disk.DiskSpec c.disk
  reservations : Reservations.ReservationSpec c.reservations
  tso : Tso.Interp.InterpSpec c.tso

/-- Machine-owned fields are allocated; the template retains the source's
kernel-layer names whose ownership is supplied by later kernel initialization. -/
def assemble (template : Record) (registers : GlobalRegisters.Names)
    (tso : Tso.Interp.EraNames) (metadata : GName) (devices : Device.Names)
    (disk reservations : GName) (memory : Tso.AddressMap Byte) : Record :=
  { template with
    registers := registers, heap := tso.ledger.bytes, metadata := metadata,
    uart := devices.uart, plic := devices.plic, virtio := devices.virtio,
    disk := disk, reservations := reservations, timestamps := tso.ledger.timestamps,
    logEntries := tso.logEntries, logLength := tso.logLength, views := tso.views,
    image := memory }

def AuxiliarySame (era template : Record) : Prop :=
  era.kernelMap = template.kernelMap ∧ era.kernelPageTable = template.kernelPageTable ∧
  era.kernelPageTableBound = template.kernelPageTableBound ∧
  era.supervisorTranslation = template.supervisorTranslation ∧
  era.supervisorInterruptEnable = template.supervisorInterruptEnable ∧
  era.supervisorPreviousPrivilege = template.supervisorPreviousPrivilege ∧
  era.supervisorPreviousInterruptEnable = template.supervisorPreviousInterruptEnable ∧
  era.parkedHart = template.parkedHart ∧ era.processState = template.processState ∧
  era.logMirror = template.logMirror ∧ era.heldLocks = template.heldLocks

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Every client resource minted by machine-era initialization. This is not
the full kernel `power_boot_res`, whose additional ghost tokens remain separate. -/
def bootClients (era : Record) (memory : Tso.AddressMap Byte) (g : State)
    (diskBytes : Nat) : IProp GF :=
  iprop(GlobalRegisters.allInitialCells capacity.registers era.registers g.registers ∗
    Tso.Interp.bootClients capacity.tso era.tsoNames memory ∗
    ([∗map] a ↦ _byte ∈ memory, Heap.token capacity.heap ⟨era.heap, era.metadata⟩ a ⊤) ∗
    Device.fragments capacity.devices era.deviceNames g.devices ∗
    Disk.imageBytes capacity.disk era.disk 0 (Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
    Reservations.allFragments capacity.reservations era.reservations g.reservations)

structure EraSpec : Prop where
  allocate : ∀ (image : BootImage) (g : State) (memory : Tso.AddressMap Byte)
    (template : Record) (diskBytes : Nat),
    BootFacts image g → FiniteMap.decode memory = g.memory →
    iprop(⊢ |==> ∃ era : Record,
      ⌜era.image = memory ∧ AuxiliarySame era template⌝ ∗
      interp capacity era g ∗ bootClients capacity era memory g diskBytes)

end MachCSL.Logic.Era
