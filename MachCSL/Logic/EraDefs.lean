import MachCSL.Logic.TsoInterpDefs
import MachCSL.Logic.DeviceDefs
import MachCSL.Logic.GlobalRegistersDefs
import MachCSL.Logic.ReservationDefs
import MachCSL.Logic.HeapDefs
import MachCSL.Logic.DiskDefs

/-! Complete Σ-free `riscvEraGS` data record, `RiscvPtsto.v:175–381`.
Names are data, not assertions that their resources have been allocated. -/
namespace MachCSL.Logic.Era
open Iris MachCSL.Machine MachCSL.Memory

/-- All fields of the source era record, including kernel-layer names whose
resource allocation is a separate obligation. No Iris proposition occurs here. -/
structure Record where
  registers : CPU → GName
  heap : GName
  metadata : GName
  uart : GName
  plic : GName
  virtio : GName
  kernelMap : GName
  kernelPageTable : GName
  kernelPageTableBound : GName
  supervisorTranslation : CPU → GName
  supervisorInterruptEnable : CPU → GName
  supervisorPreviousPrivilege : CPU → GName
  supervisorPreviousInterruptEnable : CPU → GName
  parkedHart : Nat → GName
  processState : Nat → GName
  disk : GName
  logMirror : GName
  heldLocks : CPU → GName
  reservations : GName
  timestamps : GName
  logEntries : GName
  logLength : GName
  views : GName
  image : Tso.AddressMap Byte

def Record.deviceNames (era : Record) : Device.Names := ⟨era.uart, era.plic, era.virtio⟩
def Record.tsoNames (era : Record) : Tso.Interp.EraNames :=
  ⟨⟨era.heap, era.timestamps⟩, era.logEntries, era.logLength, era.views⟩

/-- The state model's functional image and the source's finite image are tied by
the proved finite-map decoder, rather than an unchecked representation cast. -/
def Record.imageBytes (era : Record) : ByteMap 64 := FiniteMap.decode era.image

/-- One coherent byte camera is shared by the complete heap and TSO ledger. -/
structure Capacity (GF : BundledGFunctors) where
  heap : Heap.Capacity GF
  registers : Registers.Capacity GF
  devices : Device.Capacity GF
  disk : Disk.Capacity GF
  reservations : Reservations.Capacity GF
  views : Tso.Views.Capacity GF
  history : Tso.History.Capacity GF

def Capacity.tso {GF : BundledGFunctors} (c : Capacity GF) : Tso.Interp.Capacity GF :=
  ⟨c.heap.ledger, c.views, c.history⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)
open Iris.BI

/-- The actual functional RAM state is represented by the full native finite
gen_heap, including its metadata, with an explicit exact decoding equation. -/
def heapInterpAt (era : Record) (g : State) : IProp GF :=
  iprop(∃ memory : Tso.AddressMap Byte,
    Heap.interp capacity.heap ⟨era.heap, era.metadata⟩ memory ∗
    ⌜FiniteMap.decode memory = g.memory⌝)

/-- All seven source era conjuncts, `RiscvPtsto.v:2149–2159`. The fixed durable
disk authority is separate; this image authority belongs to this era alone. -/
def interp (era : Record) (g : State) : IProp GF :=
  iprop(GlobalRegisters.gregsInterp capacity.registers era.registers g.registers ∗
    heapInterpAt capacity era g ∗
    Device.interp capacity.devices era.deviceNames g.devices ∗
    Disk.imageAuth capacity.disk era.disk g.devices.virtio.v_disk ∗
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g ∗
    Reservations.resvAuth capacity.reservations era.reservations g.reservations ∗
    ⌜ReservationsOK g⌝)

end MachCSL.Logic.Era
