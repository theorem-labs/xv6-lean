import Xv6.Kernel.MycpuFetchBytesDefs
import Xv6.Machine.Boot
import MachCSL.Logic.BootWindowDefs
import MachCSL.Logic.TsoContextBytesDefs
import MachCSL.Logic.EraSpec

/-! One physical 34-byte boot slice, before any overlapping fetch sharing.
Source: BootCarve.v:154–211,1220–1255. Mapping/tier claims remain separate. -/
namespace Xv6.Kernel.MycpuBootResources
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic

def address : PhysicalAddress := BitVec.ofInt 64 MycpuDecode.base
def spanWord : BitVec (8 * 34) :=
  BitVec.ofNat _ (assembleBytes (MycpuFetchBytes.bytes.map Xv6.Machine.byteOfUInt8))
def keys : List PhysicalAddress := BootWindow.keys address 34
def descriptor : BootWindow.Word := ⟨address, 34, spanWord⟩

def storeCapacity {GF : BundledGFunctors} (capacity : Era.Capacity GF) : TsoStore.Capacity GF :=
  ⟨capacity.heap, capacity.views, capacity.history⟩
def storeNames (era : Era.Record) : TsoStore.Names := ⟨era.tsoNames, era.metadata⟩

variable {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF) (names : TsoStore.Names)

def rawSpan : IProp GF := TsoStore.storedWindow capacity names address 34 spanWord 0

def remainder (memory : Tso.AddressMap Byte) : IProp GF :=
  iprop(BootWindow.mapBytes capacity.heap.ledger names.tso.ledger.bytes
      (JalBootResources.deleteKeys memory keys) ∗
    BootWindow.mapTimes capacity.heap.ledger names.tso.ledger.timestamps
      (JalBootResources.deleteKeys (Tso.Interp.bootTimestamps memory) keys))

def contextSpan (ξ : TsoContext.CtxId) (dq : DFrac) : IProp GF :=
  TsoContextBytes.window capacity names ξ address 34 dq spanWord

/-- Byte fractions and explicitly discarded timestamp-zero receipts. -/
def physicalSpan (dq : DFrac) : IProp GF :=
  iprop(TsoRead.byteWindow capacity.heap.ledger names.tso.ledger.bytes address 34 dq spanWord ∗
    TsoRead.pristineWindow capacity.heap.ledger names.tso.ledger.timestamps address 34)

def fetchWindow (ξ : TsoContext.CtxId) (dq : DFrac) (i : Fin 14) : IProp GF :=
  TsoContextBytes.window capacity names ξ (MycpuDecode.address i)
    (MycpuFetchBytes.width i) dq (MycpuFetchBytes.word i)

def fetchWindows (ξ : TsoContext.CtxId) : IProp GF :=
  iprop([∗list] i ∈ List.finRange 14, fetchWindow capacity names ξ .discard i)

/-- Every non-TSO client from the actual era allocator, unchanged. -/
def otherClients (capacity : Era.Capacity GF) (era : Era.Record)
    (memory : Tso.AddressMap Byte) (g : State) (diskBytes : Nat) : IProp GF :=
  iprop(GlobalRegisters.allInitialCells capacity.registers era.registers g.registers ∗
    ([∗map] a ↦ _byte ∈ memory, Heap.token capacity.heap ⟨era.heap, era.metadata⟩ a ⊤) ∗
    Device.fragments capacity.devices era.deviceNames g.devices ∗
    Disk.imageBytes capacity.disk era.disk 0 (MachCSL.Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
    Reservations.allFragments capacity.reservations era.reservations g.reservations)

end Xv6.Kernel.MycpuBootResources
