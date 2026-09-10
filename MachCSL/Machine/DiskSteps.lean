import MachCSL.Machine.DeviceSteps
import MachCSL.Devices.Virtio.Dma

/-! The disk bus-master actor, `iris/RiscvLang.v:disk_step`. The second
output is the actual write set, not post-state memory. In particular, idle,
capture, pop, drain and interrupt-latch steps publish no RAM bytes. -/
namespace MachCSL.Machine
open Memory

inductive DiskStep (d : Devices.State) (memory : ByteMap 64) :
    Devices.State → ByteMap 64 → Prop where
  | dma (view : Devices.Virtio.vmem) (head : BitVec 16) (next : Devices.Virtio.State)
      (writes : ByteMap 64) (agrees : Devices.Virtio.mem_view memory view)
      (request : Devices.Virtio.virtio_req_step d.virtio view head = some (next, writes)) :
      DiskStep d memory { d with virtio := next } writes
  | capture (view : Devices.Virtio.vmem) (head : BitVec 16) (next : Devices.Virtio.State)
      (agrees : Devices.Virtio.mem_view memory view)
      (captured : Devices.Virtio.virtio_capture_step d.virtio view head = some next) :
      DiskStep d memory { d with virtio := next } empty
  | pop (view : Devices.Virtio.vmem) (next : Devices.Virtio.State)
      (agrees : Devices.Virtio.mem_view memory view)
      (popped : Devices.Virtio.virtio_pop_step d.virtio view = some next) :
      DiskStep d memory { d with virtio := next } empty
  | drain (sector : Int) (next : Devices.Virtio.State)
      (drained : Devices.Virtio.virtio_drain_step d.virtio sector = some next) :
      DiskStep d memory { d with virtio := next } empty
  | wild (view : Devices.Virtio.vmem) (writes : ByteMap 64)
      (agrees : Devices.Virtio.mem_view memory view)
      (malformed : Devices.Virtio.virtio_stalled d.virtio view = true) :
      DiskStep d memory d writes
  | latch (next : Devices.Plic.State)
      (level : Devices.irqLevel d Devices.Plic.virtioIrqId = true)
      (latched : Devices.Plic.latch d.plic Devices.Plic.virtioIrqId = some next) :
      DiskStep d memory { d with plic := next } empty
  | idle : DiskStep d memory d empty

theorem disk_uart (d d' : Devices.State) (memory writes : ByteMap 64)
    (step : DiskStep d memory d' writes) : d'.uart = d.uart := by cases step <;> rfl

end MachCSL.Machine
